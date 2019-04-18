(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let rec list_constructor n f  = if n < 0 then [] else  f n :: list_constructor (n - 1) f
let list_init len f = List.rev (list_constructor (len - 1) f )

let rec other_list_init i n f = if i >= n then [] else (f i) :: (other_list_init (i + 1) n f) 

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list with show

    let to_int = function 
    | Int n -> n 
    | String s -> failwith (Printf.sprintf "int value expected, but get string %s" s)  
    | Array a -> failwith (Printf.sprintf "int value expected, but get array" )  
    | _ -> failwith "int value expected"  

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = other_list_init 0 (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> Value.t; l : string -> Value.t; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end

(* Builtins *)
module Builtin =
  struct

    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | "$elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String s -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array  a -> List.nth a i
                               )
                    )         
    | "$length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | "$array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
    *)                                                       
        let to_int b = if b then 1 else 0
    let to_bool x = x != 0
                                                      
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval env ((st, i, o, r) as cfg) expr =      
      match expr with
      | Const n -> (st, i, o, Some (Value.of_int n))
      | Var   x -> (st, i, o, Some (State.eval st x))
      | Binop (op, x, y) ->  let ((_, _, _, Some x') as cfg') = eval env cfg x in
         let (st', i', o', Some y') = eval env cfg' y in
         (st', i', o', Some (Value.of_int @@ to_func op (Value.to_int x') (Value.to_int y')))
      | Call (name, args) ->
         let ((st', i', o', args) as cfg') = List.fold_left (fun (s, i, o, args) arg ->
			let (s, i, o, Some res) = eval env (s, i, o, None) arg in 
                         (s, i, o, args @ [res])) (st, i, o, []) args in env#definition env name args (st', i', o', None) 
      | Array a  -> let (st, i, o, r') = eval_list env cfg a in
                    (st, i, o, Some (Value.of_array r'))
      | String s -> (st, i, o, Some (Value.of_string s))
      | Elem (e, ind)    -> let (st, i, o, Some eval_el) = eval env cfg ind in
                            let (st, i, o, Some v) = eval env (st, i, o, None) e in
                            (st, i, o, Some (match v with
                                | Value.Array list -> List.nth list @@ Value.to_int eval_el
                                | Value.String s   -> Value.of_int @@ Char.code @@ String.get s @@ Value.to_int eval_el))
      | Length len         -> let (st, i, o, Some eval_len) = eval env cfg len in
                            (st, i, o, Some (match eval_len with
                                | Value.Array list -> Value.of_int @@ List.length list
                                | Value.String s -> Value.of_int @@ String.length s))

    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string                                                                                                                  
    *)
    ostap (                                      
      expr:
	  !(Ostap.Util.expr 
             (fun x -> x)
	     (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     secondary);
      secondary:
            pr:primary arr:(-"[" !(expr) -"]")* len:("." %"length")?
            {  let elms = List.fold_left (fun a i -> Elem (a, i)) pr arr in match len with
                | Some x -> Length elms
                | None   -> elms  };
      primary:
        n:DECIMAL {Const n}

      | "[" es:!(Util.list0 expr) "]" { Array es }
      | name:IDENT "(" args:!(Util.list0 expr)  ")" {Call (name, args)}
      | x:IDENT   {Var x}
      | c:CHAR    {Const (Char.code c)}
      | s:STRING  {String (String.sub s 1 (String.length s - 2))}
      | -"(" expr -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | RepeatUntil of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)

    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

      let meta_op k s =
        match k with
        | Skip -> s
        | _ -> Seq (s, k)
      
    let rec eval env ((s, i, o, _) as cfg) k stmt = match stmt with
	(*|Read v  -> let head::tail = i in
            eval env (State.update v head s, tail, o, None) Skip k
        | Write e  ->    let (s', i', o', Some v) = Expr.eval env cfg e in
                    eval env (s', i', o' @ [v], None) Skip k*)
        | Assign (v, ind, e) -> let (s, i, o, Some r) = Expr.eval env cfg e in
	      let (s, i, o, ind) = Expr.eval_list env (s, i, o, None) ind in 
              eval env (update s v r ind, i, o, None) Skip k
        | Seq (prev, next) ->  eval env cfg (meta_op k next) prev
        | Skip -> (match k with
              | Skip -> cfg
              | _ -> eval env cfg Skip k)
        | If(cond, then_branch, else_branch) ->
              let ((s, i, o, Some cond_res) as cfg') = Expr.eval env cfg cond in
              eval env cfg' k (if Expr.to_bool (Value.to_int cond_res) then  then_branch else else_branch) 
        | While (e, body) ->
              let ((s, i, o, Some e_res) as cfg') = Expr.eval env cfg e in
              if Expr.to_bool (Value.to_int e_res) then eval env cfg' (meta_op k stmt) body else 
              eval env (s, i, o, None) Skip k
        | RepeatUntil (body, e) ->
              eval env cfg (meta_op k (While (Expr.Binop ("==", e, Expr.Const 0), body))) body
        | Call (name, args) ->
              (*cfg across expr*)
              (eval env (Expr.eval env cfg (Expr.Call (name, args)))) Skip k
              (*let (arg_names, local_vars, body) = env#definition name in
              let local_state = State.push_scope s (arg_names @ local_vars) in
	      let bindings = List.combine arg_names (List.map (Expr.eval s) args) in
              let local_state_init =
                    List.fold_right(fun (arg_name, arg_value) s' -> State.update arg_name arg_value s')
                    bindings local_state
             in
             let (end_state, i, o) = eval env (local_state_init, i, o) body in
            (State.drop_scope end_state s, i, o)*)
        | Return res -> match res with
           | Some res -> Expr.eval env cfg res
           | _ -> (s, i, o, None)
         
    (* Statement parser *)
    ostap (
      simple_stmt:
                x:IDENT ind:(-"[" !(Expr.expr) -"]")* ":=" e:!(Expr.expr)    {Assign (x, ind, e)};
                 (* x:IDENT ":=" e:!(Expr.expr)       {Assign(x, e)}
               | "read" "(" x:IDENT ")"           {Read x}
               | "write" "(" e:!(Expr.expr) ")" {Write e};*)

      construct_stmt:
           "while" cond:!(Expr.expr) "do" body:!(parse) "od" 
            { While (cond, body)}
           | "for" init:!(parse) "," cond:!(Expr.expr) "," action:!(parse) "do" body:!(parse) "od"
            {  Seq(init, While(cond, Seq(body, action))) }
           | "repeat" body:!(parse) "until" cond:!(Expr.expr)
            { RepeatUntil (body, cond)}
           | "if" cond:!(Expr.expr)
                "then" th:!(parse)
                elif_branch: (%"elif" !(Expr.expr) %"then" !(parse))*
                else_branch:  (%"else" !(parse))?
                "fi"
            {
                    let else_branch' = match else_branch with
                        | Some x -> x
                        | _ -> Skip
                    in
                    let elif_branch' = List.fold_right (fun (cond, body) t -> If (cond, body, t)) elif_branch else_branch' in
                    If (cond, th, elif_branch')
            }
           | "skip" {Skip};

      call_stmt:    name:IDENT "(" args:(!(Expr.expr))* ")" {Call (name, args)};
      return_stmt:  "return" e:!(Expr.expr)?                { Return e };
     
      stmt:    simple_stmt | construct_stmt | call_stmt | return_stmt;

      parse:     line:stmt ";" rest:parse      {Seq(line, rest)} 
	       | stmt
      )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
