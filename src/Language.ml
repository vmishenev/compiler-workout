(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_int b = if b then 1 else 0
    let to_bool x = x != 0

    let eval_op operator x y =  match operator with
            | "*" -> x * y
            | "/" -> x / y
            | "%" -> x mod y
            | "+" -> x + y
            | "-" -> x - y
            | "!!" -> to_int (to_bool x || to_bool y)
            | "&&" -> to_int (to_bool x && to_bool y)
            | "==" -> to_int (x == y)
            | "!=" -> to_int (x <> y)
            | "<=" -> to_int (x <= y)
            | "<"  -> to_int (x < y)
            | ">=" -> to_int (x >= y)
            | ">" -> to_int (x > y);;
    let rec eval st expr = match expr with
        | Const value -> value
        | Var name -> st name
        | Binop(operator, l, r)-> let x = eval st l in let y = eval st r in eval_op operator x y;; 
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    let ostap_bin op = ostap($(op)), (fun x y -> Binop(op, x, y))

    ostap (                                      
      expr: !(Ostap.Util.expr
                 (fun x -> x) (* --- a function, used to transform each parsed subexpression into something; often just an id         *)
                 (Array.map (fun (assoc, ops) -> assoc, List.map ostap_bin ops) 
                     [|
                        `Lefta, ["!!"];
                        `Lefta, ["&&"];
                        `Nona,  ["=="; "!="; "<="; "<"; ">="; ">"];
                        `Lefta, ["+"; "-"];
                        `Lefta, ["*"; "/"; "%"];
                     |]
                 ) 
                 primary
             );
      primary: x: IDENT {Var x} | n: DECIMAL {Const n} | -"(" expr -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | RepeatUntil of t * Expr.t  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (s, i, o) stmt = let cfg = (s, i, o) in
       match stmt with
	| Read       v  -> let head::tail = i in
            Expr.update v head s, tail, o
        | Write      e  -> (s, i, o @ [Expr.eval s e]) 
        | Assign (v, e) -> (Expr.update v (Expr.eval s e) s, i, o)
        | Seq (prev, next) -> eval( eval cfg prev) next
        | Skip -> cfg
        | If(cond, then_branch, else_branch) ->
          eval cfg (if Expr.to_bool (Expr.eval s cond) then  then_branch else else_branch) 
        | While (e, body) ->
          if Expr.to_bool (Expr.eval s e) then eval (eval cfg body) stmt else cfg
        | RepeatUntil (body, e) ->
          let cfg' = eval cfg body in
          let (s', _, _) = cfg' in
          if not(Expr.to_bool (Expr.eval s' e)) then eval cfg' stmt else cfg';;
                               
    (* Statement parser *)
    ostap (
      simple_stmt:
                  x:IDENT ":=" e:!(Expr.expr)       {Assign(x, e)}
               | "read" "(" x:IDENT ")"           {Read x}
               | "write" "(" e:!(Expr.expr) ")" {Write e};

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
     
      stmt:    simple_stmt | construct_stmt;

      parse:     line:stmt ";" rest:parse      {Seq(line, rest)} 
	       | stmt
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse                                                     
