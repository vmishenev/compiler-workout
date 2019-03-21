open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval_one (stack, (s, i, o)) program = match program with
     | BINOP op -> (match stack with
         | y::x::tail -> ([Language.Expr.eval_op op x y] @ tail, (s, i, o))
         | _ -> failwith "stack isn't filled")
     | CONST c -> (c :: stack, (s, i, o))
     | READ -> (match i with
           | h :: t -> ([h] @ stack, (s, t, o))
           | _ -> failwith "istream is empty")
     | WRITE -> (match stack with 
           | h :: t -> (t, (s, i, o @ [h]))
           | _ -> failwith "stack is empty")
     | LD x -> ((s x) :: stack, (s, i, o))
     | ST x -> (match stack with 
           | h::t -> (t, (Language.Expr.update x h s, i, o))
           | _ -> failwith "stack is empty" )
     | LABEL l -> (stack, (s, i, o))
   
                       
let rec eval env conf program = match program with
     | h :: t -> (match h with 
          | JMP label -> eval env conf (env#labeled label)
          | CJMP (fl, l) ->
            (
               let (stack, c)=conf in
		    match stack with
		    | x :: tail_stack -> eval env (tail_stack, c)  
                                  (if (x = 0 && fl = "z" || x != 0 && fl = "nz") then (env#labeled l) else  t )
		    | _ -> failwith "stack is empty" 
             )
          | _ -> eval env (eval_one conf h) t
        )
     | [] -> conf;;

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

let label_generator =
  object
    val mutable counter = 0
    method generate =
      counter <- counter + 1;
      "l_" ^ string_of_int counter
  end


 let rec compile_expr expr = match expr with
     | Language.Expr.Const c -> [CONST c]
     | Language.Expr.Var v -> [LD v]
     | Language.Expr.Binop (op, e1, e2) -> (compile_expr e1) @ (compile_expr e2) @ [BINOP op]

 let rec compile stmt = match stmt with
     | Language.Stmt.Read v -> [READ; ST v]
     | Language.Stmt.Write e -> (compile_expr e) @ [WRITE]
     | Language.Stmt.Assign (v, e) -> (compile_expr e) @ [ST v]
     | Language.Stmt.Seq (prv, nxt) -> (compile prv) @ (compile nxt)
     | Language.Stmt.Skip -> []
     | Language.Stmt.While (e, body) ->
       let l_check = label_generator#generate in
       let l_loop = label_generator#generate in
       [JMP l_check; LABEL l_loop] @ (compile body) @ [LABEL l_check] @ (compile_expr e) @ [CJMP("nz", l_loop)]
       (*[LABEL l_cond] @ (expr e) @ [CJMP ("z", l_od)] @ (compile body) @ [JMP l_cond; LABEL l_od]*)
     | Stmt.RepeatUntil (body, e ) ->
       let l_loop = label_generator#generate in
       [LABEL l_loop] @ (compile body) @ (compile_expr e) @ [CJMP ("z", l_loop)]
     | Language.Stmt.If (e, s1, s2) ->
       let l_else = label_generator#generate in
       let l_fi = label_generator#generate in
       (compile_expr e) @ [CJMP ("z", l_else)] @ (compile s1) @ [JMP l_fi; LABEL l_else] @ (compile s2) @ [LABEL l_fi]
