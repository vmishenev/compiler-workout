open GT       
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Syntax.Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)  


let rec eval_one (stack, (s, i, o)) program = match program with
     | BINOP op -> (match stack with
         | y::x::tail -> ([Syntax.Expr.eval_op op x y] @ tail, (s, i, o))
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
           | h::t -> (t, (Syntax.Expr.update x h s, i, o))
           | _ -> failwith "stack is empty" )
                       
let rec eval conf program = match program with
     | h :: t -> eval (eval_one conf h) t
     | []            -> conf;;

(* Top-level evaluation

     val run : int list -> prg -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run i p = let (_, (_, _, o)) = eval ([], (Syntax.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Syntax.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

 let rec compile_expr expr = match expr with
     | Syntax.Expr.Const c -> [CONST c]
     | Syntax.Expr.Var v -> [LD v]
     | Syntax.Expr.Binop (op, e1, e2) -> (compile_expr e1) @ (compile_expr e2) @ [BINOP op]

 let rec compile stmt = match stmt with
     | Syntax.Stmt.Read v -> [READ; ST v]
     | Syntax.Stmt.Write e -> (compile_expr e) @ [WRITE]
     | Syntax.Stmt.Assign (v, e) -> (compile_expr e) @ [ST v]
     | Syntax.Stmt.Seq (prv, nxt) -> (compile prv) @ (compile nxt)
