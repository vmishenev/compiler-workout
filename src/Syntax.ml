(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
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
            | "<" -> to_int (x < y)
            | ">=" -> to_int (x >= y)
            | ">" -> to_int (x > y);;

    let rec eval st expr = match expr with
        | Const value -> value
        | Var name -> st name
        | Binop(operator, l, r)-> let x = eval st l in let y = eval st r in eval_op operator x y;; 
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (s, i, o) stmt = match stmt with
        | Read       v  -> let head::tail = i in
            Expr.update v head s, tail, o
        | Write      e  -> (s, i, o @ [Expr.eval s e]) 
        | Assign (v, e) -> (Expr.update v (Expr.eval s e) s, i, o)
        | Seq    (prev, next) -> eval( eval (s, i, o) prev) next
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
