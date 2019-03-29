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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval_one (cs, stack, (s, i, o) ) program = match program with
     | BINOP op -> (match stack with
         | y::x::tail -> (cs, [Language.Expr.to_func op x y] @ tail, (s, i, o))
         | _ -> failwith "stack isn't filled")
     | CONST c -> (cs, c :: stack, (s, i, o))
     | READ -> (match i with
           | h :: t -> (cs, [h] @ stack, (s, t, o))
           | _ -> failwith "istream is empty")
     | WRITE -> (match stack with 
           | h :: t -> (cs, t, (s, i, o @ [h]))
           | _ -> failwith "stack is empty")
     | LD x -> (cs, (State.eval s x) :: stack, (s, i, o))
     | ST x -> (match stack with 
           | h::t -> (cs, t, (Language.State.update x h s, i, o))
           | _ -> failwith "stack is empty" )
     | LABEL l -> (cs, stack, (s, i, o));;
   
                       
let rec eval env conf program = match program with
     | h :: t -> (match h with 
          | JMP label -> eval env conf (env#labeled label)
          | CJMP (fl, l) ->
            (
               let (cs, stack, c)=conf in
		    match stack with
		    | x :: tail_stack -> eval env (cs, tail_stack, c)  
                                  (if (x = 0 && fl = "z" || x != 0 && fl = "nz") then (env#labeled l) else  t )
		    | _ -> failwith "stack is empty" 
             

               )
          | CALL name -> 
                let (control_stack, stack, (state, i, o))=conf in
      		let prg = env#labeled name in
      		eval env ((t, state)::control_stack, stack, (state, i, o)) prg
          | BEGIN (arg_names, local_names)  ->
                let (control_stack, stack, (state, i, o))=conf in
                let local_state = State.push_scope state (arg_names @ local_names) in
                let local_state_init, updated_stack = 
                List.fold_left (fun (s, value::stack_tail) name -> (State.update name value s, stack_tail))
                 (local_state, stack) arg_names in
                eval env (control_stack, updated_stack, (local_state_init, i, o)) t
          | END :: _ ->
                 let (control_stack, stack, (state, i, o))=conf in
   		 (
                 match control_stack with
   		 | [] -> conf
    	         | (t, old_state) :: control_stack ->
     	        eval env (control_stack, stack, (State.drop_scope state old_state, i, o)) t
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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
class label_generator =
  object (self)
    val mutable counter = 0
    method generate =
      {<counter = counter + 1>}, "l_" ^ string_of_int counter
  end


let rec compile_expr expr = match expr with
     | Language.Expr.Const c -> [CONST c]
     | Language.Expr.Var v -> [LD v]
     | Language.Expr.Binop (op, e1, e2) -> (compile_expr e1) @ (compile_expr e2) @ [BINOP op]

let rec compile_lbls stmt lambda last_l = match stmt with
     | Language.Stmt.Read v -> [READ; ST v], false, lambda
     | Language.Stmt.Write e -> (compile_expr e) @ [WRITE], false, lambda
     | Language.Stmt.Assign (v, e) -> (compile_expr e) @ [ST v], false, lambda
     | Language.Stmt.Seq (prv, nxt) -> let (lambda, lbl) = lambda#generate in
                                       let (prg1, used1, lambda) = compile_lbls prv lambda lbl in
                                       let (prg2, used2, lambda) = compile_lbls nxt lambda last_l in
                                       (prg1 @
                                       (if used1 then [LABEL lbl] else []) @
                                        prg2), used2, lambda
     | Language.Stmt.Skip -> [], false, lambda
     | Language.Stmt.While (e, body) ->
       let (lambda, l_check) = lambda#generate in
       let (lambda, l_loop) = lambda#generate in
       let (loop_body, _, lambda) = compile_lbls body lambda l_check in
       [JMP l_check; LABEL l_loop] @ (loop_body) @ [LABEL l_check] @ (compile_expr e) @ [CJMP("nz", l_loop)], false, lambda
       (*[LABEL l_cond] @ (expr e) @ [CJMP ("z", l_od)] @ (compile body) @ [JMP l_cond; LABEL l_od]*)
     | Stmt.RepeatUntil (body, e ) ->
       let (lambda, l_loop) = lambda#generate in
       let (loop_body, _, lambda) = compile_lbls body lambda last_l in
       [LABEL l_loop] @ (loop_body ) @ (compile_expr e) @ [CJMP ("z", l_loop)], false, lambda
     | Language.Stmt.If (e, s1, s2) ->
       let (lambda, l_else) = lambda#generate in
       let (then_body, used1, lambda) = compile_lbls s1 lambda last_l in
       let (els_body, used2, lambda) = compile_lbls s2 lambda last_l in
       (compile_expr e) @ [CJMP ("z", l_else)] @ (then_body) @ (if used1 then [] else [JMP last_l]) @ [ LABEL l_else] 
       @ (els_body) @ (if used2 then [] else [JMP last_l]) , true, lambda
     | Language.Stmt.Call (fn_name, args) -> List.concat (List.map compile_expr (List.rev args)) @ [CALL fn_name], false, lambda;;


let rec compile_stmt prg = let lambda, l = (new label_generator)#generate in
                    let prg', used, _ = compile_lbls prg lambda l  in
                    prg' @ (if used then [LABEL l] else [])

let rec  compile_defs func_defs =
  List.fold_left(fun prev (name, (args, local_vars, body)) -> 
    prev @ [LABEL name] @ [BEGIN (args, local_vars)] @ (compile_stmt body) @ [END]
  ) [] func_defs

let compile (func_defs, stmt) =  (compile_stmt stmt) @ [END] @ (compile_defs func_defs)
