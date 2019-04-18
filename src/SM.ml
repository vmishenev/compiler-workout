open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval_one (cs, stack, ((s, i, o) as cfg) ) program = match program with
     | BINOP op -> (match stack with
         | y::x::tail -> (cs, [ Value.of_int (Language.Expr.to_func op (Value.to_int x) (Value.to_int y))] @ tail, (s, i, o))
         | _ -> failwith "stack isn't filled")
     | CONST cnst -> (cs, (Value.of_int cnst)::stack, (s, i, o))
     | STRING str -> (cs, (Value.of_string str)::stack, (s, i, o))
     | LD x -> (cs, (State.eval s x) :: stack, (s, i, o))
     | ST x -> (match stack with 
           | h::t -> (cs, t, (Language.State.update x h s, i, o))
           | _ -> failwith "st x: stack is empty" )
     | LABEL l -> (cs, stack, (s, i, o))
     | STA (name, ind) ->
                let ((value :: remain_ind), tail) = split (ind + 1) stack in
                let new_state = Language.Stmt.update s name value remain_ind in
                (cs, tail, (new_state, i, o));;
                       
let rec eval env conf program = match program with
     | h :: t -> (match h with 
          | JMP label -> eval env conf (env#labeled label)
          | CJMP (fl, l) ->
            (
               let (cs, stack, c)=conf in
		    match stack with
		    | x :: tail_stack -> eval env (cs, tail_stack, c)  
                                  (if ( (Language.Value.to_int x) = 0 && fl = "z" || (Language.Value.to_int x) != 0 && fl = "nz") then (env#labeled l) else  t )
		    | _ -> failwith "cjmp: stack is empty" 
             

               )
           | CALL (name, args, is_prc)   -> (
                 let (control_stack, stack, (state, i, o))=conf in
                      if env#is_label name
                      then let prg = env#labeled name in
      		eval env ((t, state)::control_stack, stack, (state, i, o)) prg
                      else eval env (env#builtin conf name args (not is_prc)) t)
          | BEGIN (_, arg_names, local_names)  ->
                let (control_stack, stack, (state, i, o))=conf in
                let local_state = State.enter state (arg_names @ local_names) in
                let local_state_init, updated_stack = 
                List.fold_left (fun (s, value::stack_tail) name -> (State.update name value s, stack_tail))
                 (local_state, stack) arg_names in
                eval env (control_stack, updated_stack, (local_state_init, i, o)) t
          | (RET _ | END)  ->
                 let (control_stack, stack, (state, i, o))=conf in
   		 (
                 match control_stack with
   		 | [] -> conf
    	         | (t, old_state) :: control_stack ->
     	        eval env (control_stack, stack, (State.leave state old_state, i, o)) t
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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

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
     | Language.Expr.Const c   -> [CONST c]
     | Language.Expr.Var v     -> [LD v]
     | Language.Expr.String s  -> [STRING s]
     | Language.Expr.Array arr         -> let compiled_arr = List.concat (List.map compile_expr (List.rev arr)) in
                             compiled_arr @ [CALL ("$array", (List.length compiled_arr), true)]
     | Language.Expr.Elem (a, i)      -> compile_expr i @ compile_expr a @ [CALL ("$elem", 2, true)]
     | Language.Expr.Length len         -> compile_expr len @ [CALL ("$length", 1, true)]
     | Language.Expr.Binop (op, e1, e2) -> (compile_expr e1) @ (compile_expr e2) @ [BINOP op]
     | Language.Expr.Call (name, args)   -> 
        let args_value = List.concat (List.map compile_expr (List.rev args)) in
        args_value @ [CALL (name, List.length args, true)]

let rec compile_lbls stmt lambda last_l = match stmt with
     (*| Language.Stmt.Read v -> [READ; ST v], false, lambda
     | Language.Stmt.Write e -> (compile_expr e) @ [WRITE], false, lambda*)
     | Stmt.Assign (v, ind, e) -> (match ind with
                                 | [] -> (compile_expr e @ [ST v]), false, lambda
                                 | _  -> let compiled_ind = List.fold_left (fun p id -> p @ (compile_expr id)) [] (List.rev ind) in
                                         compiled_ind @ compile_expr e @ [STA (v, List.length ind)], false, lambda
                              )

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
     | Language.Stmt.Call (fn_name, args) -> List.concat (List.map compile_expr (List.rev args)) @ [CALL (fn_name, List.length args, false)], false, lambda
     | Stmt.Return res      -> (match res with
                            | Some e -> (compile_expr e) @ [RET true], false, lambda
                            | _      -> [RET false], false, lambda)


let rec compile_stmt prg = let lambda, l = (new label_generator)#generate in
                    let prg', used, _ = compile_lbls prg lambda l  in
                    prg' @ (if used then [LABEL l] else [])

let rec  compile_defs func_defs =
  List.fold_left(fun prev (name, (args, local_vars, body)) -> 
    prev @ [LABEL name] @ [BEGIN (name, args, local_vars)] @ (compile_stmt body) @ [END]
  ) [] func_defs

let compile (func_defs, stmt) = (compile_stmt stmt) @ [END] @ (compile_defs func_defs)
