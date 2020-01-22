#use "tag-parser.ml";;

type tree_node = 
  | TreeNode of (string list) * tree_node;;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

(*arrays that indicate for a given paramente the location of the var*)
let read_array = ref [];;
let write_array = ref [];; 
let num_in_seq = ref 1;;

let check_common_father exp exp2 = 
  let exp_length = List.length exp in
  let exp2_length = List.length exp2 in
  if (exp_length <= 1 && exp2_length <= 1) then (false) else (
    if (exp_length <= 1) then (true) else (
      if (exp2_length <= 1) then (true) else (
        (List.nth exp ((List.length exp)-2)) != (List.nth exp2 ((List.length exp2)-2))
      )
    )
  )
  

let should_box_aux read write =  
   List.mem true (List.flatten (List.map (fun exp -> (List.map (fun exp2 -> check_common_father exp exp2) write)) read));;

let rec find_minor_index_in_list list_to_search item acc = 
  (match list_to_search with
  | [] -> acc
  | car::cdr -> if (String.equal item car) then (acc) else find_minor_index_in_list cdr item (acc + 1));;

let rec find_major_index lexical_env x acc = 
  (match lexical_env with
  | [] -> VarFree(x)
  | car::cdr -> if (List.mem x car) 
                then (if (acc == (-1)) 
                      then (VarParam (x, (find_minor_index_in_list car x 0))) 
                      else (VarBound(x, acc, (find_minor_index_in_list car x 0)))
              ) else (find_major_index cdr x (acc + 1)));;

let rec annotate_tail_calls_helper is_tp expr = 
  match expr with
  | Const'(x) -> expr
  | Var'(x) -> expr
  | If'(test, thn, els) -> If'(annotate_tail_calls_helper false test, annotate_tail_calls_helper is_tp thn, annotate_tail_calls_helper is_tp els)
  | Seq'(x) -> Seq'(annotate_list_with_tp is_tp x)
  | Set'(a,b) -> Set'(a, annotate_tail_calls_helper false b)
  | Def'(a,b) -> Def'(a, annotate_tail_calls_helper false b)
  | Or'(x) -> Or'(annotate_list_with_tp is_tp x)
  | LambdaSimple'(str_list, exprs) -> LambdaSimple'(str_list, annotate_tail_calls_helper true exprs)
  | LambdaOpt'(str_list, str, exprs) -> LambdaOpt'(str_list, str, annotate_tail_calls_helper true exprs)
  | Applic'(x, x_list) -> if (is_tp) then (ApplicTP'(annotate_tail_calls_helper false x, List.map (annotate_tail_calls_helper false) x_list))
                                     else (Applic'  (annotate_tail_calls_helper false x, List.map (annotate_tail_calls_helper false) x_list))
  | _ -> raise X_syntax_error

and annotate_list_with_tp is_tp expr =
  let reversed_list = List.rev expr in
  let last_expr = List.hd reversed_list in
  let without_the_last = List.tl reversed_list in
  let normalized_list_without_last = List.rev without_the_last in
  let to_return = (List.map (fun a -> annotate_tail_calls_helper false a) normalized_list_without_last) @ [(annotate_tail_calls_helper is_tp last_expr)] in
  to_return ;;

let rec annotate_LA_with_lexical_env lexical_env e  =  
  match e with
  | Const(x) -> Const'(x)
  | Var(x) -> Var'(find_major_index lexical_env x (-1))
  | If(test, thn, els) -> If'(annotate_LA_with_lexical_env lexical_env test, annotate_LA_with_lexical_env lexical_env thn, annotate_LA_with_lexical_env lexical_env els)
  | Seq(x) -> Seq'(List.map (fun a -> annotate_LA_with_lexical_env lexical_env a) x)
  | Set(a,b) -> Set'(annotate_LA_with_lexical_env lexical_env a, annotate_LA_with_lexical_env lexical_env b)
  | Def(a,b) -> Def'(annotate_LA_with_lexical_env lexical_env a, annotate_LA_with_lexical_env lexical_env b)
  | Or(x) -> Or'(List.map (fun a -> annotate_LA_with_lexical_env lexical_env a) x)
  | LambdaSimple(str_list, exprs) -> LambdaSimple'(str_list, (annotate_LA_with_lexical_env (str_list::lexical_env) exprs))
  | LambdaOpt(str_list, str, exprs) -> LambdaOpt'(str_list, str, (annotate_LA_with_lexical_env ((str_list@[str])::lexical_env) exprs))
  | Applic(x, x_list) -> Applic'(annotate_LA_with_lexical_env lexical_env x, List.map (fun a -> annotate_LA_with_lexical_env lexical_env a) x_list) ;;

let rec box_set_helper expr = 
  (match expr with
  | Const'(x) -> expr
  | Var'(x) -> expr
  | BoxSet'(a,b) -> BoxSet'(a, box_set_helper b)
  | If'(test, thn, els) -> If'(box_set_helper test, box_set_helper thn, box_set_helper els)
  | Seq'(x) -> Seq'(List.map (fun a -> box_set_helper a) x)
  | Set'(a,b) -> Set'(box_set_helper a, box_set_helper b)
  | Def'(a,b) -> Def'(box_set_helper a, box_set_helper b)
  | Or'(x) -> Or'(List.map (fun a -> box_set_helper a) x)
  | LambdaSimple'(str_list, body) -> LambdaSimple'(str_list, lambda_boxing str_list body)
  | LambdaOpt'(str_list, str, body) -> LambdaOpt'(str_list, str, lambda_boxing (str_list@[str]) body)
  | Applic'(x, x_list) -> Applic'(box_set_helper x, List.map (fun a -> box_set_helper a) x_list)
  | ApplicTP'(x, x_list) -> ApplicTP'(box_set_helper x, List.map (fun a -> box_set_helper a) x_list)
  | _ -> expr)
  
  and lambda_boxing parameters body = 
    let body_after_change = change_body parameters body in
    box_set_helper body_after_change

  and change_body parameters body = 
    let should_box_list = (List.map (fun param -> find_rw_and_box param [1] body) parameters) in
    let newbody = create_the_body should_box_list parameters parameters body in
    newbody

  and create_the_body should_box_list parameters allParameters body = 
    match parameters with
    | [] -> body
    | car::cdr -> if (List.hd should_box_list) then (let min = (find_minor_index_in_list allParameters car 0) in
                                                     let newbody = match body with
                                                                  | Seq'(Set'(x,Box'(y))::[restOfBody]) -> Seq'(Set'(x,Box'(y))::(Set'(Var'(VarParam(car, min)), Box'(VarParam(car, min))))::[(box_the_body car restOfBody)])
                                                                  | _ -> Seq'(Set'(Var'(VarParam(car, min)), Box'(VarParam(car, min)))::[(box_the_body car body)]) in
                                                     create_the_body (List.tl should_box_list) cdr allParameters newbody)
                                              else (create_the_body (List.tl should_box_list) cdr allParameters body)


  and find_rw_and_box param acc body =  
    let _ = read_array := [] in
    let _ = write_array := [] in
    let _ = find_rw param acc false body in
    let boolean_should_box = should_box !read_array !write_array in
    boolean_should_box

  and find_rw param acc is_in_seq body =
    match body with
    | Var'(VarParam(x, maj)) when (String.equal x param) -> (read_array := acc::!read_array) 
    | Var'(VarBound(x, maj, min)) when (String.equal x param) -> (read_array :=  acc::!read_array) 
    | BoxSet'(VarParam(x, maj), rest) when (String.equal x param) -> find_rw param acc is_in_seq rest
    | BoxSet'(VarBound(x, maj, min), rest) when (String.equal x param) -> find_rw param acc is_in_seq rest
    | BoxSet'(a,b) -> find_rw param acc is_in_seq b
    | If'(tst, tn, els) -> find_rw param acc is_in_seq tst;
                           find_rw param acc is_in_seq tn;
                           find_rw param acc is_in_seq els; 
    | Seq'(sequance) -> (let _ =num_in_seq := 1 in
                         List.iter (fun x -> ()) (List.map (fun x -> find_rw param acc true x) sequance )
                         )  
    | Set'(Var'(VarParam(x, maj)), rest) when (String.equal x param) -> (let _ = (write_array:= acc::!write_array) in
                                                                         find_rw param acc is_in_seq rest)
    | Set'(Var'(VarBound(x, maj, min)), rest) when (String.equal x param) -> (let _ = (write_array:= acc::!write_array) in
                                                                              find_rw param acc is_in_seq rest)
    | Set'(a,b) -> find_rw param acc is_in_seq b
    | Def'(a,b) -> find_rw param acc is_in_seq a;
                   find_rw param acc is_in_seq b;
    | Or'(sequance) -> List.map (fun x -> find_rw param acc true x) sequance |> ignore
    | LambdaSimple'(param_list, newbody) when (not (List.mem param param_list)) -> (if (is_in_seq) 
                                            then (find_rw param ([!num_in_seq]@acc) false newbody;
                                                num_in_seq:= !num_in_seq + 1)
                                            else(find_rw param ([1]@acc) is_in_seq newbody;)) 
    | LambdaOpt'(param_list, str, newbody) when (not (List.mem param (str::param_list))) -> (if (is_in_seq) 
                                            then(find_rw param ([!num_in_seq]@acc) false newbody;
                                                num_in_seq:= !num_in_seq + 1)
                                            else(find_rw param ([1]@acc) is_in_seq newbody;))
    | Applic'(x, x_list) -> (find_rw param acc is_in_seq x;
                            List.map (fun x -> find_rw param acc true x) x_list |> ignore;)
    | ApplicTP'(x, x_list) -> (find_rw param acc is_in_seq x;
                            List.map (fun x -> find_rw param acc true x) x_list |> ignore;)   
    | _ -> ()

  and should_box readarr writearr = 
    match readarr, writearr with
    | [],_ -> false
    | _,[] -> false
    | _ -> should_box_aux !read_array !write_array

  and box_the_body param body = 
    match body with
    | Var'(VarParam(x, maj)) when (String.equal x param) -> BoxGet'(VarParam(x, maj)) 
    | Var'(VarBound(x, maj, min)) when (String.equal x param)  -> BoxGet'(VarBound(x, maj, min))  
    | BoxSet'(var, rest) -> BoxSet'(var, box_the_body param rest)
    | If'(tst, tn, els) -> If'(box_the_body param tst, box_the_body param tn, box_the_body param els)
    | Seq'(sequance) -> Seq'(List.map (fun x -> box_the_body param x) sequance)
    | Set'(Var'(VarParam(x, maj)), rest) when (String.equal x param) -> BoxSet'(VarParam(x, maj), box_the_body param rest) 
    | Set'(Var'(VarBound(x, maj, min)), rest) when (String.equal x param) -> BoxSet'(VarBound(x, maj, min), box_the_body param rest) 
    | Set'(a,b) -> Set'(a, box_the_body param b)
    | Or'(sequance) -> Or'(List.map (fun x -> box_the_body param x) sequance)
    | LambdaSimple'(param_list, newbody) when (not(List.mem param param_list)) -> LambdaSimple'(param_list, box_the_body param newbody) 
    | LambdaOpt'(param_list, str, newbody) when (not (List.mem param (str::param_list))) -> LambdaOpt'(param_list, str, box_the_body param newbody)
    | Applic'(x, x_list) -> Applic'(box_the_body param x, List.map (fun x -> box_the_body param x) x_list)
    | ApplicTP'(x, x_list) -> ApplicTP'(box_the_body param x, List.map (fun x ->box_the_body param x) x_list)
    | _ -> body

let annotate_lexical_addresses e = annotate_LA_with_lexical_env ([]) e;;
  
let annotate_tail_calls e = annotate_tail_calls_helper false e;;
  
let box_set e = box_set_helper e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)

