#use "semantic-analyser.ml";;
#use "labels.ml";;


(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list ->  ((constant * (int * string)) list)

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

exception X_exp of expr'

let param_count = ref 1 

let rec get_consts_from_ast list_of_consts ast = 
  match ast with
  | Const'(const) -> list_of_consts @ [const]
  | BoxSet'(v, expr) -> list_of_consts @ get_consts_from_ast list_of_consts expr
  | If'(test, thn, els) -> list_of_consts @
                           get_consts_from_ast list_of_consts test @
                           get_consts_from_ast list_of_consts thn @
                           get_consts_from_ast list_of_consts els
  | Seq'(expr_list) -> list_of_consts @ (expr_list_to_const_list ([]) expr_list)  
  | Set'(a,b) -> list_of_consts @
                  get_consts_from_ast list_of_consts a @
                  get_consts_from_ast list_of_consts b
  | Def'(a,b) -> list_of_consts @
                  get_consts_from_ast list_of_consts a @
                  get_consts_from_ast list_of_consts b
  | Or'(expr_list) -> list_of_consts @ (expr_list_to_const_list ([]) expr_list)  
  | LambdaSimple'(param_list, body) -> list_of_consts @ get_consts_from_ast list_of_consts body
  | LambdaOpt'(param_list, opt_string, body) -> list_of_consts @ get_consts_from_ast list_of_consts body
  | Applic'(expr, expr_list) -> list_of_consts @ 
                                get_consts_from_ast list_of_consts expr @
                                (expr_list_to_const_list ([]) expr_list)  
  | ApplicTP'(expr, expr_list) -> list_of_consts @ 
                                  get_consts_from_ast list_of_consts expr @
                                 (expr_list_to_const_list ([]) expr_list) 
  | _ -> list_of_consts

and expr_list_to_const_list aux_list expr_list = 
  match expr_list with
  | [] -> aux_list
  | car::cdr -> (get_consts_from_ast aux_list car) @ (expr_list_to_const_list aux_list cdr)

let rec expand_const const = 
  match const with
  | Sexpr(Symbol(str)) -> [Sexpr(String(str))] @ [const] 
  | Sexpr(Pair(TaggedSexpr(str, expr),cdr)) -> (expand_const (Sexpr(TaggedSexpr(str, expr)))) @ (expand_const (Sexpr(cdr))) @ [Sexpr(Pair(expr, cdr))]
  | Sexpr(Pair(car, TaggedSexpr(str, expr))) -> (expand_const (Sexpr(car))) @ (expand_const (Sexpr(TaggedSexpr(str, expr)))) @ [Sexpr(Pair(car, expr))]
  | Sexpr(Pair(car,cdr)) -> (expand_const (Sexpr(car))) @ (expand_const (Sexpr(cdr))) @ [const]
  | Sexpr(TagRef(x)) -> []
  | Sexpr(TaggedSexpr(str, expr)) -> expand_const (Sexpr(expr)) 
  | Sexpr(x) -> [const]  
  | Void -> []
  
let rec remove_dups list_of_consts = 
  match list_of_consts with
  | [] -> []
  | car::cdr -> car :: remove_dups (List.filter (fun x -> not(car = x)) cdr);;



let rec const_list_to_tuple_list list_to_return offset list_of_consts = 
  (match list_of_consts with
  | [] -> list_to_return
  | Void::cdr -> const_list_to_tuple_list (list_to_return@[(Void, (offset, "MAKE_VOID"))]) (offset+1) cdr
  | Sexpr(Nil)::cdr -> const_list_to_tuple_list (list_to_return@[(Sexpr(Nil), (offset, "MAKE_NIL"))]) (offset+1) cdr
  | Sexpr(Bool(false))::cdr -> const_list_to_tuple_list (list_to_return@[(Sexpr(Bool(false)), (offset, "MAKE_BOOL(0)"))]) (offset+2) cdr
  | Sexpr(Bool(true))::cdr -> const_list_to_tuple_list (list_to_return@[(Sexpr(Bool(true)), (offset, "MAKE_BOOL(1)"))]) (offset+2) cdr
  | Sexpr(Number(Int(i)))::cdr -> const_list_to_tuple_list (list_to_return@[(Sexpr(Number(Int(i))), (offset, Printf.sprintf "MAKE_LITERAL_INT(%d)" i))]) (offset+9) cdr
  | Sexpr(Number(Float(f)))::cdr -> const_list_to_tuple_list (list_to_return@[(Sexpr(Number(Float(f))), (offset, Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" f))]) (offset+9) cdr
  | Sexpr(Char(c))::cdr -> const_list_to_tuple_list (list_to_return@[(Sexpr(Char(c)), (offset, Printf.sprintf "MAKE_LITERAL_CHAR(%d)" (Char.code c)))]) (offset+2) cdr
  | Sexpr(String(x))::cdr -> (let str = String.escaped x in
                   const_list_to_tuple_list (list_to_return@[(Sexpr(String(str)), (offset, Printf.sprintf "MAKE_LITERAL_STRING %S" str))]) (offset + (String.length str) + 9) cdr)
    (* special cases *)
  | Sexpr(Symbol(str))::cdr -> const_list_to_tuple_list (list_to_return@[(Sexpr(Symbol(str)), (offset, "MAKE_LITERAL_SYMBOL(TEMP)"))]) (offset + 9) cdr
  | Sexpr(Pair(a,b))::cdr -> const_list_to_tuple_list (list_to_return@[(Sexpr(Pair(a,b)), (offset, "MAKE_LITERAL_PAIR(TEMP1, TEMP2)"))]) (offset + 17) cdr
  | _ -> []
  );;

let rec find_offset sexpr list_of_literal_tuples = 
  match list_of_literal_tuples with
  | [] -> -1
  | (Sexpr(s), (offset, txt))::cdr when s = sexpr -> offset
  | (a,(b,c))::cdr -> find_offset sexpr cdr
                                                       

let litreal_tuple_to_full tuple list_of_literal_tuples =
  (match tuple with 
  | (Sexpr(Symbol(str)), (offset, tmp_string)) -> (Sexpr(Symbol(str)), (offset, (Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" (find_offset (String(str)) list_of_literal_tuples))))
  | (Sexpr(Pair(car, cdr)), (offset, tmp_string)) -> (Sexpr(Pair(car,cdr)), (offset, (Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d)" (find_offset car list_of_literal_tuples) (find_offset cdr list_of_literal_tuples) )))
  | _ -> tuple
);;

let rec remove_tag sexp = 
  match sexp with
  | TaggedSexpr(a,b) -> b
  | Pair(a,b) -> Pair(remove_tag a, remove_tag b)
  | _ -> sexp;;

let rec change_the_name acc x =
  match x with 
  | Pair(car, cdr) -> Pair((change_the_name acc car),(change_the_name acc cdr))
  | TaggedSexpr(str, exp) -> TaggedSexpr(str ^ (string_of_int acc), change_the_name acc exp)
  | TagRef(str) -> TagRef(str ^ (string_of_int acc))
  | _ -> x

let rec change_ref_with_num acc single_ast = 
  match single_ast with
  | Const'(Sexpr(x)) -> Const'(Sexpr(change_the_name acc x))
  | BoxSet'(VarFree(x), expr) -> BoxSet'(VarFree(x), change_ref_with_num acc expr)
  | BoxSet'(VarParam(str, a), expr) -> BoxSet'(VarParam(str, a), change_ref_with_num acc expr)
  | BoxSet'(VarBound(str, a, b), expr) -> BoxSet'(VarBound(str, a, b), change_ref_with_num acc expr)
  | If'(tst,thn,els) ->  If'(change_ref_with_num acc tst, change_ref_with_num acc thn, change_ref_with_num acc els) 
  | Seq'(expr_list) -> Seq'( List.map (fun x -> change_ref_with_num acc x) expr_list)
  | Set'(a, b) -> Set'(change_ref_with_num acc a, change_ref_with_num acc b)
  | Def'(a, b) -> Def'(change_ref_with_num acc a, change_ref_with_num acc b)
  | Or'(expr_list) -> Or'( List.map (fun x -> change_ref_with_num acc x) expr_list)
  | LambdaSimple'(str_list, body) -> LambdaSimple'(str_list, change_ref_with_num acc body)
  | LambdaOpt'(str_list, str, body) -> LambdaOpt'(str_list, str, change_ref_with_num acc body)
  | Applic'(expr, expr_list) -> Applic'(change_ref_with_num acc expr, ( List.map (fun x -> change_ref_with_num acc x) expr_list))
  | ApplicTP'(expr, expr_list) -> ApplicTP'(change_ref_with_num acc expr, ( List.map (fun x -> change_ref_with_num acc x) expr_list))
  | _ -> single_ast
  ;;

let rec change_ref acc list_to_ret ast_list = 
  match ast_list with
  | car::[] -> [(change_ref_with_num acc car)]@list_to_ret
  | car::cdr -> (let tmp = [(change_ref_with_num acc car)] in
                (change_ref (acc+1) tmp cdr)@list_to_ret)
  | [] -> [];;

let rec fill_table x = 
  match x with
  | Pair(car, cdr) -> (fill_table car)@(fill_table cdr)
  | TaggedSexpr(str, exp) -> [(str, exp)]@(fill_table exp)
  | _ -> []
                 
let rec get_tagged_to_list list_to_ret ast = 
  match ast with
  | Const'(Sexpr(x)) -> (fill_table x)@list_to_ret
  | BoxSet'(VarFree(x), expr) -> (get_tagged_to_list list_to_ret expr)@list_to_ret
  | BoxSet'(VarParam(str, a), expr) -> (get_tagged_to_list list_to_ret expr)@list_to_ret
  | BoxSet'(VarBound(str, a, b), expr) -> (get_tagged_to_list list_to_ret expr)@list_to_ret
  | If'(tst,thn,els) -> (get_tagged_to_list list_to_ret tst)@(get_tagged_to_list list_to_ret thn)@(get_tagged_to_list list_to_ret els)@list_to_ret
  | Seq'(expr_list) -> (get_tagged_aux ([]) expr_list)@list_to_ret
  | Set'(a, b) -> (get_tagged_to_list list_to_ret a)@(get_tagged_to_list list_to_ret b)@list_to_ret
  | Def'(a, b) -> (get_tagged_to_list list_to_ret a)@(get_tagged_to_list list_to_ret b)@list_to_ret
  | Or'(expr_list) -> (get_tagged_aux ([]) expr_list)@list_to_ret
  | LambdaSimple'(str_list, body) -> (get_tagged_to_list list_to_ret body)@list_to_ret
  | LambdaOpt'(str_list, str, body) -> (get_tagged_to_list list_to_ret body)@list_to_ret
  | Applic'(expr, expr_list) -> (get_tagged_to_list list_to_ret expr)@(get_tagged_aux ([]) expr_list)@list_to_ret
  | ApplicTP'(expr, expr_list) -> (get_tagged_to_list list_to_ret expr)@(get_tagged_aux ([]) expr_list)@list_to_ret
  | _ -> list_to_ret

  and get_tagged_aux aux_list expr_list = 
  match expr_list with
  | [] -> aux_list
  | car::cdr -> (get_tagged_to_list aux_list car) @ (get_tagged_aux aux_list cdr);;


let find_offset_final car list_of_literal_tuples list_of_names_exprs = 
  match car with
  | TagRef(x) -> (let expr = (List.assoc x list_of_names_exprs) in
                  fst (List.assoc (Sexpr(expr)) list_of_literal_tuples))
  | _ -> find_offset car list_of_literal_tuples

let final_const tuple list_of_literal_tuples list_of_names_exprs = 
  match tuple with 
  | (Sexpr(Pair(car, cdr)), (offset, tmp_string)) when (String.contains tmp_string '-') -> (Sexpr(Pair(car, cdr)), (offset, (Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d)" (find_offset_final car list_of_literal_tuples list_of_names_exprs) (find_offset_final cdr list_of_literal_tuples list_of_names_exprs))))
  | _ -> tuple;;

let make_consts_tbl_aux asts = 
  let asts_with_changed_ref = change_ref 1 ([]) asts in
  let list_of_names_exprs = List.flatten (List.map (fun ast -> get_tagged_to_list ([]) ast) asts_with_changed_ref) in
  let list_of_names_without_tagged = List.map (fun (str, x) -> (str,(remove_tag x))) list_of_names_exprs in
  let initial_list_of_consts = List.flatten (List.map (fun ast -> get_consts_from_ast ([]) ast) asts_with_changed_ref) in
  let expanded_list = List.flatten (List.map (fun const -> expand_const const) initial_list_of_consts) in
  let no_tags = List.map (fun (a) ->
                                    (match a with
                                    | Sexpr(x) -> (Sexpr(remove_tag x))
                                    | Void -> Void)) expanded_list in
  let list_with_mendatory_prefix = [Void; Sexpr(Nil); Sexpr(Bool(false)); Sexpr(Bool(true))] @ no_tags in
  let list_without_dups = remove_dups list_with_mendatory_prefix in
  let list_of_literal_tuples = const_list_to_tuple_list ([]) 0 list_without_dups in
  let tmp = list_of_literal_tuples in
  let list_of_tuples = List.map (fun tuple -> litreal_tuple_to_full tuple list_of_literal_tuples) tmp in
  let final = List.map (fun tuple -> final_const tuple list_of_literal_tuples list_of_names_without_tagged) list_of_tuples in
  final;;

let rec get_all_free_vars list_to_return asts = 
    match asts with
  | Var'(VarFree(x)) -> list_to_return@[x]
  | Box'(VarFree(x))-> list_to_return@[x]
  | If'(tst,thn,els) -> (list_to_return@
                        get_all_free_vars list_to_return thn@
                        get_all_free_vars list_to_return els)
  | Seq'(expr_list)-> list_to_return @ (get_free_vars_from_list ([]) expr_list)
  | Set'(a,b) ->  list_to_return @
                  get_all_free_vars list_to_return a @
                  get_all_free_vars list_to_return b
  | Def'(a,b) ->  list_to_return @
                  get_all_free_vars list_to_return a @
                  get_all_free_vars list_to_return b
  | Or'(expr_list) -> list_to_return @ (get_free_vars_from_list ([]) expr_list)
  | LambdaSimple'(param_list, body) -> list_to_return @ get_all_free_vars list_to_return body
  | LambdaOpt'(param_list, opt_string, body) -> list_to_return @ get_all_free_vars list_to_return body
  | Applic'(expr, expr_list) -> list_to_return @ 
                                get_all_free_vars list_to_return expr @
                                (get_free_vars_from_list ([]) expr_list)  
  | ApplicTP'(expr, expr_list) -> list_to_return @ 
                                  get_all_free_vars list_to_return expr @
                                 (get_free_vars_from_list ([]) expr_list) 
  | _ -> list_to_return

and get_free_vars_from_list aux_list expr_list = 
  match expr_list with
  | [] -> aux_list
  | car::cdr -> (get_all_free_vars aux_list car) @ (get_free_vars_from_list aux_list cdr);;

let rec free_list_to_tuple_list list_to_return offset free_vars_list = 
  (match free_vars_list with
  | [] -> list_to_return
  | x::cdr -> free_list_to_tuple_list (list_to_return@[(x, offset)]) (offset+1) cdr
  );;

let make_fvars_tbl_aux asts = 
  let list_of_free_vars = List.flatten (List.map (fun ast -> get_all_free_vars ([]) ast) asts) in
  let removed_dups = remove_dups list_of_free_vars in
  let list_of_tuples = free_list_to_tuple_list ([]) 29 removed_dups in
  list_of_tuples;;

let rec get_num_of_args acc arg_list =
  match arg_list with
  | [] -> acc
  | car::cdr -> get_num_of_args (acc +1) cdr

  
let rec generate_aux acc consts_tbl fvars_tbl expr = 
  match expr with
  | Const'(c) ->  (let constlable = Labels.make_label "Gen_Const" in
                   Printf.sprintf "%s:\nmov rax, const_tbl+%d\nend_%s:\n" (constlable) (fst (List.assoc c consts_tbl)) (constlable))
  | Var'(VarParam(_, minor)) -> (let varlable = Labels.make_label "Gen_Var_Param" in
                                Printf.sprintf "%s:\n mov rax, qword[rbp + 8 * (4 + %d)]\nend_%s:\n" (varlable) (minor) (varlable)) 
  | Var'(VarBound(_, major, minor)) -> (let varlable = Labels.make_label "Gen_Var_Bound" in
                                       Printf.sprintf "%s:\nmov rax, qword[rbp + (8 * 2)]\nmov rax, qword[rax + (8 * %d)]\nmov rax, qword[rax + (8 * %d)]\nend_%s:\n" (varlable) (major) (minor) (varlable))
  | Var'(VarFree(v)) -> (let varlable = Labels.make_label "Gen_Var_Free" in 
                        Printf.sprintf "%s:\nmov rax, qword [fvar_tbl+(%d*8)]\nend_%s:\n" (varlable) (List.assoc v fvars_tbl) (varlable))
  | Box'(v) -> (let varlable = Labels.make_label "Gen_Box" in        	
                      Printf.sprintf "%s:\n%s\nMALLOC r10, 8\nmov qword[r10], rax\nmov rax, r10\nend_%s:\n" (varlable) (generate_aux acc consts_tbl fvars_tbl (Var'(v))) (varlable))
  | BoxGet'(v) -> (let boxlable = Labels.make_label "Gen_Box_Get" in
                   Printf.sprintf "%s:\n%s\nmov rax, qword [rax]\nend_%s:\n" (boxlable) (generate_aux acc consts_tbl fvars_tbl (Var'(v))) (boxlable))
  | BoxSet'(v,e) -> (let boxlable = Labels.make_label "Gen_Box_get" in 
                    Printf.sprintf "%s:\n%s\npush rax\n%s\npop qword [rax]\nmov rax, SOB_VOID_ADDRESS\nend_%s:\n" (boxlable) (generate_aux acc consts_tbl fvars_tbl e) (generate_aux acc consts_tbl fvars_tbl (Var'(v))) (boxlable) )
  | If'(tst,thn,els) ->( let iflable = Labels.make_label "Gen_If" in
                         let elselable = Labels.make_label "Lelse" in
                         let exitlable = Labels.make_label "Lexit" in
                         Printf.sprintf "%s:\n%s\ncmp rax, SOB_FALSE_ADDRESS\nje %s\n%s\njmp %s\n%s:\n%s\n%s:\nend_%s:\n" (iflable) (generate_aux acc consts_tbl fvars_tbl tst) (elselable) (generate_aux acc consts_tbl fvars_tbl thn) (exitlable) (elselable) (generate_aux acc consts_tbl fvars_tbl els) (exitlable) (iflable) ) 
  | Seq'(expr_list) -> (let seqlable = Labels.make_label "Gen_Seq" in
                         Printf.sprintf "%s:\n%s\nend_%s:\n" (seqlable) (String.concat "\n" (List.map (fun e -> generate_aux acc consts_tbl fvars_tbl e) expr_list)) (seqlable))
  | Set'(Var'(VarParam(_, minor)), e) -> (let lable = Labels.make_label "Gen_Set_Var_Param" in
                                          Printf.sprintf "%s:\n%s\nmov qword [rbp + 8 * (4 + %d)], rax\nmov rax, SOB_VOID_ADDRESS\nend_%s:\n" (lable) (generate_aux acc consts_tbl fvars_tbl e) (minor) (lable))
  | Set'(Var'(VarBound(_,major,minor)),e) -> (let lable = Labels.make_label "Gen_Set_Var_Bound" in
                                              Printf.sprintf "%s:\n%s\nmov rbx, qword [rbp + 8 * 2]\nmov rbx, qword [rbx + 8 * %d]\nmov qword [rbx + 8 * %d], rax\nmov rax, SOB_VOID_ADDRESS\nend_%s:\n" (lable) (generate_aux acc consts_tbl fvars_tbl e) (major) (minor) (lable))
  | Set'(Var'(VarFree(v)),e) -> (let lable = Labels.make_label "Gen_Set_Var_Free" in 
                                Printf.sprintf "%s:\n%s\nmov qword [fvar_tbl+(%d*8)], rax\nmov rax, SOB_VOID_ADDRESS\nend_%s:\n" (lable) (generate_aux acc consts_tbl fvars_tbl e) (List.assoc v fvars_tbl) (lable) )
  | Def'(Var'(VarFree(v)),e) -> (let lable = Labels.make_label "Gen_Def_Var_Free" in
                                Printf.sprintf "%s:\n%s\nmov qword [fvar_tbl+(%d*8)], rax\nmov rax, SOB_VOID_ADDRESS\nend_%s:\n" (lable) (generate_aux acc consts_tbl fvars_tbl e) (List.assoc v fvars_tbl) (lable))
  | Or'(expr_list) -> (let lable = Labels.make_label "Gen_Or" in
                      let lexit = Labels.make_label "Lexit" in
                       Printf.sprintf "%s:\n%s\nend_%s:\n" (lable) (or_epxr_to_string lexit acc consts_tbl fvars_tbl "" expr_list) (lable))
  | Applic'(proc, arg_list) -> (let lable = Labels.make_label "Gen_Applic" in
                                Printf.sprintf "%s:\n%s\nend_%s:\n" (lable) (generate_applic acc proc arg_list consts_tbl fvars_tbl) (lable))
  | ApplicTP'(proc, arg_list) -> (let lable = Labels.make_label "Gen_ApplicTP" in
                                Printf.sprintf "%s:\n%s\nend_%s:\n" (lable) (generate_applicTP acc proc arg_list consts_tbl fvars_tbl) (lable))
  | LambdaSimple'(param_list, body) -> (let lable = Labels.make_label "Gen_Lambda_Simple" in
                                        Printf.sprintf "%s:\n%s\nend_%s:\n" (lable) (generate_lambda_simple acc param_list body consts_tbl fvars_tbl) (lable))
  | LambdaOpt'(param_list, str, body) -> (let lable = Labels.make_label "Gen_Lambda_Opt" in
                                          Printf.sprintf "%s:\n%s\nend_%s:\n" (lable) (generate_lambda_opt acc param_list str body consts_tbl fvars_tbl) (lable))
  | _ -> raise (X_exp expr)

and generate_lambda_simple env_depth param_list body consts_tbl fvars_tbl = 
  let loop_lable = Labels.make_label "loop" in
  let move_params_loop = Labels.make_label "move_params_loop" in
  let lcode = Labels.make_label "Lcode" in
  let lcont = Labels.make_label "Lcont" in
  let first_lambda = Labels.make_label "first_lambda" in
  (Printf.sprintf
  "; allocate ExtEnv to be of size |Env| + 1
  
  mov r9, %d                          ; r9 holds the depth of the env
  MALLOC rbx, r9                ; for dummy frame
  mov qword[rbx], SOB_NIL_ADDRESS
  cmp r9, 8                           ; if first lambda -> skip the old env copy
  je %s 
  MALLOC rbx, r9                      ; rbx now holds ExtEnv
  mov rdx, qword[rbp + 8*2]           ; rdx now points to the old env
  mov r8, 0                           ; r8 = i 
  mov r9, 1                           ; r9 = j
  
  %s:                                  ; loop ExtEnv[i+1] = Env[i]
  mov r10, qword[rdx + 8*r8]
  mov qword[rbx + 8*r9], r10
  inc r8
  inc r9
  cmp r9, %d
  jle %s
  mov r8, 0
  mov rcx, qword[rbp + 8*3]            ; rcx now holds the number of the params         
  imul rcx, rcx, 8
  MALLOC rdx, rcx                      ; rdx now holds array for the params                
  %s:  
  mov r9, qword[rbp + 8*(4+r8)]
  mov qword[rdx + r8*8], r9             ; rdx[i] = Param-i
  inc r8
  cmp r8, qword[rbp + 8*3]
  jle %s
  mov qword[rbx + 0], rdx              ; ExtEnv[0] = param_list
  %s:
  MAKE_CLOSURE(rax, rbx, %s)
  jmp %s
  %s:
    push rbp
    mov rbp, rsp
    %s
    leave
    ret
  %s:
  " ((env_depth+1)*8)(first_lambda)(loop_lable)(env_depth)(loop_lable)(move_params_loop)(move_params_loop)(first_lambda)(lcode)(lcont)(lcode)
  (generate_aux (env_depth+1) consts_tbl fvars_tbl body)(lcont))

and generate_lambda_opt env_depth param_list str body consts_tbl fvars_tbl = 
  let loop = Labels.make_label "loop" in
  let finish_pairing = Labels.make_label "finish_pairing" in
  let num_of_params = get_num_of_args 0 param_list in
  let loop_lable = Labels.make_label "loop" in
  let move_params_loop = Labels.make_label "move_params_loop" in
  let lcode = Labels.make_label "Lcode" in
  let lcont = Labels.make_label "Lcont" in
  let first_lambda = Labels.make_label "first_lambda" in
  let opt_cont = Labels.make_label "Opt_lable" in
  (Printf.sprintf
  "; allocate ExtEnv to be of size |Env| + 1

  mov r9, %d                          ; r9 holds the depth of the env
  MALLOC rbx, r9            ; for dummy frame

  cmp r9, 8                           ; if first lambda -> skip the old env copy
  mov qword[rbx], SOB_NIL_ADDRESS
  je %s 
  MALLOC rbx, r9                      ; rbx now holds ExtEnv
  mov rdx, qword[rbp + 8*2]           ; rdx now points to the old env
  mov r8, 0                           ; r8 = i 
  mov r9, 1                           ; r9 = j
  
  %s:                                  ; loop ExtEnv[i+1] = Env[i]
  mov r10, qword[rdx + 8*r8]
  mov qword[rbx + 8*r9], r10
  inc r8
  inc r9
  cmp r9, %d
  jle %s
  mov r8, 0
  mov rcx, PARAM_COUNT            ; rcx now holds the number of the params         
  imul rcx, rcx, 8
  MALLOC rdx, rcx                      ; rdx now holds array for the params                
  %s:  
  mov r9, qword[rbp + 8*(4+r8)]
  mov qword[rdx + r8*8], r9             ; rdx[i] = Param-i
  inc r8
  cmp r8, PARAM_COUNT
  jle %s
  mov qword[rbx + 0], rdx              ; ExtEnv[0] = param_list
  %s:
  MAKE_CLOSURE(rax, rbx, %s)
  jmp %s
  %s:
        push rbp
    mov rbp, rsp
    ;adjust the stack for the optional arguments
    mov rax, %d           ; num of params
    mov r15, qword[rbp + (8*3)]           ; num of args
    cmp rax, r15
    jg %s
    mov qword[rbp + (8*3)], rax           ; change num of args 
    ; make pairs
    mov r9, qword[rbp + 8*(3+r15)]        ; r9 holds last arg
    mov r10, SOB_NIL_ADDRESS              ; for the last pair
    mov r11, r15
    MAKE_PAIR(r8, r9, r10)                ; Pair(last_arg, NIL)
    %s: 
    cmp r11, rax                          ; if top = bottom, finish
    je %s 
    dec r11
    mov r10, qword[rbp + 8*(3 + r11)]
    mov r13, r8
    MAKE_PAIR(r8, r10, r13)
    jmp %s 
    %s:
    mov qword[rbp + 8*(3+rax)], r8          ; the last element is now a pair
  
    ; change the stack
    mov r9, rax
    mov r10, rax
    add r10, 4
    mov rdx, r15
    add rdx, 2
    _%s:
    cmp r10, 0
    je __%s
    dec r10
    dec rdx
    mov rcx, [rbp + r10*8]
    mov [rbp + 8*(2+rdx)], rcx
    jmp _%s       ; finised moving args
    
    __%s: 
    add rdx, 2
    shl rdx, 3
    add rsp, rdx
    mov rbp, rsp
    %s:
    %s
    leave
    ret
  %s:
  " ((env_depth+1)*8)(first_lambda)(loop_lable)(env_depth)(loop_lable)(move_params_loop)(move_params_loop)(first_lambda)(lcode)(lcont)(lcode)(num_of_params +1)(opt_cont)(loop)(finish_pairing)(loop)(finish_pairing)
  (loop)(loop)(loop)(loop)(opt_cont)(generate_aux (env_depth+1) consts_tbl fvars_tbl body)(lcont))

and generate_applic acc proc arg_list consts_tbl fvars_tbl = 
  let magic = "\npush SOB_NIL_ADDRESS\n" in
  let args =  if (List.length arg_list = 0) then (magic )
                                            else (magic ^ (String.concat "\npush rax\n" (List.map (fun x -> generate_aux acc consts_tbl fvars_tbl x) (List.rev arg_list))) ^ "\npush rax\n") in
  let args_with_proc = args ^ Printf.sprintf "\npush %d\n" (get_num_of_args 0 arg_list) ^ (generate_aux acc consts_tbl fvars_tbl proc) in 
  let debug = Labels.make_label "debug"  in
  (Printf.sprintf 
              "%s
               mov bl, byte [rax]
               cmp bl, T_CLOSURE
               jne error_exit
               push qword[rax+1] ; push env
               call [rax+9]      ; call closure
               add rsp, 8*1      ; pop env
               %s:
               pop rbx           ; pop arg count
               inc rbx           ; include magic
               shl rbx, 3        ; rbx = rbx * 8
               add rsp, rbx      ; pop args" 
args_with_proc debug)

and generate_applicTP acc proc arg_list consts_tbl fvars_tbl = 
  let magic = "\npush SOB_NIL_ADDRESS\n" in
 let args =  if (List.length arg_list = 0) then (magic )
                                            else (magic ^ (String.concat "\npush rax\n" (List.map (fun x -> generate_aux acc consts_tbl fvars_tbl x) (List.rev arg_list))) ^ "\npush rax\n") in
  let args_with_proc = args ^ Printf.sprintf "\npush %d\n" (get_num_of_args 0 arg_list) ^ (generate_aux acc consts_tbl fvars_tbl proc) in 
  let debug = Labels.make_label "debug"  in
  (Printf.sprintf 
              "%s
               mov bl, byte [rax]   
               cmp bl, T_CLOSURE    
               jne error_exit   
               push qword[rax+1] ; push env   
               push qword[rbp + 8]  ; old ret addr    
              %s:
               mov r11, [rbp]    
               mov r12, PARAM_COUNT   
               SHIFT_FRAME %d                                 
               add r12, 5
               shl r12, 3
               add rsp, r12
               mov rbp, r11
               jmp [rax + 9]
               "

args_with_proc debug((get_num_of_args 0 arg_list)+5) )


and or_epxr_to_string lexit acc consts_tbl fvars_tbl str_to_return expr_list = 
  match expr_list with
  | car::[] -> str_to_return ^ (generate_aux acc consts_tbl fvars_tbl car) ^ "\n" ^lexit^":"
  | car::cdr -> or_epxr_to_string lexit acc consts_tbl fvars_tbl (str_to_return ^ (generate_aux acc consts_tbl fvars_tbl car) ^ "cmp rax, SOB_FALSE_ADDRESS\njne "^lexit^"\n") cdr 
  | [] -> "";;

let rec remove_tagged expr = 
  match expr with
  | Const'(Sexpr(x)) -> Const'(Sexpr(remove_tag x))
  | BoxSet'(v, e) -> BoxSet'(v,remove_tagged e)
  | If'(a,b ,c) -> If'(remove_tagged a,remove_tagged b ,remove_tagged c)
  | Seq'(e) -> Seq'(List.map (fun x -> remove_tagged x )e)  
  | Set'(a,b) -> Set'(remove_tagged a,remove_tagged b)
  | Def'(a,b) -> Def'(remove_tagged a,remove_tagged b)
  | Or'(e) -> Or'(List.map (fun x -> remove_tagged x )e)
  | LambdaSimple'(a,b) -> LambdaSimple'(a,remove_tagged b) 
  | LambdaOpt'(a,b,c) -> LambdaOpt'(a,b,remove_tagged c)
  | Applic'(a, b) -> Applic'(remove_tagged a, List.map (fun x -> remove_tagged x) b)
  | ApplicTP'(a,b) -> ApplicTP'(remove_tagged a, List.map (fun x -> remove_tagged x) b)
  | _ -> expr

let generate_aux_aux acc consts_tbl fvars_tbl expr = 
  let newexpr = change_ref 1 ([]) [expr] in
  let no_tagged = remove_tagged (List.hd newexpr) in
  generate_aux acc consts_tbl fvars_tbl no_tagged;;

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = make_consts_tbl_aux asts;;
  let make_fvars_tbl asts = make_fvars_tbl_aux asts;;
  let generate consts fvars e = generate_aux_aux 0 consts fvars e;;
end;;
