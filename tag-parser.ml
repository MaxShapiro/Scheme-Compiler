#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
  
                       
exception X_syntax_error;;

(*-----------------------------------------------------------------------*)

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  


let rec separate_arguments_from_bindings bindings = 
  match bindings with
  | Nil -> Nil
  | Pair(Pair(argument, Pair(value, Nil)), rest) -> (let arguments = separate_arguments_from_bindings rest in
                                                    (Pair(argument, arguments)))
  | _ -> raise X_syntax_error;;

let rec separate_values_from_bindings bindings = 
match bindings with
  | Nil -> Nil
  | Pair(Pair(argument, Pair(value, Nil)), rest) -> (let values = separate_values_from_bindings rest in
                                                    (Pair(value, values)))
  | _ -> raise X_syntax_error;;

let rec fake_bindings_for_letrec bindings = 
match bindings with 
  | Nil -> Nil
  | Pair(Pair(argument, Pair(value, Nil)), rest) -> Pair(Pair(argument, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"),Nil)), Nil)), fake_bindings_for_letrec rest)
  | _ -> raise X_syntax_error

let rec set_bindings_for_letrec bindings body_of_original_letrec = 
match bindings with
  | Nil -> body_of_original_letrec
  | Pair(Pair(argument, Pair(value, Nil)), rest) -> Pair(Pair(Symbol("set!"), Pair(argument, Pair(value, Nil))), set_bindings_for_letrec rest body_of_original_letrec)
  | _ -> raise X_syntax_error

let rec is_proper_list sexpr = 
  match sexpr with
  | Nil -> true
  | Pair(a,b) -> is_proper_list b
  | _-> false;;

let rec get_string_list args_list list_to_return = 
  match args_list with
  | Nil -> list_to_return
  | Pair(Symbol car, cdr) -> if (List.mem car list_to_return) then raise X_syntax_error else get_string_list cdr (List.append list_to_return [car]) 
  | Symbol(x) -> if (List.mem x list_to_return) then raise X_syntax_error else list_to_return 
  | _ -> raise X_syntax_error;;

let rec get_last_string args_list =
  match args_list with
  | Symbol(x) -> x
  | Pair(car, cdr) -> get_last_string cdr
  | _ -> raise X_syntax_error;;

let rec tag_parse = function 
  (*Constants*)
  | Pair(Symbol("quote"), Pair(x, Nil)) ->                      Const(Sexpr(x))
  | Number(x) ->                                                Const(Sexpr(Number(x)))
  | Bool(x) ->                                                  Const(Sexpr(Bool(x)))
  | Char(x) ->                                                  Const(Sexpr(Char(x)))
  | String(x) ->                                                Const(Sexpr(String(x)))
  | TaggedSexpr(str, Pair(Symbol "quote", Pair(sexpr, Nil))) -> Const(Sexpr(TaggedSexpr(str, sexpr))) 
  | TaggedSexpr(str, rest) ->                                   Const(Sexpr(TaggedSexpr(str, rest))) 
  | TagRef(x) ->                                                Const(Sexpr (TagRef ("x")))

  (*Conditionals*)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If(tag_parse test, tag_parse dit, tag_parse dif)
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) ->            If(tag_parse test, tag_parse dit, Const(Void))

  (*Lambda Expressions*)
  | Pair(Symbol("lambda"), Pair(args_list, rest)) ->if (is_proper_list args_list) 
                                                    then 
                                                      (match rest with
                                                      | Pair(a, Nil) -> LambdaSimple((get_string_list args_list ([])), tag_parse a)
                                                      | _ ->  LambdaSimple((get_string_list args_list ([])), Seq(tag_parse_proper_list rest [])))                                             
                                                    else 
                                                      (match rest with
                                                      | Pair(a, Nil) -> LambdaOpt((get_string_list args_list ([])), get_last_string args_list, tag_parse a)
                                                      | _ -> LambdaOpt((get_string_list args_list ([])), get_last_string args_list, Seq(tag_parse_proper_list rest [])))

  (*Disjunctions - Or statement*)
  | Pair(Symbol("or"), cdr) ->( match cdr with
                                | Nil -> Const(Sexpr(Bool false))
                                | Pair(x,Nil) -> tag_parse x
                                | _ -> Or(tag_parse_proper_list cdr ([])))

    (*Definitions*)                            
  | Pair(Symbol("define"), Pair(Symbol(x), Pair(cdr, Nil))) -> Def(Var(x), tag_parse cdr)

    (*MIT DEFINE*)
  | Pair(Symbol("define"), Pair(Pair(Symbol(name), argl), exprs)) ->  let name = tag_parse (Symbol(name)) in
                                                                      let lambda = tag_parse (Pair(Symbol("lambda"), Pair(argl, exprs))) in
                                                                      Def(name, lambda)
    (*Assignments*)  
  | Pair(Symbol("set!"), Pair(Symbol(x), Pair(cdr, Nil))) -> Set(Var(x), tag_parse cdr)

    (*Sequences*)
  | Pair(Symbol("begin"), cdr) -> (match cdr with
                                  | Nil -> Const(Void)
                                  | Pair(x, Nil) -> tag_parse x
                                  | _ -> Seq(tag_parse_proper_list cdr ([])))


  (*----------- MACRO EXPANSIONS -----------*)

  (*Cond*)
  | Pair(Symbol("cond"), cdr) -> tag_parse (expand_cond cdr)

  (*Let*)
  | Pair(Symbol("let"), Pair(bindings, body)) ->  
                                                  let arguments_from_bindings = separate_arguments_from_bindings bindings in
                                                  let values_from_bindings = separate_values_from_bindings bindings in
                                                  let lambda_body = (match body with
                                                                    | Pair(x,Nil) -> tag_parse x
                                                                    | _ -> Seq(tag_parse_proper_list body [])) in
                                                  Applic(LambdaSimple((get_string_list arguments_from_bindings []), lambda_body), (tag_parse_proper_list values_from_bindings []))

  
  (*Let star*)
  | Pair(Symbol("let*"), Pair(bindings, body)) -> (match bindings with
                                                  | Nil -> tag_parse (Pair(Symbol("let"), Pair(bindings, body)))
                                                  | Pair(Pair(argument, Pair(value, Nil)),Nil) -> tag_parse (Pair(Symbol("let"), Pair(bindings, body)))
                                                  | Pair(Pair(argument, Pair(value, Nil)),rest) -> 
                                                                                                let just_one_binding = Pair(Pair(argument, Pair(value, Nil)), Nil) in
                                                                                                let body_of_let = Pair(Pair(Symbol("let*"), Pair(rest, body)), Nil) in
                                                                                                tag_parse(Pair(Symbol("let"), Pair(just_one_binding, body_of_let)))
                                                  | _ -> raise X_syntax_error)

  (*LETREC*)
  | Pair(Symbol("letrec"), Pair(bindings, body)) -> (match bindings with
                                                  | Nil -> tag_parse (Pair(Symbol("let"), Pair(bindings, body)))
                                                  | Pair(Pair(argument, Pair(value, Nil)),rest) -> 
                                                        let fake_bindings = fake_bindings_for_letrec bindings in
                                                        let body_of_let = set_bindings_for_letrec bindings body in
                                                        tag_parse(Pair(Symbol("let"), Pair(fake_bindings, body_of_let)))
                                                  | _ -> raise X_syntax_error) 

  (*AND*)
  | Pair(Symbol("and"), cdr) -> expand_and cdr

  (*Quasiquoted expressions*)
  | Pair(Symbol("quasiquote"), Pair(car, Nil)) -> tag_parse (expand_QQ car)
  
  (*Applic*)
  | Pair(procedure, args_list) -> Applic(tag_parse procedure, tag_parse_proper_list args_list ([]))                              

  (*Variables*)
  | Symbol(x) -> if (List.mem x reserved_word_list) then raise X_syntax_error else Var(x)

  | _ -> raise X_syntax_error



and tag_parse_proper_list rest list_to_return =
match rest with
| Nil -> list_to_return;
| Pair(a, b) -> (tag_parse a)::(tag_parse_proper_list b list_to_return)
| _ -> raise X_syntax_error

(*Macro Expansion Functions*)

and expand_cond ribs =
  match ribs with
  | Pair(Pair(Symbol "else", x),_) -> Pair(Symbol("begin"), x)
  | Pair(Pair(test, Pair(Symbol "=>", Pair(exprf, Nil))), rest) -> (make_cond_arrow_expr test exprf rest )
  | Pair(Pair(test, expr), rest) -> (make_cond_test test expr rest)
  | _ ->raise X_syntax_error

and expand_and = function
  | Nil -> Const(Sexpr(Bool true))
  | Pair(x, Nil) -> tag_parse x
  | Pair(x, y) -> If(tag_parse x, expand_and y, Const(Sexpr(Bool false)))
  | _ -> raise X_syntax_error


and expand_QQ = function
  | Pair(Symbol("unquote"), Pair(sexp, Nil)) -> sexp
  | Pair(Symbol("unquote-splicing"), Pair(sexp,Nil)) -> raise X_syntax_error
  | Pair(Pair(Symbol("unquote-splicing"), Pair(sexp, Nil)), b) -> Pair(Symbol("append"), Pair(sexp, Pair(expand_QQ b, Nil)))
  | Pair(a, Pair(Symbol("unquote-splicing"), Pair(sexp, Nil))) -> Pair(Symbol("cons"), Pair(expand_QQ a, Pair(sexp, Nil)))
  | Pair(a, b) -> Pair(Symbol("cons"), Pair(expand_QQ a, Pair(expand_QQ b, Nil)))
  | Symbol(x) -> Pair(Symbol("quote"), Pair(Symbol(x),Nil)) 
  | Nil -> Pair((Symbol("quote")), Pair(Nil, Nil))
  | x -> Pair((Symbol("quote")), Pair(x, Nil))
  
and make_cond_arrow_expr test exprf rest =
  let lambda = Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(exprf, Nil))), Nil)) in
  let vall = Pair(Symbol("value"), Pair(test, Nil)) in
  let exprf = Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)) in
  let lambda_rest = Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(Pair(Symbol("cond"), rest), Nil))), Nil)) in
  let finish = Pair(Pair(Symbol("rest"), Nil), Nil) in
  let assignments = (match rest with
                    | Nil -> Pair(vall, Pair(lambda, Nil))
                    | _ ->   Pair(vall, Pair(lambda, Pair(lambda_rest, Nil)))) in
  let ret = (match rest with
                | Nil -> Pair(Symbol("if"), Pair(Symbol("value"), Pair(exprf, Nil)))
                | _ ->   Pair(Symbol("if"), Pair(Symbol("value"), Pair(exprf, finish)))) in
  Pair(Symbol("let"), Pair(assignments, Pair(ret, Nil)))
  
and make_cond_test test expr rest =
  let expr = (match expr with
              | Nil -> raise X_syntax_error
              | _ -> Pair(Symbol "begin", expr)) in
            (match rest with
              | Nil -> Pair(Symbol "if", Pair(test, Pair(expr, Nil)))
              | _ -> Pair(Symbol "if", Pair(test, Pair(expr, Pair(Pair(Symbol "cond", rest), Nil)))));;


(*-----------------------------------------------------------------------*)

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)



let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = List.map tag_parse_expression sexpr;;


end;; (* struct Tag_Parser *)


let a = [TaggedSexpr ("a", Symbol "b")    ];;
let b = Tag_Parser.tag_parse_expressions a;;
