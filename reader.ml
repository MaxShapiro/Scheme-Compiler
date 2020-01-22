#use "pc.ml";;

open PC;;

exception X_not_yet_implemented;;

exception X_this_should_not_happen;;

exception X_char of char;;

type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;



(* ----------    helping functions -----------*)  

let make_nt_digit ch_from ch_to displacement =
  let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
  let nt = pack nt (let delta = (Char.code ch_from) - displacement in
      fun ch -> (Char.code ch) - delta) in
nt;;

let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let make_spaced nt =
  make_paired (star nt_whitespace) (star nt_whitespace) nt;;

let base_getter nt s = 
  let ((a,b),c) = nt s in
  let base = int_of_string(list_to_string b) in
  base;;


let rec list_dup_check tag_to_avoid sexprlist =
    match sexprlist with
    | [] -> true
    | (a::b) -> match a with
                |TaggedSexpr(tag, s) -> if (String.equal tag tag_to_avoid) then false else (list_dup_check tag_to_avoid b)
                | _ -> list_dup_check tag_to_avoid b ;;

let rec list_to_proper_list list_of_sexpr = 
  match list_of_sexpr with
  | [] -> Nil
  | (a::b)->( match a with
             | TaggedSexpr(tag, s) -> if (list_dup_check tag b) then Pair (a ,list_to_proper_list b) else raise X_this_should_not_happen
             | _ -> Pair (a ,list_to_proper_list b));;

let rec list_to_improper_list_helper list_before_dot last_single_sexpr =
    match list_before_dot with
    | [] -> last_single_sexpr
    | (a::b) -> Pair(a, list_to_improper_list_helper b last_single_sexpr);;

let rec check_for_duplication tag_to_avoid sexpr =
  match sexpr with
  | Pair(left, right) -> Pair((check_for_duplication tag_to_avoid left), (check_for_duplication tag_to_avoid right))
  | TaggedSexpr(tag, s) ->
  if (String.equal tag tag_to_avoid) then raise X_this_should_not_happen
  else TaggedSexpr(tag, check_for_duplication tag_to_avoid s)
  | _ -> sexpr;;


let rec check_dual lst sexpr = 
  match sexpr with
  | Pair(car,cdr) -> check_dual (check_dual lst car) cdr
  | TaggedSexpr(tag, tagged_sexp) -> if (List.mem tag lst) 
                                                then raise X_this_should_not_happen
                                                else begin 
                                                check_dual (tag::lst) tagged_sexp
                                                end
  | _ -> lst;;
  
(*---------------------- parsers ------------------------*) 
  
let rec sexp s = 
   skip_comments(disj_list [boolean_nt; char_nt; number_nt; string_nt; symbol_nt; empty_list; list_nt; dotted_list_nt;
            quoted_nt; quasi_quoted_nt; unquoted_nt; unquoted_spliced_nt; tagged_expr_nt; tagged_nt; radix_int; radix_float; nil_nt]) s

and line_comment_nt s = 
  let comment_prefix_nt = char ';' in
  let actual_comment_nt = plus (range (char_of_int 11) (char_of_int 127)) in (*All chars beside '\n'*)
  let comment_suffix_nt = char '\n' in
  let nt = caten comment_prefix_nt actual_comment_nt in
  let nt = caten nt comment_suffix_nt in
  pack nt (function x -> ' ') s

and sexpr_comments_nt s = 
  let comment_prefix_nt = word "#;" in
  let nt = caten comment_prefix_nt sexp in
  pack nt (function x -> ' ') s

and whitespace_nt s =
  pack nt_whitespace (function x -> ' ') s

and skip_comments the_big_one s =
  let possible_comments = disj_list [line_comment_nt; sexpr_comments_nt; nt_whitespace] in
  let nt = star possible_comments in
  let nt = make_paired nt nt the_big_one in
  let nt = pack nt (function x -> x) in
  nt s

and nil_nt s = 
  let nt = word "()"  in
  let nt = pack nt (fun _ -> Nil) in
  nt s

and boolean_nt s = 
  let true_nt = word_ci "#t" in
  let true_nt = pack true_nt (fun x->Bool(true)) in
  let false_nt = word_ci "#f" in
  let false_nt = pack false_nt (fun x->Bool(false)) in
  disj true_nt false_nt s

and char_nt s = 
  let nt = disj named_char visible_simple_char  in
  let nt = caten char_prefix nt in
  pack nt (fun (a,b) -> Char(b)) s
  
and char_prefix s= word "#\\" s

and visible_simple_char s = range (char_of_int 33) (char_of_int 127) s

and named_char s= 
  let nul = pack (word_ci "nul") (fun x -> char_of_int 0) in
  let newline = pack (word_ci "newline") (fun x -> char_of_int 10) in
  let return = pack (word_ci "return") (fun x -> char_of_int 13) in
  let tab = pack (word_ci "tab") (fun x -> char_of_int 9) in
  let formfeed = pack (word_ci "page") (fun x -> char_of_int 12) in
  let space = pack (word_ci "space") (fun x -> char_of_int 32) in
  disj_list[nul; newline; return; tab; formfeed; space] s

and digit_nt s = range '0' '9' s 

and number_nt s =
  let integer_or_float = not_followed_by (disj_list [ scientific; construct_float_nt; construct_integer_nt]) symbol_nt in
    pack integer_or_float (function (x) -> Number (x)) s

and integer_nt s = 
  let plus_nt = char '+' in
  let minus_nt = char '-' in
  let plus_minus_nt = disj plus_nt minus_nt in
  let maybe_plus_minus = PC.maybe plus_minus_nt in
  let nt = caten maybe_plus_minus natural_nt in
  pack nt (function (a,b)-> 
    match a with
    | Some '-' -> '-' :: b
    | Some '+' -> '+' :: b
    | None -> b
    | _ -> raise X_no_match) s

and construct_integer_nt s = 
  pack integer_nt (fun x -> Int(int_of_string(list_to_string x))) s

and natural_nt s = plus digit_nt s 

and float_nt s =
  let dot = word "." in
  let nt = caten_list [integer_nt; dot; natural_nt] in
  pack nt (fun (list) -> List.concat list ) s

and construct_float_nt s = 
  pack float_nt (function a -> 
    match a with
    | '-'::b -> Float (-1.0 *. float_of_string (list_to_string (b)))
    | '+'::b -> Float (float_of_string (list_to_string (b)))
    | any -> Float (float_of_string (list_to_string (a)))
    ) s

and scientific s = 
  let left_side_nt = disj float_nt integer_nt  in
  let e = word_ci "e" in
  let nt = caten_list [left_side_nt; e; integer_nt] in
  let nt = pack nt (fun x -> List.concat x) in
  let nt = pack nt (fun x -> Float (float_of_string (list_to_string x))) in
  nt s

and radix_aux_letters base s =  
  let make_nt_digit ch_from ch_to displacement =
    let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
    let nt = pack nt (let delta = (Char.code ch_from) - displacement in
        fun ch -> (Char.code ch) - delta) in
  nt in
  let nt = disj (make_nt_digit '0' '9' 0) (make_nt_digit 'a' (char_of_int(base+86)) 10) in
  let nt = disj nt (make_nt_digit 'A' (char_of_int(base+54)) 10) in
  let nt = plus nt in
  nt s

and radix_int s =
  let nt = caten (word "#") integer_nt in
  let base = base_getter nt s in
  let nt = caten nt (word_ci "r") in
  let digits = make_nt_digit '0' '9' 0 in
  let digits = disj digits (make_nt_digit 'a' 'z' 10 ) in
  let digits = disj digits (make_nt_digit 'A' 'Z' 10 ) in
  let plus_nt = char '+' in
  let minus_nt = char '-' in
  let plus_minus = disj plus_nt minus_nt in
  let maybe_plus_minus = maybe plus_minus in
  let take_care_of_int = caten nt maybe_plus_minus in
  let take_care_of_int = caten take_care_of_int (plus digits) in
  let take_care_of_int = not_followed_by take_care_of_int (char '.') in
  let take_care_of_int = pack take_care_of_int (function ((((hash,basis),r),sign),num) ->
    match sign with
    |Some '+' -> Number(Int(List.fold_left (fun a b -> base * a + b) 0 num))
    |Some '-' -> Number(Int(-1* List.fold_left (fun a b -> base * a + b) 0 num))
    |None -> Number(Int(List.fold_left (fun a b -> base * a + b) 0 num)) 
    | _ -> raise X_no_match ) in
  take_care_of_int s

and radix_float s =
  let nt = caten (word "#") integer_nt in
  let base = base_getter nt s in
  let nt = caten nt (word_ci "r") in
  let digits = make_nt_digit '0' '9' 0 in
  let digits = disj digits (make_nt_digit 'a' 'z' 10 ) in
  let digits = disj digits (make_nt_digit 'A' 'Z' 10 ) in
  let plus_nt = char '+' in
  let minus_nt = char '-' in
  let plus_minus = disj plus_nt minus_nt in
  let maybe_plus_minus = maybe plus_minus in
  let take_care_of_int = caten nt maybe_plus_minus in
  let take_care_of_int = caten take_care_of_int (plus digits) in
  let take_care_of_int = caten take_care_of_int (char '.') in
  let take_care_of_int = caten take_care_of_int (plus digits) in
  let ((a,b),c) = take_care_of_int s in
  let num_of_chars = float_of_int(List.length b)  in
  let num_of_chars = (-1.) *. num_of_chars in
  let take_care_of_int = pack take_care_of_int (function (((((((a),b),c),sign),before_dot),dot),after_dot) ->
    match sign with
    |Some '+' -> Number(Float(
    (float_of_int(List.fold_left (fun a b -> base * a + b) 0 before_dot)) +.
    (float_of_int(List.fold_left (fun a b -> (base * a + b)) 0 after_dot)) *. float_of_int(base)**(num_of_chars)))
    |Some '-' -> Number(Float( (-1.) *.
      ((float_of_int(List.fold_left (fun a b -> base * a + b) 0 before_dot)) +.
      (float_of_int(List.fold_left (fun a b -> (base * a + b)) 0 after_dot)) *. float_of_int(base)**(num_of_chars))))
    |None -> Number(Float(
      (float_of_int(List.fold_left (fun a b -> base * a + b) 0 before_dot)) +.
      (float_of_int(List.fold_left (fun a b -> (base * a + b)) 0 after_dot)) *. float_of_int(base)**(num_of_chars))) 
    | _ -> raise X_no_match ) in
    take_care_of_int s

and string_nt s = 
  let quote = word "\"" in
  let string_char_star = star string_char_nt in
  let left_quote = caten quote string_char_star in
  let nt = caten left_quote quote in
  pack nt (fun ((a,b),c) -> String(list_to_string(b))) s

and string_char_nt s = 
    disj string_literal_char_nt string_meta_char_nt s

and string_literal_char_nt s = 
  let range_until_quote = range ' ' '!' in
  let range_from_quote_to_square = range '#' '[' in 
  let rest = range ']' '~' in
  let nt = disj_list [range_until_quote; range_from_quote_to_square; rest] in
  nt s

and string_meta_char_nt s = 
  let return = pack (word_ci "\\r") (fun x -> char_of_int 13) in
  let newLine = pack (word_ci "\\n") (fun x -> char_of_int 10) in
  let tab = pack (word_ci "\\t") (fun x -> char_of_int 9) in
  let page = pack (word_ci "\\f") (fun x -> char_of_int 12) in
  let backslash = pack (word_ci "\\\\") (fun x -> char_of_int 92) in
  let doubleQuote = pack (word_ci "\\\"") (fun x -> char_of_int 34) in
  disj_list [return; newLine; tab; page; backslash; doubleQuote] s

and symbol_nt s = 
  let nt = plus symbol_char_nt in
  pack nt (fun x -> Symbol (list_to_string (x))) s
  
and symbol_char_nt s = 
  let lowercase_nt = range 'a' 'z' in
  let uppercase_nt = range 'A' 'Z' in
  let nt = disj lowercase_nt uppercase_nt in
  let nt = pack nt (fun x -> lowercase_ascii x) in
  disj_list [digit_nt; nt;
        char '!';
        char '$';
        char '^';
        char '*';
        char '-';
        char '_';
        char '=';
        char '+';
        char '<';
        char '>';
        char '?';
        char '/';
        char ':';] s
  

and list_nt s =
  let spaced_single_sexpr_nt = make_spaced sexp in
  let star_nt = star spaced_single_sexpr_nt in
  let nt = make_paired (char '(') (char ')') star_nt in
  pack nt list_to_proper_list s

and empty_list s = 
  let nt = caten (char '(') (star (char ' ')) in
  let comments = disj line_comment_nt sexpr_comments_nt in
  let nt = caten nt (star comments) in
  let nt = caten nt (star (char ' ')) in
  let nt = caten nt (char ')') in
  pack nt (fun x -> Nil) s

and list_to_improper_list list_of_sexpr = 
  match list_of_sexpr with
  | ((a, '.'), b) -> list_to_improper_list_helper a b 
  | _ -> raise X_no_match

and dotted_list_nt s=
  let spaced_single_sexpr_nt = make_spaced sexp in
  let some_spaced_sexpr_nt = plus spaced_single_sexpr_nt in
  let followed_by_a_dot_nt = caten some_spaced_sexpr_nt (make_spaced (char '.')) in
  let followed_by_a_single_sexpr_nt = caten followed_by_a_dot_nt spaced_single_sexpr_nt in
  let parenthesis_with_parser_nt = make_paired (char '(') (char ')') followed_by_a_single_sexpr_nt in
  pack parenthesis_with_parser_nt list_to_improper_list s

and quoted_nt s =
  let quoted_prefix_nt = char '\'' in
  let spaced_single_sexpr_nt = make_spaced sexp in
  let nt = caten quoted_prefix_nt spaced_single_sexpr_nt in
  pack nt (function (a,b) -> Pair(Symbol ("quote"), Pair(b, Nil))) s

and quasi_quoted_nt s=
  let quasi_quoted_prefix_nt = char '`' in
  let spaced_single_sexpr_nt = make_spaced sexp in
  let nt = caten quasi_quoted_prefix_nt spaced_single_sexpr_nt in
  pack nt (function (a,b) -> Pair(Symbol ("quasiquote"), Pair(b, Nil))) s

and unquoted_nt s=
  let unquoted_prefix_nt = char ',' in
  let spaced_single_sexpr_nt = make_spaced sexp in
  let nt = caten unquoted_prefix_nt spaced_single_sexpr_nt in
  pack nt (function (a,b) -> Pair(Symbol ("unquote"), Pair(b, Nil))) s

and unquoted_spliced_nt s =
  let unquoted_spliced_prefix_nt = word ",@" in
  let spaced_single_sexpr_nt = make_spaced sexp in
  let nt = caten unquoted_spliced_prefix_nt spaced_single_sexpr_nt in
  pack nt (function (a,b) -> Pair(Symbol ("unquote-splicing"), Pair(b, Nil))) s

and tagged_nt s =
  let symbol_nt = plus symbol_char_nt in
  let symbol_with_spaces_nt = make_spaced symbol_nt in
  let nt = make_paired (word "#{") (char '}') symbol_with_spaces_nt in
  pack nt (function (a) -> TagRef (list_to_string a)) s

and tagged_expr_nt s =
  let symbol_nt = plus symbol_char_nt in
  let symbol_with_spaces_nt = make_spaced symbol_nt in
  let tagged_nt = make_paired (word "#{") (word "}=") symbol_with_spaces_nt in
  let tag_sexpr_pair_nt = caten tagged_nt sexp in
  let nt = pack tag_sexpr_pair_nt (function (tag,sexpr) ->
              let tag = (list_to_string tag) in
              let duplication_free_sexpr = (check_for_duplication tag sexpr) in
              TaggedSexpr(tag, duplication_free_sexpr)) in
  nt s;;
  
(*----------- module ------------*)

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
  (fun ch -> (ch = (lowercase_ascii ch)))
  s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexpr string = 
  let s = string_to_list string in
  let returned = sexp s in
  let (a,b) = returned  in
  let _ = (check_dual [] a) in
  match (a,b) with 
  | (sexp, []) -> sexp
  | _ -> raise X_no_match ;;
  

let read_sexprs string = 
  let s = string_to_list string in
  let returned = (star sexp) s in
  let (a,b) = returned in
  let _ = List.map (check_dual []) a in
  (fun (exp, rest) -> exp ) returned ;;

end;; (* struct Reader *)  
