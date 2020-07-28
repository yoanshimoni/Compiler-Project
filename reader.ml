
#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;




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



let maybeNil nt s =
  try let (e, s) = (nt s) in
      (e, s)
  with X_no_match -> (Nil,s);;

let nt_digit = range_ci '0' '9';;
let nt_letter = range 'a' 'z';;
let nt_bigletter = pack (range 'A' 'Z') (fun(e)->lowercase_ascii e);;
let nt_sign = one_of "!$^*-_=+<>?/:";;

let nt_symbolChar = 
  disj_list [nt_digit; nt_bigletter; nt_letter; nt_sign];;

let nt_symbol = 
  pack (plus nt_symbolChar) (fun(a)->Symbol((list_to_string a)));;



let nt_boolean = 
  let t = pack (word_ci "#t") (fun (t) -> Bool(true)) in
  let f = pack (word_ci "#f") (fun (f) -> Bool(false)) in
  (disj t f);; 


let nt_charPrefix = word "#\\";;

let nt_visibleSimpleChar = const (fun ch -> ch > ' ');;

let nt_namedChar = 
  let nul = pack (word_ci "nul") (fun (a) -> char_of_int 0) in
  let newline = pack (word_ci "newline") (fun (a) -> char_of_int 10) in
  let return = pack (word_ci "return") (fun (a) -> char_of_int 13) in
  let tab = pack (word_ci "tab") (fun (a) -> char_of_int 9) in
  let page = pack (word_ci "page") (fun (a) -> char_of_int 12) in
  let space = pack (word_ci "space") (fun (a) -> char_of_int 32) in
  disj_list [nul; newline; return; tab; page; space];;

let nt_char = 
  let name = pack (caten nt_charPrefix nt_namedChar) (fun (a,b) -> Char (b)) in
  let visible = pack (caten nt_charPrefix nt_visibleSimpleChar) (fun (a,b) -> Char (b)) in
  disj name visible;; 

let nt_natural = plus (nt_digit);;

let plus = (char '+');;

let minus = (char '-');;


let nt_integer =
  pack (caten (maybe(disj minus plus)) nt_natural) 
    (function(a,b)-> match a with
    | Some('-') -> Int (int_of_string (list_to_string b) * -1)
    | _ -> Int (int_of_string (list_to_string b)));;
    

let nt_integer2 =
  pack (caten (maybe(disj minus plus)) nt_natural) 
    (function(a,b)-> match a with
    | Some('-') -> (string_of_int (int_of_string (list_to_string b) * -1))
    | _ -> (list_to_string b));;
    
let nt_integerforfloat = 
  pack (caten (maybe(disj minus plus)) nt_natural) 
    (function(a,b)-> match a with
    | Some('-') ->  ("-" ^ (list_to_string b))
    | _ -> (list_to_string b));;
    
let nt_float =
  let e = caten (caten nt_integerforfloat (char '.')) nt_natural in
  pack e (function ((int,dot),nat)-> 
  (Float (float_of_string (int ^ "." ^ (list_to_string nat)))));; 

let nt_float2 =
  let e = caten (caten nt_integerforfloat (char '.')) nt_natural in
  pack e (function ((int,dot),nat)-> 
  (int ^ "." ^ (list_to_string nat)));; 

let nt_scientific = 
  let num1 = caten (disj nt_float2 nt_integer2) (char_ci 'e') in
  let num2 = caten num1 nt_integer2 in
  pack num2 (fun ((n1,e),n2) -> (Float((float_of_string(n1^(String.make 1 e)^n2)))));; 


let make_NT_digit ch_from ch_to displacement =
    let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
    let delta = (Char.code ch_from) - displacement in
    pack nt (fun ch -> (Char.code ch) - delta);;

let nt_intdignum = 
   star (disj_list [(make_NT_digit 'a' 'z' 10); (make_NT_digit 'A' 'Z' 10); (make_NT_digit '0' '9' 0)]);;
let nt_floatdignum = 
    let e = caten nt_intdignum (char '.') in
    let e = caten e nt_intdignum in
    pack e (fun((a,b),c) -> (a,c));;

let nt_base = 
  let nt = caten (char '#') (nt_natural) in
  let nt = pack nt (fun(hash,base)->base) in
  let nt = caten nt (char_ci 'r') in
  pack nt (fun(base,radix)->(int_of_string(list_to_string base)));;

let nt_plusminus = maybe (disj minus plus);;

let nt_intradix = pack (caten nt_base (caten nt_plusminus nt_intdignum)) (fun(base,(p,number))->
     match p with
     | Some('+') -> (Int (List.fold_left (fun a b -> a * base + b) 0 number))
     | Some('-') -> (Int ((-1) * (List.fold_left (fun a b -> a * base + b) 0 number)))
     | None -> (Int (List.fold_left (fun a b -> a * base + b) 0 number))
     | _ -> raise X_no_match);;

let nt_floatradix = 
  let nt = caten nt_base (caten nt_plusminus nt_floatdignum) in
  pack nt (fun (base,(p,(dig,frac))) ->
    let numradix = float_of_int(List.fold_left (fun a b -> a * base + b) 0 dig) in
    let fracradix = float_of_int(List.fold_left (fun a b -> a * base + b) 0 frac) in
    let length = float_of_int(List.length frac * (-1)) in
    let fracmul = (float_of_int(base) ** length) in
    let fraction = fracradix *. fracmul in
    match p with
     | Some('+') -> (Float (numradix +. fraction))
     | Some('-') -> (Float ((-1.0)*. (numradix +. fraction)))
     | None -> (Float (numradix +. fraction))
     | _ -> raise X_no_match);;

let nt_radix = disj nt_floatradix nt_intradix;;
   

let nt_number = 
  let nt = (not_followed_by (disj_list [nt_radix; nt_scientific; nt_float; nt_integer]) nt_symbol) in
  pack nt (fun(n) -> Number(n));;

let nt_stringMetachar = 
  let return = pack (word_ci "\\r") (fun (a) -> char_of_int 13) in
  let newline = pack (word_ci "\\n") (fun (a) -> char_of_int 10) in
  let tab = pack (word_ci "\\t") (fun (a) -> char_of_int 9) in
  let page = pack (word_ci "\\f") (fun (a) -> char_of_int 12) in
  let backslash = pack (word_ci "\\\\") (fun (a) -> char_of_int 92) in
  let doublequote = pack (word_ci "\\\"") (fun (a) -> char_of_int 34) in
  disj_list [return; newline; tab; page; backslash; doublequote];;

let nt_stringLiteral = 
  diff nt_any (disj (char '\\') (char '\"'));;



let nt_stringChars = disj nt_stringLiteral nt_stringMetachar;;


let nt_string = 
  let e = caten (char '"') (caten (star nt_stringChars) (char '"')) in
  pack e (function (a,(b,c))-> 
    (String (list_to_string b)));;




let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let nt_spaces = star nt_whitespace;;

let make_spaces nt =
  make_paired nt_spaces nt_spaces nt;;

let nt_linecomment = 
  let semicolon = char ';' in
  let commentendof = caten (star (diff nt_any (word_ci "\n"))) (disj (word_ci "\n") nt_end_of_input) in
  let e = caten semicolon commentendof in
  make_spaces e;;


let make_comments nt = make_paired (star nt_linecomment) (star nt_linecomment) nt;;

let nt_skip nt = make_comments(make_spaces nt);;


let nt_boolean = 
  let t = pack (not_followed_by (word_ci "#t") nt_symbolChar) (fun (t) -> Bool(true)) in
  let f = pack (not_followed_by (word_ci "#f") nt_symbolChar) (fun (f) -> Bool(false)) in
  (disj t f);;


let rec nt_sexp str = 
  let parsers = disj_list [nt_boolean; nt_char; nt_number; nt_string; nt_symbol; nt_sexpcomments; nt_nil;nt_taggedsexpr;nt_tagref; nt_dottedList; nt_list; nt_quoted; nt_qquoted; nt_unquotedspliced; nt_unquoted] in
  let e = nt_skip parsers in
  pack e (function (a) -> a) str

and nt_sexpcomments str = 
  let prefix = word_ci "#;" in
  let nt = pack (caten prefix nt_sexp) (fun(pre,sexp) -> sexp) in
  let nt = pack (caten nt (maybeNil nt_sexp)) (fun(a,b)->b) in
  nt str

  
and nt_nil str = 
  let parenLeft = char '(' in
  let parenRight = char ')' in
  let e = caten parenLeft (caten (nt_skip nt_epsilon) parenRight) in
  pack e (function (a,(b,c)) -> Nil) str

  and nt_list str = 
  let parenLeft = char '(' in
  let parenRight = char ')' in
  let e1 = caten parenLeft (caten (nt_skip nt_epsilon) (star nt_sexp)) in
  let e2 = caten e1 parenRight in
  pack e2 (function ((a,(b,c)),d) -> List.fold_right (fun x y -> Pair(x,y)) c Nil) str
    
  and nt_dottedList str = 
  let parenLeft = char '(' in
  let nt_point = char '.' in
  let parenRight = char ')' in
  let e1 = caten parenLeft (caten (nt_skip nt_epsilon) (star nt_sexp)) in
  let e2 = caten e1 nt_point in
  let e3 = caten e2 (nt_skip nt_epsilon) in
  let e4 = caten e3 nt_sexp in
  let e5 = caten e4 parenRight in
  pack e5 (function ((((((a,(b,c)),d),e),f),g))-> List.fold_right (fun x y -> Pair(x,y)) c f ) str

and nt_quoted str = 
  let nt_quote = char '\'' in
  let e = caten nt_quote nt_sexp in
  pack e (fun (_,b) -> Pair(Symbol("quote"),Pair(b,Nil))) str

and nt_qquoted str = 
  let nt_qquote = char '`' in
  let e = caten nt_qquote nt_sexp in
  pack e (fun (_,b) -> Pair(Symbol("quasiquote"),Pair(b,Nil))) str
  
and nt_unquotedspliced str = 
  let nt_unquotedsplice = word ",@" in
  let e = caten nt_unquotedsplice nt_sexp in
  pack e (fun (_,b) -> Pair(Symbol("unquote-splicing"),Pair(b,Nil))) str

and nt_unquoted str = 
  let nt_unquote = char ',' in
  let e = caten nt_unquote nt_sexp in
  pack e (fun (_,b) -> Pair(Symbol("unquote"),Pair(b,Nil))) str



and nt_taggedsexpr str= 
  let nt = caten (word_ci "#{") (star nt_symbolChar) in
  let nt = caten nt (word_ci "}=") in
  let nt = caten nt (disj_list [nt_list; nt_dottedList; nt_sexp]) in
  pack nt (fun(((a,b),c),d) -> 
     TaggedSexpr ((list_to_string b), d)) str
                              
and nt_tagref str = 
  let nt = caten (word_ci "#{") (star nt_symbolChar) in
  let nt = caten nt (word_ci "}") in
  pack nt (fun ((a,b),c)-> TagRef(list_to_string b)) str


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
let (e,s) = (nt_sexp (string_to_list string)) in
  if(s == []) then e else raise X_no_match;;
  
let read_sexprs string = 
  let (e,s) = star nt_sexp (string_to_list string) in
  e;;


end;; (* struct Reader *)
