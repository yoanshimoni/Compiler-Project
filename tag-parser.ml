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



let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  
   
exception X_syntax_error;;



let rec tag_parse sexpr = 
  match sexpr with
  | Number(x)-> Const(Sexpr(Number(x)))
  | Bool(x)-> Const(Sexpr(Bool(x)))
  | Char(x)-> Const(Sexpr(Char(x)))
  | String(x)-> Const(Sexpr(String(x)))
  | TaggedSexpr(x, Pair(Symbol("quote"), Pair(y,Nil))) -> Const(Sexpr(TaggedSexpr(x,y)))
  | TaggedSexpr(x,y)-> Const(Sexpr(TaggedSexpr(x,y)))
  | Symbol(x)-> if(not(List.mem x reserved_word_list)) then Var(x) else raise X_syntax_error
  | TagRef(x) -> Const(Sexpr (TagRef (x)))
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil)))->
      If(tag_parse test, tag_parse dit, Const(Void))
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil))))->
      If(tag_parse test, tag_parse dit, tag_parse dif)
  | Pair(Symbol("quote"), Pair(x,Nil))-> Const(Sexpr(x))
  | Pair(Symbol "quasiquote", Pair(expr, Nil)) -> tag_parse (make_quasiquote expr)
  | Pair(Symbol("lambda"), Pair(Symbol optargs, body))->LambdaOpt([], optargs, (tag_parse (Pair(Symbol "begin", body))))
  | Pair(Symbol("lambda"), Pair(args, body))->if (is_improper_list args) 
      then LambdaOpt((cut_opt args), (take_last args), (tag_parse(Pair(Symbol "begin", body))))
      else LambdaSimple((args_to_list args), (tag_parse(Pair(Symbol "begin", body))))
  | Pair(Symbol "begin", Nil) -> Const(Void)
  | Pair(Symbol "begin", Pair(x,Nil)) -> (tag_parse x)
  | Pair(Symbol "begin", Pair(x,y)) -> Seq((beginExp (Pair(x,y))))
  | Pair(Symbol "or", body) -> (make_or body)
  | Pair(Symbol "define", Pair(Pair(name, argl), expr)) -> Def((tag_parse name), (tag_parse (Pair(Symbol "lambda", Pair(argl, expr)))))
  | Pair(Symbol "define", Pair(name, Pair(expr, Nil))) -> Def((tag_parse name),(tag_parse expr))
  | Pair(Symbol "set!", Pair(name, Pair(setValue, Nil))) -> Set((tag_parse name),(tag_parse setValue))
  | Pair(Symbol "let", Pair(varsvals, body)) -> Applic((tag_parse (make_lambda varsvals body)),(beginExp (get_vals varsvals)))
  | Pair(Symbol "let*", Pair(varsvals, body)) -> (make_kleenlet varsvals body)
  | Pair(Symbol "letrec", Pair(varsvals, body)) -> (tag_parse (make_letrec varsvals body))
  | Pair(Symbol "and", body) -> if (body = Nil) then Const(Sexpr(Bool(true))) else (tag_parse (make_and body))
  | Pair(Symbol "cond", body) -> tag_parse (make_cond body)
  | Pair (op, body) -> Applic(tag_parse op, beginExp body) 
  | _ -> raise X_syntax_error

and make_or body = 
match body with
  | Nil -> Const(Sexpr(Bool(false)))
  | Pair(x, Nil) -> (tag_parse x)
  | Pair(x,y) -> Or(beginExp body)
  | _ -> raise X_syntax_error

and make_cond body = 
match body with
  | Pair(Pair(Symbol "else", expr), Nil) -> Pair(Symbol "begin", expr)
  | Pair(Pair(test, Pair(Symbol "=>", expr)), Nil) -> Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, expr)), Nil)), Nil)), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))), Nil))) 
  | Pair(Pair(test, Pair(Symbol "=>", expr)), rest) -> Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(test, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, expr)), Nil)), Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair((make_cond rest), Nil))), Nil)), Nil))), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil)))
  | Pair(Pair(test, Nil), Nil) -> test
  | Pair(Pair(test, expr), Nil) -> Pair(Symbol "if", Pair(test, Pair(Pair(Symbol "begin", expr), Nil)))
  | Pair(Pair(test, expr), rest) -> Pair(Symbol "if", Pair(test, Pair(Pair((Symbol "begin"), expr), Pair((make_cond rest), Nil))))
  | _ -> raise X_syntax_error

and make_quasiquote expr = 
match expr with
  | Pair(Symbol "unquote", Pair(sexpr, Nil)) -> sexpr
  | Pair(Symbol "unquote-splicing", Pair(sexpr, Nil)) -> raise X_syntax_error
  | Symbol x -> Pair (Symbol "quote", Pair(Symbol x, Nil))
  | Nil -> Pair (Symbol "quote", Pair(Nil, Nil))
  | Pair(Pair(Symbol "unquote-splicing", Pair(sexpr, Nil)), y) -> Pair(Symbol "append", Pair(sexpr, Pair((make_quasiquote y), Nil)))
  | Pair(x, Pair(Symbol "unquote-splicing", Pair(sexpr, Nil))) -> Pair(Symbol "cons", Pair((make_quasiquote x), Pair(sexpr, Nil)))
  | Pair(x, y) -> make_cons (make_quasiquote x) (make_quasiquote y) 
  | _ -> Pair(Symbol("quote"), Pair(expr,Nil))

and make_cons x y = Pair(Symbol "cons", Pair(x, Pair(y, Nil)))

and make_and body = 
  match body with
  | Pair(x,Nil) -> x
  | Pair(x,rest) -> Pair(Symbol "if", Pair(x, Pair((make_and rest), Pair(Bool(false), Nil))))
  | _ -> raise X_syntax_error

and make_letrec varsvals body = 
  let vars = (getvars_letrec varsvals) in
  let body = (getbody_letrec varsvals body) in
  Pair(Symbol "let", Pair(vars,body))

and getvars_letrec varsvals = 
  match varsvals with 
  | Nil -> Nil
  | Pair(Symbol(x),Nil)-> Pair(Symbol(x),Symbol("whatever"))
  | Pair(Pair(Symbol(x),Pair(y, Nil)), Nil) -> Pair(Pair(Symbol(x),Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), Nil)
  | Pair(Pair(Symbol(x),Pair(y, Nil)), rest) -> Pair(Pair(Symbol(x),Pair(Pair(Symbol "quote", Pair(Symbol "whatever", Nil)), Nil)), getvars_letrec rest)
  | _ -> raise X_syntax_error

and getbody_letrec varsvals body = 
  match varsvals with
  | Nil -> Nil
  | Pair(Pair(x,Pair(y, Nil)), Nil) -> Pair(Pair(Symbol "set!", Pair(x, Pair(y, Nil))),body)
  | Pair(Pair(x,Pair(y,Nil)), rest) -> Pair(Pair(Symbol "set!", Pair(x, Pair(y, Nil))), (getbody_letrec rest body))
  | _ -> raise X_syntax_error


and make_kleenlet varsvals body = 
  match varsvals with
  | Nil -> Applic((tag_parse (make_lambda varsvals body)),(beginExp (get_vals varsvals)))
  | Pair(Pair(Symbol(x),Pair(y, Nil)), Nil)-> Applic((tag_parse (make_lambda varsvals body)),(beginExp (get_vals varsvals)))
  | Pair(Pair(Symbol(x),Pair(y, Nil)), rest) -> Seq([Applic((tag_parse (make_lambda (Pair(Symbol(x),Nil)) Nil)),(beginExp (Pair(y,Nil))));(make_kleenlet rest body)])
  | _ -> raise X_syntax_error

and beginExp pair = 
  match pair with
  | Nil -> []
  | Pair(x, Pair(y,z)) -> (tag_parse x)::(beginExp (Pair(y,z)))
  | Pair(y,Nil) -> [(tag_parse y)]
  | Pair(x,y) -> [(tag_parse x);(tag_parse y)]
  | _ -> raise X_syntax_error


and make_lambda varsvals body = 
  let vars = (get_vars varsvals) in
  Pair(Symbol "lambda", Pair(vars, body))


and get_vars varsvals = 
 match varsvals with
  | Nil -> Nil
  | Pair(Symbol(x),Nil)-> Pair(Symbol(x),Nil)
  | Pair(Pair(Symbol(x),Pair(y, Nil)), Nil) -> Pair(Symbol(x), Nil)
  | Pair(Pair(Symbol(x),Pair(y, Nil)), rest) -> Pair((Symbol(x),(get_vars rest)))
  | _ -> raise X_syntax_error

and get_vals varsvals = 
  match varsvals with
   | Nil -> Nil
   | Pair(Pair(Symbol(x),Pair(y, Nil)), Nil) -> Pair(y, Nil)
   | Pair(Pair(Symbol(x),Pair(y, Nil)), rest) -> Pair(y, (get_vals rest))
   | _ -> raise  X_syntax_error

and is_improper_list list =
  match list with
  | Nil -> false
  | Pair(x,Nil) -> false
  | Pair(x, Pair(y,z)) -> is_improper_list z
  | Pair(x, y) -> true
  | _ -> true

and args_to_list args = match args with 
  | Nil -> []
  | Pair(Symbol(x),rest) -> (x::(args_to_list rest))
  | Symbol(x) -> [x]
  | _ -> raise X_syntax_error


and cut_opt args = match args with  
  | Nil -> []   
  | Pair(Symbol(x),rest) -> (x::(cut_opt rest))
  | Symbol(x) -> [] 
  | _ -> raise X_syntax_error
  

and take_last g =  match g with  
 | Pair(Symbol(x),rest) -> (take_last rest)
 | Nil -> ""
 | Symbol(x) -> x
 | _ -> raise X_syntax_error;;



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
	


module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; 

module Tag_Parser : TAG_PARSER = struct


let tag_parse_expression sexpr = tag_parse sexpr;;
let tag_parse_expressions sexpr = (List.map tag_parse sexpr);;



end;; 
