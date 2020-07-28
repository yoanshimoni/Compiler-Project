#use "tag-parser.ml";;


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

let rec is_param x params minor =
  match params with
  | [] -> -1
  | (s::rest) -> if (s = x) then minor else (is_param x rest (minor + 1));;

let rec sub_expr expr env = 
match expr with
  | Const(x) -> Const'(x) 
  | Var(x) -> (make_var x env 0) 
  | If(x,y,z) -> If'((sub_expr x env),(sub_expr y env),(sub_expr z env)) 
  | Seq(exprs) -> Seq'(List.map (fun x -> (sub_expr x env)) exprs)
  | Set (exp1,exp2) -> Set'((sub_expr exp1 env),(sub_expr exp2 env))
  | Def (exp1,exp2) -> Def'((sub_expr exp1 env),(sub_expr exp2 env))
  | Or(exprs) -> Or'(List.map (fun x -> (sub_expr x env)) exprs)
  | LambdaSimple (params,exp1) -> (make_lambdasimple params exp1 env)
  | LambdaOpt (params,str,exp1) ->  (make_lambdaopt params str exp1 env)
  | Applic(exp, exprs) -> Applic'((sub_expr exp env), (List.map (fun x -> (sub_expr x env)) exprs))


and make_lambdasimple params exp1 env = 
  let newEnv = params :: env in 
  let newExp = (sub_expr exp1 newEnv) in
  LambdaSimple'(params, newExp)

and make_lambdaopt params str exp1 env = 
  let newEnv = (List.append params [str]) :: env in 
  let newExp = (sub_expr exp1 newEnv) in
  LambdaOpt'(params, str, newExp)



and make_var x env major= 
  match env with
    | [] -> Var' (VarFree (x))
    | env0::rest -> let res = (is_param x env0 0) in
                    if (res = (-1)) then (make_var x rest (major+1))
                    else if (major=0) then Var'(VarParam(x, res))
                         else Var'(VarBound(x, (major-1), res))



let rec ann_tail_expr exp b = 
  match exp with 
    | Const'(x) -> Const'(x)
    | If'(x,y,z) ->  If'((ann_tail_expr x false), (ann_tail_expr y b), (ann_tail_expr z b))
    | Var'(str) -> Var'(str)
    | Set'(exp1,exp2) -> Set' ((ann_tail_expr exp1 false) ,(ann_tail_expr exp2 false))  
    | Def'(exp1,exp2) -> Def' ((ann_tail_expr exp1 false) ,(ann_tail_expr exp2 false))  
    | Seq'(exps) -> Seq'(make_seq exps b)  
    | Or'(exps) -> Or'(make_seq exps b)
    | LambdaSimple'(lst,exp1) -> LambdaSimple' (lst, (ann_tail_expr exp1 true))
    | LambdaOpt'(lst,str,exp1) -> LambdaOpt' (lst, str, (ann_tail_expr exp1 true))
    | Applic'(exp1,exps) -> (make_applic exp1 exps b)  
    | ApplicTP'(exp1, exps) -> ApplicTP'(exp1, exps)   
    | Box'(exp) -> Box'(exp)
    | BoxGet'(exp) -> BoxGet'(exp)
    | BoxSet'(var1, exp) -> BoxSet'(var1, exp)       

and make_seq exps b = 
  match b with
    | true -> 
      let list_no_last = List.rev (List.tl (List.rev exps)) in
      let list_no_last = (List.map (fun x -> (ann_tail_expr x false)) list_no_last) in
      let last_exp =  List.hd (List.rev exps) in
      let last_exp = [(ann_tail_expr last_exp true)] in
      (List.append list_no_last last_exp)
    | false -> (List.map (fun x -> (ann_tail_expr x false)) exps)

and make_applic exp1 exps b = 
  match b with
  | true -> ApplicTP'((ann_tail_expr exp1 false), (List.map (fun x -> (ann_tail_expr x false)) exps))
  | false -> Applic'((ann_tail_expr exp1 b), (List.map (fun x -> (ann_tail_expr x b)) exps));;


let rec boxing_set expr = 
  match expr with
  | Const'(x) -> Const'(x)
  | If'(_test,_then,_else) ->  If'((boxing_set _test), (boxing_set _then), (boxing_set _else))
  | Var'(str) -> Var'(str)
  | Set'(exp1,exp2) -> Set'(exp1, (boxing_set exp2))
  | Def'(exp1,exp2) -> Def'(exp1, (boxing_set exp2 )) 
  | Seq'(exps) -> Seq'(List.map (fun x -> (boxing_set x)) exps)
  | Or'(lst) ->  Or'(List.map (fun x -> (boxing_set x )) lst)
  | LambdaSimple'(params,exp) -> if (List.length params=0) then LambdaSimple'(params, (boxing_set exp))
                                 else LambdaSimple'(params, boxing_set (boxLambda params exp))
  | LambdaOpt'(params,str,exp) -> if ((List.length (List.append params [str]))<1) then LambdaOpt'(params, str, (boxing_set exp))
                                  else LambdaOpt'(params, str, boxing_set (boxLambda (List.append params [str]) exp))
  | Applic'(exp1,exps) ->  Applic'((boxing_set exp1), (List.map (fun x -> (boxing_set x)) exps)) 
  | ApplicTP'(exp1,exps) ->  ApplicTP'((boxing_set exp1), (List.map (fun x -> (boxing_set x)) exps)) 
  | BoxSet'(var, set) -> BoxSet'(var, (boxing_set set))
  | BoxGet'(var) -> expr 
  | Box'(var) -> expr

and getcount = ref 0 
and setcount = ref 0 

and boxLambda params expr = 
  let tmpBody = ref expr in
  let tmpList = ref [] in
  let boxcounter = ref 0 in
  for i = (List.length params)-1  downto 0 do
    getcount := 0;
    setcount := 0;
    let var = (List.nth params i) in
    let get_Var = (getVar var expr [0] 0) in
    let set_Var = (setVar var expr [0] 0) in
    let need_box = (comp_rw get_Var set_Var) in
    if (need_box) then (
      tmpList := (List.append [Set'(Var' (VarParam (var, i)), Box' (VarParam (var, i)))] !tmpList);
      tmpBody := (replaceBody var !tmpBody);
      boxcounter := !boxcounter+1
      )
  done;
  if(!boxcounter>0) then Seq' (List.append !tmpList [!tmpBody]) else !tmpBody


and replaceBody var body = 
  match body with
    | Const'(x) -> Const'(x)
    | If'(_test,_then,_else) ->  If'((replaceBody var _test), (replaceBody var _then), (replaceBody var _else))
    | Seq'(exps) -> Seq'(List.map (fun x -> (replaceBody var x)) exps)
    | Or'(exps) ->  Or'(List.map (fun x -> (replaceBody var x)) exps)
    | Var'(VarFree(str)) -> body
    | Var'(VarParam(str,min)) -> (if(String.equal str var) then (BoxGet'(VarParam(str,min))) else body)
    | Var'(VarBound(str,maj,min)) -> (if (String.equal str var) then (BoxGet'(VarBound(str,maj,min))) else body)
    | Def'(exp1,exp2) -> Def' (exp1 ,(replaceBody var exp2 ))  
    | LambdaSimple'(lst,expr) -> (if (List.exists (fun x -> String.equal var x) lst) 
                                  then body
                                  else LambdaSimple'(lst,(replaceBody var expr)))
    | LambdaOpt'(lst,opt,expr) -> (if (List.exists (fun x -> String.equal var x) (List.cons opt lst)) 
                                  then body
                                  else LambdaOpt'(lst,opt,(replaceBody var expr)))
    | Applic'(exp1,exps) ->  Applic'((replaceBody var exp1), (List.map (fun x -> (replaceBody var x)) exps)) 
    | ApplicTP'(exp1,exps) ->  ApplicTP'((replaceBody var exp1), (List.map (fun x -> (replaceBody var x)) exps)) 
    | BoxSet'(_var, set) -> BoxSet'(_var, (replaceBody var set))
    | BoxGet'(_var) -> body
    | Box'(_var) -> body 
    | Set'(exp1,exp2) -> 
        match exp1 with 
        | Var'(VarFree(str)) -> Set'(exp1,(replaceBody var exp2))
        | Var'(VarParam(str,min)) -> (if (String.equal str var) then (BoxSet'(VarParam(str,min),(replaceBody var exp2))) else Set'(exp1,(replaceBody var exp2)))
        | Var'(VarBound(str,maj,min)) -> (if (String.equal str var) then (BoxSet'(VarBound(str,maj,min), (replaceBody var exp2))) else Set'(exp1,(replaceBody var exp2)))
        | _ -> raise X_syntax_error

and comp_rw getvar setvar =
  match getvar with
  | [] -> false
  | v::t -> if((comp_w v setvar)) then true else (comp_rw t setvar)

and comp_w v1 setvar =
  match setvar with
    | [] -> false
    | v2::t ->   
                   if ((List.hd (List.rev v1))==(List.hd (List.rev v2))) then (comp_w v1 t)
                   else if (List.length v1<2 || List.length v2<2) then true
                   else if ((List.nth v1 1)==(List.nth v2 1)) then (comp_w v1 t)
                   else true
    


  
  
  

and getVar var expr array count = 
  match expr with
    | Const'(x) -> []
    | If'(_test,_then,_else) -> (List.append(getVar var _test array count)(List.append (getVar var _then array count)(getVar var _else array count)))
    | Var'(VarFree(str)) -> []
    | Var'(VarParam(str,_)) -> (if (String.equal str var) then [array] else [])
    | Var'(VarBound(str,_,_)) -> (if (String.equal str var) then [array] else []) 
    | Set'(exp1,exp2) -> (getVar var exp2 array count)
    | Def'(exp1,exp2) -> (getVar var exp2 array count)
    | Seq'(exps) -> (List.fold_left (fun x y -> (List.append x y)) [] (List.map (fun y -> (getVar var y array count)) exps))
    | Or'(exps) -> (List.fold_left (fun x y -> (List.append x y)) [] (List.map (fun y -> (getVar var y array count)) exps))
    | LambdaSimple'(params,expr) -> (if (List.exists (fun x -> String.equal var x) params) then []
                                  else (
                                    (getcount := !getcount+1);
                                     (getVar var expr (List.append array [!getcount]) !getcount)))
    | LambdaOpt'(params,str,expr) -> (if (List.exists (fun x -> String.equal var x) params) then []
                                  else (
                                    (getcount := !getcount+1); 
                                     (getVar var expr (List.append array [!getcount]) !getcount)))
    | Applic'(exp1,exps) -> (List.fold_left (fun x y -> (List.append x y)) [] (List.map (fun y -> (getVar var y array count)) (List.cons exp1 exps)))
    | ApplicTP'(exp1,exps) -> (List.fold_left (fun x y -> (List.append x y)) [] (List.map (fun y -> (getVar var y array count)) (List.cons exp1 exps)))
    | BoxSet'(_var, set) -> (getVar var set array count)
    | BoxGet'(_var) -> []
    | Box'(_var) -> []


and setVar var expr array count = 
  match expr with
    | Const'(x) -> []
    | If'(_test,_then,_else) -> (List.append(setVar var _test array count) (List.append (setVar var _then array count)(setVar var _else array count)))
    | Var'(VarFree(str)) -> []
    | Var'(VarParam(str,_)) -> []
    | Var'(VarBound(str,_,_)) -> [] 
    | Set'(exp1,exp2) -> (set_expr_var exp1 exp2 var expr array count)
    | Def'(exp1,exp2) -> (setVar var exp2 array count)
    | Seq'(exps) -> (List.fold_left (fun x y -> (List.append x y)) [] (List.map (fun y -> (setVar var y array count)) exps))
    | Or'(exps) -> (List.fold_left (fun x y -> (List.append x y)) [] (List.map (fun y -> (setVar var y array count)) exps))
    | LambdaSimple'(params,expr) -> (if (List.exists (fun x -> String.equal var x) params) then []
                                  else (
                                    (setcount := !setcount+1);
                                     (setVar var expr (List.append array [!setcount]) !setcount)))
    | LambdaOpt'(params,str,expr) -> (if (List.exists (fun x -> String.equal var x) params) then []
                                  else (
                                    (setcount := !setcount+1); 
                                     (setVar var expr (List.append array [!setcount]) !setcount)))
    | Applic'(exp1,exps) -> (List.fold_left (fun x y -> (List.append x y)) [] (List.map (fun y -> (setVar var y array count)) (List.cons exp1 exps)))
    | ApplicTP'(exp1,exps) -> (List.fold_left (fun x y -> (List.append x y)) [] (List.map (fun y -> (setVar var y array count)) (List.cons exp1 exps)))
    | BoxSet'(_var, set) -> (setVar var set array count)
    | BoxGet'(_var) -> []
    | Box'(_var) -> []

and set_expr_var exp1 exp2 var expr array count= 
  match exp1 with
    | Var'(VarFree(str)) -> 
    (setVar var exp2 array count)
    | Var'(VarParam(str,_)) -> 
    (if (String.equal str var) 
    then (List.append [array] (setVar var exp2 array count)) 
    else (setVar var exp2 array count))
    | Var'(VarBound(str,_,_)) -> 
    (if (String.equal str var) 
    then (List.append [array] (setVar var exp2 array count)) 
    else (setVar var exp2 array count))
    | _ -> raise X_syntax_error

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

let annotate_lexical_addresses e =  
  let env = [] in
  let exp_lex = (sub_expr e env) in
  exp_lex;;

let annotate_tail_calls e =  ann_tail_expr e false;;

let box_set e = boxing_set e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)
