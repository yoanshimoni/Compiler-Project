
 #use "semantic-analyser.ml";;

let make_string str =
    let chars_asci = List.map (fun (x) -> string_of_int (Char.code x)) str in
    String.concat "," chars_asci;;      

let rec make_const_table expr basictable addr = 
 match expr with
  | [] -> basictable
  | s::rest -> let const = (const_table s basictable addr) in 
               (make_const_table rest (List.append basictable const) addr)

and const_table expr basictable addr = 
  match expr with
    | Const'(x) -> (match x with
                    | Void -> []
                    | Sexpr(y) -> if (const_exist y basictable) then [] 
                                  else (make_const_expr x basictable addr))
    | If'(x,y,z) -> let a = (const_table x basictable addr) in 
                    let b = (const_table y (basictable @ a) addr) in 
                    let c = (const_table z (basictable @ a @ b) addr) in
                      (a @ b @ c) 
    | Applic'(x,lst) -> let a = (const_table x basictable addr) in
                        let b = List.fold_left (fun acc exp -> acc @ (const_table exp (basictable @ acc) addr)) a lst in
                        b
    | ApplicTP'(x,lst) -> let a = (const_table x basictable addr) in
                          let b = List.fold_left (fun acc exp -> acc @ (const_table exp (basictable @ acc) addr)) a lst in
                          b                   
    | Var'(str) -> []
    | Set'(x,y) -> (const_table y basictable addr)
    | Def'(x,y) -> let a = (const_table x basictable addr) in
                  let b = (const_table y (basictable @ a) addr) in
                  (a @ b)
    | Seq'(lst) -> (List.fold_left (fun acc exp -> acc @ (const_table exp (basictable @ acc) addr)) [] lst) 
    | Or'(lst) ->  (List.fold_left (fun acc exp -> acc @ (const_table exp (basictable @ acc) addr)) [] lst)               
    | LambdaSimple'(lst,x) -> (const_table x basictable addr)
    | LambdaOpt'(lst,str,x) -> (const_table x basictable addr) 
    | BoxSet'(var, set) -> (const_table set basictable addr)
    | BoxGet'(var) -> []
    | Box'(var) -> []                            


and const_exist x basictable = 
  match basictable with
  | [] -> false
  | ((s,(_,_))::rest) -> (match s with
                 | Void -> (const_exist x rest)
                 | Sexpr(y) -> if (sexpr_eq x y) then true else (const_exist x rest))
       

and const_address x basictable = 
match basictable with
  | [] -> raise X_this_should_not_happen
  | ((s,(index,_))::rest) -> (match s with
                         | Sexpr(y) -> if (sexpr_eq x y) then index else (const_address x rest)
                         | Void -> (const_address x rest))
                         

and make_const_expr expr basictable addr = 
  match expr with
  | Void -> [] 
  | Sexpr(x) -> 
                begin match x with
                | Bool(b) -> []
                | Nil -> []
                | Char(c) -> addr := !addr+2;
                             [(expr, (!addr - 2, Printf.sprintf "MAKE_LITERAL_CHAR (%d)" (Char.code c)))]
                | Number(Float(num)) ->  addr := !addr + 9 ; 
                                         [(expr,(!addr - 9, Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" num))]
                | Number(Int(num)) -> addr := !addr + 9 ; 
                                        [(expr, (!addr - 9, Printf.sprintf "MAKE_LITERAL_INT(%d)" num))] 
                | String(str) -> let newStr = (make_string (string_to_list str)) in
                                    addr := !addr + 9 + (String.length str); 
                                   [(expr, (!addr - 9 - (String.length str) , (Printf.sprintf "MAKE_LITERAL_STRING %d\ndb " (String.length str)) ^ newStr ))]                   
                | Symbol(str) -> let strexpr = (const_table (Const'(Sexpr(String(str)))) basictable addr) in
                                 let straddr = (match strexpr with 
                                               | [] -> (const_address (String(str)) basictable)  
                                               | (_,(index,_))::rest -> index) in
                                 addr := !addr + 9 ;
                                 strexpr @ [(expr, (!addr - 9, Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl + %d)" straddr))]
                | Pair(a,b) -> let sexpr1 = (const_table (Const'(Sexpr(b))) basictable addr) in          
                               let sexpr2 = (const_table (Const'(Sexpr(a))) (basictable@sexpr1) addr) in
                               addr := !addr + 17;
                               sexpr1 @ sexpr2 @ [(expr, (!addr - 17, Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl + %d,const_tbl + %d)" 
                                          (const_address a (basictable @ sexpr1 @ sexpr2)) (const_address b (basictable @ sexpr1 @ sexpr2))))]
                | TaggedSexpr (str, sexpr)-> []
                | TagRef (str) -> []
                end





let consts_tbl expr = 
   let addr = ref 6 in
   let basictable = 
          [(Void, (0, "MAKE_VOID"));
          (Sexpr(Nil), (1, "MAKE_NIL"));
          (Sexpr(Bool false), (2, "MAKE_BOOL(0)"));
          (Sexpr(Bool true), (4, "MAKE_BOOL(1)"))] in
  (make_const_table expr basictable addr);;




let rec vars_table expr basictable addr = 
 match expr with
  | [] -> basictable
  | s::rest -> let var = (make_vars_expr s basictable addr) in 
               (vars_table rest (List.append basictable var) addr)

and make_vars_expr expr basictable addr = 
  match expr with 
    | Const'(x) -> []
    | If'(x,y,z) -> let a = (make_vars_expr x basictable addr) in 
                       let b = (make_vars_expr y (basictable @ a) addr) in 
                       let c = (make_vars_expr z (basictable @ a @ b) addr) in
                       (a @ b @ c) 
    | Applic'(x,lst) -> let a = (make_vars_expr x basictable addr) in
                        let b = List.fold_left (fun acc exp -> acc @ (make_vars_expr exp (basictable @ acc) addr)) a lst in
                        b
    | ApplicTP'(x,lst) -> let a = (make_vars_expr x basictable addr) in
                          let b = List.fold_left (fun acc exp -> acc @ (make_vars_expr exp (basictable @ acc) addr)) a lst in
                          b                   
    | Var'(str) -> (make_var str basictable addr)
    | Set'(x,y) -> (make_vars_expr y basictable addr)
    | Def'(x,y) -> let a = (make_vars_expr x basictable addr) in
                   let b = (make_vars_expr y (basictable @ a) addr) in
                   (a @ b)
    | Seq'(lst) -> (List.fold_left (fun acc exp -> acc @ (make_vars_expr exp (basictable @ acc) addr)) [] lst) 
    | Or'(lst) ->  (List.fold_left (fun acc exp -> acc @ (make_vars_expr exp (basictable @ acc) addr)) [] lst)               
    | LambdaSimple'(lst,x) -> (make_vars_expr x basictable addr)
    | LambdaOpt'(lst,str,x) -> (make_vars_expr x basictable addr)
    | BoxSet'(var, set) -> (make_vars_expr set basictable addr)
    | BoxGet'(var) -> []
    | Box'(var) -> []

and make_var exp basictable addr = 
match exp with 
    | VarFree(x) -> (if(var_exist x basictable)
                      then []
                    else ((addr := !addr + 1); [(x, !addr-1)] ))
    | _ -> []


and var_exist x basictable = 
  match basictable with
  | [] -> false
  | (s::rest) -> match s with
                 | (var,address) -> (if (String.equal var x) then true
                                     else (var_exist x rest))
           

and fvar_address x fvartable = 
match fvartable with
  | [] -> raise X_this_should_not_happen
  | (v,index)::rest -> if (String.equal v x) then index
                       else (fvar_address x rest)
                        


let make_vars_tbl expr = 
  let addr = ref 29 in
  let basictable = ["boolean?",0; "float?",1; "integer?",2; "pair?",3;
   "null?",4; "char?",5; "string?",6;
   "procedure?",7; "symbol?",8; "string-length",9;
   "string-ref",10; "string-set!",11; "make-string",12;
   "symbol->string",13; 
   "char->integer",14; "integer->char",15; "eq?",16;
   "+", 17; "*",18; "-",19; "/",20; "<",21; "=",22;
   "car", 23; "cdr",24; "set-car!",25;"set-cdr!",26; "cons",27;"apply",28] in
   (vars_table expr basictable addr);;

let counter = ref 0;;

  let rec make_generator consttbl freetbl exp counter depth = 
  match exp with
    | Const'(x) -> let address = (match x with 
                    | Void -> 0
                    | Sexpr(y) -> (const_address y consttbl)) in
                   Printf.sprintf "mov rax,const_tbl + %d\n" address
    | Var'(VarParam(_,minor)) -> let rbp_min = minor+4 in (Printf.sprintf "mov rax, qword [rbp + 8*%d]\n" rbp_min)
    | Var'(VarBound(_, major, minor)) -> (Printf.sprintf "mov rax, qword [rbp + 8 * 2]\n") ^
                                         (Printf.sprintf  "mov rax, qword [rax + 8 * %d]\n" major) ^
                                         (Printf.sprintf  "mov rax, qword [rax + 8 * %d]\n" minor)
    | Var'(VarFree(v)) -> Printf.sprintf "mov rax, qword [fvar_tbl + 8 * %d]\n" (fvar_address v freetbl) 
    | Set'(Var'(VarParam(_, minor)),e) -> (make_generator consttbl freetbl e counter depth) ^
                                          (Printf.sprintf "mov qword [rbp + 8 * (4 + %d)], rax\n
                                                          mov rax, SOB_VOID_ADDRESS\n") minor
    | Set'(Var'(VarBound(_,major,minor)),e) -> (make_generator consttbl freetbl e counter depth) ^
                                                Printf.sprintf "mov rbx, qword [rbp + 8 * 2]\n" ^                   
                                                Printf.sprintf "mov rbx, qword [rbx + 8 * %d]\n" major ^
                                                Printf.sprintf "mov qword [rbx + 8 * %d], rax\n" minor ^
                                                Printf.sprintf "mov rax, SOB_VOID_ADDRESS\n"
    | Set'(Var'(VarFree(v)),e) -> (make_generator consttbl freetbl e counter depth) ^
                                  Printf.sprintf "mov qword [fvar_tbl + 8 * %d], rax\n" (fvar_address v freetbl) ^
                                  Printf.sprintf "mov rax, SOB_VOID_ADDRESS\n"
    | Seq'(lst) -> List.fold_left (fun a b -> a ^ b) "" (List.map (fun (x) -> (make_generator consttbl freetbl x counter depth)) lst)    
    | Or'(lst) -> let count_num = !counter in
                  counter := !counter + 1; 
                  (make_or consttbl freetbl lst counter count_num depth)
    | If'(te,th,el) ->  let count_num = !counter in
                        counter := !counter + 1;
                        (make_generator consttbl freetbl te counter depth) ^                                       
                        (Printf.sprintf "cmp rax, SOB_FALSE_ADDRESS\n  je Lelse%d\n" count_num) ^
                        (make_generator consttbl freetbl th counter depth) ^
                        (Printf.sprintf "jmp Lexit%d\n" count_num) ^
                        (Printf.sprintf "Lelse%d:\n" count_num) ^
                        (make_generator consttbl freetbl el counter depth) ^
                        (Printf.sprintf "Lexit%d:\n" count_num)
    | Box'(v) -> (make_generator consttbl freetbl (Var'(v)) counter depth) ^
                 (Printf.sprintf "mov rdx, rax\n") ^
                 (Printf.sprintf "MALLOC rax, WORD_SIZE\n") ^
                 (Printf.sprintf "mov qword [rax], rdx\n")
    | BoxGet'(v) -> (make_generator consttbl freetbl (Var'(v)) counter depth) ^
                    (Printf.sprintf "mov rax, qword [rax]\n")
    | BoxSet'(v,e) -> (make_generator consttbl freetbl e counter depth) ^
                      (Printf.sprintf "push rax\n") ^ 
                      (make_generator consttbl freetbl (Var'(v)) counter depth) ^
                      (Printf.sprintf "pop qword [rax]\n  mov rax, SOB_VOID_ADDRESS\n")
    | Def'(Var'(VarFree(v)), e) -> (make_generator consttbl freetbl e counter depth) ^ 
                                   (Printf.sprintf "mov qword [fvar_tbl + 8 * %d], rax\n" (fvar_address v freetbl)) ^
                                   (Printf.sprintf "mov rax, SOB_VOID_ADDRESS\n")
    | LambdaSimple'(args, body) -> let count_num = !counter in 
                                  counter := !counter+1; (make_lambda body consttbl freetbl counter count_num depth)
    | LambdaOpt'(lst, str, body) -> 
                                     (make_lambdaOpt body consttbl freetbl depth counter (List.length lst))  
    | Applic'(proc, args) ->   counter := !counter+1;
                              (make_applic proc args consttbl freetbl counter depth)
    | ApplicTP'(proc, args) ->  counter := !counter+1;
                              (make_applic proc args consttbl freetbl counter depth)
    | _ ->  raise X_this_should_not_happen

and make_applic proc args consttbl freetbl counter depth = 
  let rev_arglist = (List.rev args) in
  let generated_args = (List.map (fun(x) -> (make_generator consttbl freetbl x counter depth )) rev_arglist) in
  let generated_args = "push SOB_NIL_ADDRESS\n" ^ (String.concat "push rax\n" generated_args) ^ 
  "push rax\n" ^
  (Printf.sprintf "push %d\n" (List.length args)) ^
  (make_generator consttbl freetbl proc counter depth) ^
  "inc rax\n" ^
  "mov rbx, qword [rax]\n" ^
  "push rbx\n" ^ 
  "add rax, 8\n" ^
  "call [rax]\n" ^
  "add rsp , 8*1\n" ^ 
  "mov rbx, 0\n" ^
  "pop rbx\n" ^
  "add rbx ,1\n" ^
  "shl rbx , 3\n" ^
  "add rsp , rbx\n" in 
  generated_args

    
  and make_lambdaOpt body constTbl fvarTbl depth id argsLen =
    let myid = !id in
     id:=!id +1;
    (Printf.sprintf "MALLOC r8,%d\n" ((depth + 1) * 8)) ^
    (Printf.sprintf "mov r9, %d\n" depth) ^
    "cmp r9, 0\n" ^
    (Printf.sprintf "je emptyEnvCopy%d\n" myid) ^
    "mov rax, qword[rbp + 8 * 2]\n" ^
    "mov r12, 0\n" ^
    "mov r13, 1\n" ^
    (Printf.sprintf "loopOfCopyEnv%d:\n" myid) ^
    (Printf.sprintf "\tcmp r12, %d\n" depth) ^
    (Printf.sprintf "\tje endOfCopyEnv%d\n" myid) ^
    "mov r11, qword[rax + 8 * r12]\n"   ^
    "mov qword[r8 + 8 * r13], r11\n" ^
    "inc r12\n\tinc r13\n" ^
    (Printf.sprintf "\tjmp loopOfCopyEnv%d\n" myid) ^
    (Printf.sprintf "endOfCopyEnv%d:\n" myid) ^
    "mov r9, qword [rbp + 8 * 3]\n" ^
    "lea r11, [r9 * 8]\n"    ^
    "MALLOC r12, r11\n" ^
    "mov rcx, 0\n" ^
    (Printf.sprintf "loopOfCopyArgs%d:\n" myid) ^
    "cmp rcx, r9\n" ^
    (Printf.sprintf "\tje endOfCopyArgs%d\n" myid) ^
    "mov r10, rcx\n" ^
    "add r10, 4\n" ^
    "mov r11,qword[rbp + 8 * r10]\n" ^
    "mov qword[r12 + 8 * rcx], r11\n" ^
    "inc rcx\n" ^
    (Printf.sprintf "jmp loopOfCopyArgs%d\n" myid) ^
    (Printf.sprintf "endOfCopyArgs%d:\n" myid) ^
    "mov qword [r8], r12\n" ^
    (Printf.sprintf "emptyEnvCopy%d:\n" myid) ^
    (Printf.sprintf "MAKE_CLOSURE (rax, r8, Lcode%d)\n" myid) ^
    (Printf.sprintf "jmp Lcont%d\n" myid) ^
    (Printf.sprintf "Lcode%d:\n" myid) ^
    "push rbp\n" ^
    "mov rbp, rsp\n\t" ^

     "mov r8, qword[rbp + 8 * 3] ; \n" ^ 
     "mov rcx, r8\n ; n after applic" ^
     "add r8, 1; r8 <- n+1\n" ^
     (Printf.sprintf "mov r9, %d ; \n" argsLen) ^
     "add r9, 1;\n" ^
     (Printf.sprintf "StackFix%d:\n" myid) ^  
     "cmp rcx, r9\n" ^
     (Printf.sprintf "jl endStackFix%d\n" myid) ^
     
     "mov r10, PVAR(rcx)\n" ^
     "dec rcx\n" ^

     "mov r12, PVAR(rcx)\n" ^
     "MAKE_PAIR (rax, r12, r10)\n" ^
     "mov PVAR(rcx), rax\n" ^
  
     (Printf.sprintf "jmp StackFix%d\n" myid) ^  
     (Printf.sprintf "endStackFix%d:\n" myid) ^
    
     (make_generator constTbl fvarTbl body id (depth+1)) ^
    "leave\n ret\n" ^
    (Printf.sprintf "Lcont%d:\n" myid)
    
  

and make_lambda body consttbl freetbl counter count_num depth = 
   (Printf.sprintf "MALLOC r8,%d\n" ((depth + 1) * 8)) ^
   (Printf.sprintf "mov r9, %d\n" depth) ^
   (Printf.sprintf "cmp r9, 0\n") ^                               
   (Printf.sprintf "jg ExtEnv%d\n" count_num) ^ 
   (Printf.sprintf "Lboth%d:\n" count_num) ^     
   (Printf.sprintf "MAKE_CLOSURE (rax, r8, Lcode%d)\n" count_num) ^
   (Printf.sprintf "jmp Lcont%d\n" count_num) ^
   (Printf.sprintf "Lcode%d:\n" count_num) ^
   (Printf.sprintf "push rbp\n") ^
   (Printf.sprintf "mov rbp, rsp\n") ^
   (make_generator consttbl freetbl body counter (depth+1)) ^
   (Printf.sprintf "leave\n ret\n") ^
   (Printf.sprintf "jmp Lcont%d\n" count_num) ^
   (Printf.sprintf "ExtEnv%d:\n" count_num) ^    
   (Printf.sprintf "mov rax, qword [rbp + 8 * 2]\n") ^
   (Printf.sprintf "mov r12, %d\n" depth) ^
   (Printf.sprintf "mov r13, 1\n") ^
   "mov r15, 0\n" ^
   "mov r14, 1\n" ^
   (Printf.sprintf "CopyEnvs%d:\n" count_num) ^
   "mov r10, qword [rax+8*r15]\n" ^
   "mov qword [r8+8*r14], r10\n" ^
   "inc r15\n" ^
   "inc r14\n" ^
   (Printf.sprintf "cmp r15, %d\n" (depth+1)) ^
   (Printf.sprintf "jne CopyEnvs%d\n" count_num) ^
   "mov r14, qword [rbp + 8*3]\n" ^
   "inc r14\n" ^
   "shl r14, 3\n" ^
   "MALLOC r15, r14\n" ^
   "mov r14, 0\n" ^
   "mov r10, 0\n" ^
   "mov r11, qword [rbp + 8*3]\n" ^
   "inc r11\n" ^
   (Printf.sprintf "CopyArgs%d:\n" count_num) ^
   "mov r10, PVAR(r14)\n" ^
   "mov qword [r15+r14*8], r10\n" ^
   "inc r14\n" ^
   "cmp r14, r11\n" ^
   (Printf.sprintf "jne CopyArgs%d\n" count_num) ^
   "mov qword [r8], r15\n" ^
   (Printf.sprintf "jmp Lboth%d\n" count_num) ^
   (Printf.sprintf "Lcont%d:\n" count_num)


  

and make_or consttbl freetbl lst counter count_num depth = 
    match lst with
    | [] -> (Printf.sprintf "Lexit%d:\n" count_num)
    | e :: rest  -> ((make_generator consttbl freetbl e counter depth) ^  
                     (Printf.sprintf "cmp rax, SOB_FALSE_ADDRESS\njne Lexit%d\n" count_num) ^ 
                     (make_or consttbl freetbl rest counter count_num depth))




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
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

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

module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = (consts_tbl asts);;
  let make_fvars_tbl asts = (make_vars_tbl asts);;
  let generate consts fvars e = (make_generator consts fvars e counter 0);;
end;;

