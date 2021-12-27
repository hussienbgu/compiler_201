#use "semantic-analyser.ml";;

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
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;
(* 
| Const' of constant
| Var' of var
| Box' of var
| BoxGet' of var
| BoxSet' of var * expr'
| If' of expr' * expr' * expr'
| Seq' of expr' list
| Set' of var * expr'
| Def' of var * expr'
| Or' of expr' list
| LambdaSimple' of string list * expr'
| LambdaOpt' of string list * string * expr'
| Applic' of expr' * (expr' list)
| ApplicTP' of expr' * (expr' list);; *)
(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)
(* scan the ast and collect the sexprs in all const record , the result is a list of sexprs *)



let rec scan_ast asts = 
  match asts with 
    | Const'(Void) ->[]
    | Var'(v) -> []
    | BoxGet'(exp) -> []
    | Box'(exp) -> []
    | Const'(Sexpr(exp)) ->[exp]
    | BoxSet'(var,exp) -> scan_ast(exp)
    | Def'(var,exp) -> scan_ast(exp)
    | Set'(var,exp) -> scan_ast(exp) 
    | If'(tst,thn,els) -> scan_ast(tst)@scan_ast(thn)@scan_ast(els)
    | LambdaSimple'(paramtesrs,body) -> scan_ast(body)
    | LambdaOpt'(paramtesrs,opt,body)-> scan_ast(body)
    | Seq'(exps) -> List.fold_right (fun a b -> (List.append a b)) (List.map (fun x-> scan_ast x) exps) []
    | Or'(exps) ->  List.fold_right (fun a b -> (List.append a b)) (List.map (fun x-> scan_ast x) exps) []
    | Applic'(exp1,exp2) ->  (scan_ast exp1)@ List.fold_right (fun a b -> (List.append a b)) (List.map (fun x-> scan_ast x ) exp2 )[]
    | ApplicTP'(exp1,exp2) ->(scan_ast exp1)@ List.fold_right (fun a b -> (List.append a b)) (List.map (fun x-> scan_ast x ) exp2 )[]
    

(* convert the list of the sexprs into set (to remove duplicates) *)
  let append_uniq a b = if List.mem b a then a else b :: a ;;
   
  

(* expand the list to include all sub constants and
    convert the list after expanded into set *)
let rec expand_exp sexp = 
  match sexp with 
  | Symbol(e) -> [Sexpr(String(e))]@[Sexpr(Symbol(e))]
  | Pair(car,cdr) ->  (expand_exp car)@(expand_exp cdr)@[Sexpr((Pair(car,cdr)))]
  | e -> [Sexpr(e)] ;; 

let expand_sexprs_list lst = 
  let expanded = (List.map (fun exp -> expand_exp exp) lst) in
  let addition = List.append [[Void;Sexpr (Nil);Sexpr(Bool false);Sexpr(Bool true)]] expanded in 
  (List.rev (List.fold_left append_uniq [] (List.concat addition)));;

(*go over the list from first to last and create the constant table *)
let offset = ref 6 ;;
let increase_offset kind  =
  match kind with
   | "_char" -> offset := !offset + 2 ; !offset - 2
   | "_float" -> offset := !offset + 9;!offset - 9
   | "_fraction" -> offset :=!offset +17;!offset -17
   | "_pair" -> offset :=!offset +17;!offset -17
   | "_symbol" -> offset := !offset +9;!offset -9
   | str -> offset := !offset + 9 +  (String.length str) ; !offset -9 - (String.length str) ;;
   let rec get_adrress sexpr const_tbl = 
    match const_tbl with
      | [] -> 0
      | (Void,(_,_))::cdr -> get_adrress sexpr cdr
      | (Sexpr(e),(offset,s))::cdr -> if (e = sexpr) then offset else get_adrress sexpr cdr;;
    let convert_string_to_ascii s =    
        let length = String.length s in 
        match length with 
         | 0 -> "\"\""
         | _ -> let toascii =  List.map (Char.code) (string_to_list s) in
                String.concat ", " (List.map (Printf.sprintf "%d") toascii) ;;
    let rec check_exp exps const_tabl  =
      match exps with 
        | Void::con -> let f = const_tabl@[(Void, ((0, "MAKE_VOID\n")))] in
                               (check_exp con f)

        | Sexpr(Nil)::con -> let f = const_tabl@[
                        (Sexpr(Nil),
                        ((1,"MAKE_NIL\n")))] in
                        (check_exp con f)

        | Sexpr(Bool(false))::con -> let f = const_tabl@[
                                (Sexpr(Bool(false)),
                                ((2,Printf.sprintf "MAKE_LITERAL_BOOL(%d)\n" 0)))] in
                                (check_exp con f)

        | Sexpr(Bool(true))::con ->  let f = const_tabl@[
                                (Sexpr(Bool(true)),
                                ((4,Printf.sprintf "MAKE_LITERAL_BOOL(%d)\n" 1)))] in
                                (check_exp con f)

        | Sexpr(Number(Float(num)))::con -> let f = const_tabl@[
                                        (Sexpr(Number(Float(num))),
                                        ((increase_offset("_float"),Printf.sprintf "MAKE_LITERAL_FLOAT(%f)\n" num )))] in 
                                         (check_exp con f)

        | Sexpr(Number(Fraction(num1,num2)))::con -> let f = const_tabl@[
                                                  (Sexpr(Number(Fraction(num1,num2))),
                                                  ((increase_offset ("_fraction"),(Printf.sprintf "MAKE_LITERAL_RATIONAL(%d,%d)\n" (num1) (num2)))))] in 
                                                  (check_exp con f)
        
        | Sexpr(Char(s))::con -> let f =  const_tabl@[
                              (Sexpr(Char(s)), 
                              ((increase_offset("_char"),"MAKE_LITERAL_CHAR(" ^ (string_of_int (Char.code s)) ^ ")")))] in 
                              (check_exp con f)

        | Sexpr(String(s))::con -> let f =const_tabl@[
                              (Sexpr(String(s)),
                              ((increase_offset(s),"MAKE_LITERAL_STRING " ^ convert_string_to_ascii s ^ "\n")))] in 
                              (check_exp con f)
    
        | Sexpr(Symbol(s))::con -> let f = const_tabl@[
                              (Sexpr(Symbol(s)),
                              ((increase_offset("_symbol"), (Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl + %d)\n" (get_adrress ((String(s))) (const_tabl)) ))))] in
                               (check_exp con f)

        | Sexpr(Pair(car,cdr))::con -> let f = const_tabl@[
          (Sexpr(Pair(car,cdr)),
          ((increase_offset("_pair"),
          (Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d)\n" (get_adrress car const_tabl) (get_adrress ((cdr)) (const_tabl))))))] in
          (check_exp con f)
        | _ -> const_tabl ;;

let make_test exp = 
  let _scanned = List.concat (List.map (fun x -> scan_ast x) exp) in
  let _to_set = List.rev (List.fold_left append_uniq [] _scanned)   in 
  let _expanded = expand_sexprs_list _to_set in 
  check_exp _expanded [] ;;

(**********************************************************************************************************)
(**********************************************************************************************************)
(**********************************************************************************************************)

(* scan the ast and collect a list of strings that are the names of all the free variables 
 that occur in the ast of the user code *)
let rec scan_ast_var asts = 
    match asts with 
      | Const'(Void) ->[]
      | Var'(v) -> (match v with 
                    | VarFree(var) -> [var]
                    | _ -> [] )
      | BoxGet'(v) -> scan_ast_var(Var'(v))
      | Box'(v) -> scan_ast_var(Var'(v))
      | Const'(Sexpr(exp)) ->[]
      | BoxSet'(var,exp) -> scan_ast_var(Var'(var))@scan_ast_var(exp)
      | Def'(var,exp) -> scan_ast_var(Var'(var))@scan_ast_var(exp)
      | Set'(var,exp) -> scan_ast_var(Var'(var))@scan_ast_var(exp) 
      | If'(tst,thn,els) -> scan_ast_var(tst)@scan_ast_var(thn)@scan_ast_var(els)
      | LambdaSimple'(paramtesrs,body) -> scan_ast_var(body)
      | LambdaOpt'(paramtesrs,opt,body)-> scan_ast_var(body)
      | Seq'(exps) -> List.fold_right (fun a b -> (List.append a b)) (List.map (fun x-> scan_ast_var x) exps) []
      | Or'(exps) ->  List.fold_right (fun a b -> (List.append a b)) (List.map (fun x-> scan_ast_var x) exps) []
      | Applic'(exp1,exp2) ->  (scan_ast_var exp1)@ List.fold_right (fun a b -> (List.append a b)) (List.map (fun x-> scan_ast_var x ) exp2 )[]
      | ApplicTP'(exp1,exp2) ->(scan_ast_var exp1)@ List.fold_right (fun a b -> (List.append a b)) (List.map (fun x-> scan_ast_var x ) exp2 )[]

let primitive =
      [
        
        "boolean?"; "flonum?"; "rational?";
        "pair?"; "null?"; "char?"; "string?";
        "procedure?"; "symbol?";
        (* String procedures *)
        "string-length"; "string-ref"; "string-set!";
        "make-string"; "symbol->string";
        (* Type conversions *)
        "char->integer"; "integer->char"; "exact->inexact";
        (* Identity test *)
        "eq?";
        (* Arithmetic ops *)
         "+"; "*"; "/"; "="; "<"; 
        (* Additional rational numebr ops *)
        "numerator"; "denominator"; "gcd";
        "apply" ;"car";"cdr";"cons"; "set-car!";"set-cdr!";
        (* you can add yours here *)
        
      ]
(* create a list of pairs for each one in the list *)
 let rec make_pair_with_index list_of_names var_tabl count =
  match list_of_names with  
    | car::cdr -> let f = var_tabl@[(car,count)] in                  
                   (make_pair_with_index cdr f (count+8)) 
    | [] -> var_tabl ;;
    
  

let count_label = ref 0;;



let increase_count flag = 
match flag with
| true -> count_label:= !count_label + 1 ;!count_label 
| false -> !count_label ;;
let rec labelInFVarTable var var_table =
  match var_table with 
   | (varname,offset)::cdr -> if (String.equal varname  var) then offset else (labelInFVarTable var cdr)
   | [] -> 0 ;;

let rec addressInConstTable const const_table =
  match const_table with
   | (exp,(offset,assembly))::cdr ->  if (exp = const) then  offset else addressInConstTable const cdr
   | [] -> 0 ;;
  let rec gen const_table fvars_table e depth = 
    match e with 
      | Const'(exp) ->  "mov rax, const_tbl + " ^ string_of_int (addressInConstTable exp const_table) ^ "\n"
      | Var'(VarFree(v)) -> "mov rax, qword[fvar_tbl+" ^  string_of_int (labelInFVarTable v fvars_table) ^"]\n"
      | Var'(VarParam(_, minor)) -> Printf.sprintf "mov rax, qword[rbp + 8 * (4 + %s)]\n" (string_of_int minor)
      
      | Var'(VarBound(_, major, minor)) ->                 "mov rax, qword[rbp + 16]\n
                                                            mov rax, qword[rax + (8*" ^ string_of_int major ^ ")]\n" ^
                                                            "mov rax, qword[rax + (8*" ^ string_of_int minor ^ ")]\n" 
      
      | BoxGet'(v) ->  (gen const_table fvars_table (Var'(v)) depth) 
                             ^ "\n" ^ 
                             "mov rax,qword[rax]\n" 
      
       | BoxSet'(v,exp) ->  (gen const_table fvars_table exp depth) 
                        
                               ^  "\n"^ 
                                  "push rax\n" ^ 
                                  (gen const_table fvars_table (Var'(v)) depth) ^ "\n"
                                  ^"pop qword[rax]\n
                                  mov rax, SOB_VOID_ADDRESS\n"
      
      | Box'(VarParam(_,minor)) -> 
                                  
      "push rbx \nMALLOC rax , 8\n "
      ^ "mov rbx,  PVAR(" ^ (string_of_int minor) ^ ")\n 
      mov qword[rax],rbx\n 
      pop rbx\n" 
      

      | Set'((VarFree(v)),exp) -> (gen const_table fvars_table exp depth) 
                                           ^
                                          "\n" ^ 
                                           "mov qword [fvar_tbl+" ^ string_of_int (labelInFVarTable v fvars_table) ^"], rax\n"
                                          ^ "mov rax, SOB_VOID_ADDRESS\n" 
                                        
      | Set'((VarBound(_,major,minor)),exp) -> gen const_table fvars_table exp depth   
                                                ^ 
                                               "\n" ^  "mov rbx ,qword [rbp + (8*2)]\n
                                                                       mov rbx ,qword [rbx + (8*" ^ (string_of_int major) ^ ")]\n" ^
                                                                       "mov qword [rbx + (8*" ^ (string_of_int minor) ^ ")], rax\n
                                                                       mov rax ,SOB_VOID_ADDRESS\n"
      | Set'((VarParam(_, minor)),exp) ->  (gen const_table fvars_table exp depth)
                                                ^   
                                               "\n" ^
                                                   "mov qword [rbp + 8 * (4+" ^ (string_of_int minor) ^ ")], rax\n"
                                                    ^ "mov rax, SOB_VOID_ADDRESS\n" 
      | If'(tst,thn,els) -> let _id = string_of_int (increase_count true) in
                            let _test = (gen const_table fvars_table tst depth) in
                            let _then = (gen const_table fvars_table thn depth) in
                            let _else = (gen const_table fvars_table els depth) in 
                            _test^ "\n"^ 
                            "cmp rax, SOB_FALSE_ADDRESS" ^ "\n" ^ 
                            "je Lelse" ^ _id ^ "\n"
                            ^ _then^ "\n" ^ 
                            "jmp Lexit" ^ _id ^ "\n"
                            ^ "Lelse" ^ _id  ^ ":\n" ^
                            _else^ "\n"^ 
                            "Lexit" ^ _id ^ ":\n"

      | Or'(exps) ->
                      let without_last = List.rev (List.tl (List.rev exps)) in 
                      let exitid = (increase_count true) in 
                      let l = List.fold_left (fun acc e -> acc ^ gen const_table fvars_table e depth ^ "cmp rax, SOB_FALSE_ADDRESS\n" ^ "jne Lexit" ^ string_of_int (exitid) ^ "\n" ) "" without_last in 
                      let last = List.hd (List.rev exps) in 
                      let after_calc = (gen const_table fvars_table last depth) ^ 
                      "\n" 
                       ^ "Lexit" ^ string_of_int (exitid) ^ ":\n" in 
                      l ^ after_calc 
                      
            

      | Seq'(exps) -> List.fold_left (fun acc e -> acc ^ gen const_table fvars_table e depth) "" exps               
      | Def'((VarFree(v)),exp) ->   (gen const_table fvars_table exp depth) 
                             ^ 
                           "\n" ^  "mov qword [fvar_tbl +" ^ string_of_int (labelInFVarTable v fvars_table) ^ "], rax\n "
                                               ^   "mov rax, SOB_VOID_ADDRESS\n"
                                                  

      | LambdaSimple'(paramtesrs,body) -> 
        let _id = string_of_int (increase_count true) in
        
         Printf.sprintf "EXT_ENV %s\n  
                         mov rbx, rax\n
                         MAKE_CLOSURE(rax, rbx, Lcode%s)\n
                         jmp Lcont%s\n
                         Lcode%s:\n
                         push rbp\n
                         mov rbp, rsp\n " (string_of_int depth) _id  _id  _id   ^
                         gen const_table fvars_table body (depth+1) ^ 
                         Printf.sprintf "
                         \nleave\n
                         ret\n
                         Lcont%s:\n" _id 
        
      | Applic'(proc,args) -> 
        let num_of_args = string_of_int (List.length args) in
        let gen_args = List.fold_right (fun arg acc -> acc ^ (gen const_table fvars_table arg depth) ^ "\n" ^ "push rax\n") args ""in  
        gen_args ^ "\n" 
        ^"push " ^ num_of_args ^ "\n"^ 
          (gen const_table fvars_table proc depth) ^ "\n" ^
            "CLOSURE_ENV rbx,rax
             push rbx 
             CLOSURE_CODE rbx,rax
             call rbx
             add rsp ,8
             pop rbx      
             shl rbx, 3 
             add rsp, rbx\n"

      | ApplicTP'(proc,args) -> 
        let num_of_args = string_of_int (List.length args) in
        let gen_args = List.fold_right (fun arg acc -> acc ^ (gen const_table fvars_table arg depth) ^ "\n" ^ "push rax\n") args ""in  
         gen_args ^ "\n" ^
         "push " ^ num_of_args ^ "\n" ^
        (gen const_table fvars_table proc depth) ^ "\n" ^ 
         "CLOSURE_ENV rbx, rax\n 
          push rbx\n
          push qword[rbp + (8 * 1)]
          SHIFT_FRAME " ^ string_of_int ((List.length args) + 3) ^ "\n"^
          "CLOSURE_CODE rbx, rax\n
          jmp rbx\n"
           
         | LambdaOpt'(paramtesrs,opt,body) -> 
        let _id = (increase_count true) in
        let code_label = (string_of_int _id) in 
        let cont_label = (string_of_int _id) in
        let d =  (string_of_int depth) in  
        "EXT_ENV " ^ d ^ "\n" ^
        "mov rbx, rax\n"^
        "MAKE_CLOSURE(rax, rbx, "  ^ "Lcode"^code_label ^ ")\n"^
        "jmp Lcont" ^ cont_label ^ "\n" ^
        "Lcode" ^ code_label ^ ":\n" ^
        "FIX_STACK " ^ (string_of_int ((List.length paramtesrs ) +1)) ^ "\n" ^
        "push rbp\n" ^
        "mov rbp, rsp\n" ^
        (gen const_table fvars_table body (depth+1)) ^
        "leave\n" ^
        "ret\n" ^
        "Lcont"^ cont_label ^ ":\n"     
      | _ -> "" ;; 
      
module Code_Gen : CODE_GEN = struct

  let make_consts_tbl asts = 
    let _scanned = List.concat (List.map (fun x -> scan_ast x) asts) in
    let _to_set = List.rev (List.fold_left append_uniq [] _scanned) in 
    let _expanded = expand_sexprs_list _to_set in 
    check_exp _expanded [] ;;

  let make_fvars_tbl asts = 
    let scanned = List.append primitive (List.fold_left(fun acc ast -> List.append acc (scan_ast_var ast)) [] asts)  in 
    let to_set = List.rev (List.fold_left append_uniq [] scanned)  in 
    let table = make_pair_with_index to_set [] 0 in 
    table;;

  let generate consts fvars e = gen consts fvars e 0 ;;

end;;