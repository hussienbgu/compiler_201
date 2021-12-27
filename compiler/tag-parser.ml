#use "reader.ml";;
open Reader;;

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

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  


(* work on the tag parser starts here *)

let rec check_proper_list lst =
  match lst with
    | Nil -> true
    | Pair(car,Nil) -> true
    | Pair(car,Pair(a,b)) -> check_proper_list (Pair(a,b))
    | Pair(car,cdr) -> false
    | _ -> false
;;
  
let rec list_from_pairs pair=
  match pair with
    | Nil -> []
    | Pair(expr,Nil)->[expr]
    | Pair(expr, Pair(car,cdr))-> expr::list_from_pairs(Pair(car,cdr))
    | Pair(expr1,expr2)->expr1::[expr2]
    | _-> raise X_syntax_error
;;

let rec pair_to_string_lst sexp = 
  let str_lst = list_from_pairs sexp in
    List.map (fun e -> match e with
      |Symbol(name)-> name
      |_ -> raise X_syntax_error)
      str_lst
;;
  
let rec remove_last lst =
  match lst with
    | [s] -> []
    | car::cdr -> List.append [car] (remove_last cdr)
    | [] -> []
;;

let get_last lst = 
  let rev_lst = List.rev lst in match rev_lst with
  | car :: cdr -> car
  | [] -> "empty list"
;;

let rec list_to_pairs lst =
  match lst with 
    | a::[] -> Pair(a,Nil) 
    | a::b -> Pair(a,list_to_pairs b)
    | [] -> raise X_syntax_error 
;;

let rec map_tag_parse func lst =
  match lst with 
    | Nil -> []
    | Pair(car,cdr) -> List.append([func car]) (map_tag_parse func  cdr)
    | _ -> raise X_syntax_error
;;

let rec get_vals_of_params parameters = 
  match parameters with 
    | Nil -> (Nil,Nil)
    | Pair(Pair(param,Pair(value,Nil)),cdr) ->
      let (_args,_values) = (get_vals_of_params cdr) in
      (Pair(param,_args),Pair(value,_values))
    | _ -> raise X_syntax_error
;;

let expand_MIT_define name arglist expr =
  Pair(Symbol "define" ,Pair (Symbol name,Pair(Pair(Symbol "lambda",Pair (arglist,expr)),Nil)))
;;  

let expand_and exp =
  match exp with
  | Nil -> (Bool true)
  | Pair(e,Nil) -> e
  | Pair(first,second) -> (Pair(Symbol "if",Pair(first,Pair(Pair(Symbol "and",second),Pair(Bool false,Nil)))))
  | _ -> raise X_syntax_error
;;

let expand_let_star exp =
  match exp with 
  | Pair(Nil,body) -> Pair(Symbol "let",Pair(Nil,body)) 
  | Pair(Pair(v,Nil),ex)-> Pair(Symbol "let",Pair(Pair(v,Nil),ex))
  | Pair(Pair(v1,rest_vs),ex) -> Pair(Symbol("let"),Pair(Pair(v1,Nil),Pair(Pair(Symbol "let*",Pair(rest_vs,ex)),Nil)))
  | _ -> raise X_syntax_error
;;


let expand_letrec (a, b) =
let rec get_params args =
match args with 
| Nil -> (Nil,b)
| Pair(Pair(Symbol a,Pair(b,Nil)),cdr) -> (let (x,y) = get_params cdr in 
 (Pair(Pair(Symbol a,Pair(Pair(Symbol "quote",Pair(Symbol "whatever",Nil)),Nil)),x),Pair(Pair(Symbol "set!",Pair(Symbol a,Pair(b,Nil))),y)))
| _ -> raise X_syntax_error in
let (params,values) = get_params a in 
Pair (Symbol "let",Pair(params,values))
;;

let rec expand_cond ribs =
match ribs with 
| Nil -> Nil
| Pair(exp,rest) -> (match exp with
                     | Pair(test,Pair(Symbol "=>",exp1))  -> if (rest=Nil)
                        then (Pair(Symbol "let",Pair(Pair(Pair(Symbol "value",Pair(test,Nil)),Pair(Pair(Symbol "f",Pair(Pair(Symbol "lambda",Pair(Nil,exp1)),Nil)),Nil)),Pair(Pair(Symbol "if",Pair(Symbol "value",Pair(Pair(Pair(Symbol "f",Nil),Pair(Symbol "value" , Nil)),Nil))),Nil))))
                        else (Pair(Symbol "let",Pair(Pair(Pair(Symbol "value",Pair(test,Nil)),Pair(Pair(Symbol "f",Pair(Pair(Symbol "lambda",Pair(Nil,exp1)),Nil)),Pair(Pair(Symbol "rest",Pair(Pair(Symbol "lambda",Pair(Nil,Pair(expand_cond rest,Nil))),Nil)),Nil))),Pair(Pair(Symbol "if",Pair(Symbol "value",Pair(Pair(Pair(Symbol "f",Nil),Pair(Symbol "value" , Nil)),Pair(Pair(Symbol "rest",Nil),Nil)))),Nil))))
                     | Pair(Symbol "else",exp1) -> Pair(Symbol "begin",exp1)
                     | Pair(test,exp1) ->  Pair(Symbol "if",Pair(test,Pair(Pair(Symbol "begin",exp1),Pair((expand_cond rest),Nil))))  
                     | _ -> raise X_syntax_error)
| _ -> raise X_syntax_error
;;

let expand_let (parameters,body) =    
  let (args,values) = (get_vals_of_params parameters) in
  Pair(Pair(Symbol "lambda",Pair (args,body)),values)
;;

let rec expand_quasiquote x = 
  match x with  
  | Pair (Symbol "unquote",Pair(sexprtion,Nil)) -> sexprtion
  | Pair (Symbol "unquote-splicing",Pair(sexprtion,Nil)) -> raise X_no_match
  | Nil -> Pair(Symbol "quote",Pair(x,Nil))
  | Symbol s -> Pair(Symbol "quote" ,Pair(Symbol s ,Nil))
  | Pair(Pair (Symbol "unquote-splicing",Pair(sexprtion,Nil)),_B) -> Pair(Symbol"append",Pair(sexprtion,Pair(expand_quasiquote _B ,Nil)))
  | Pair(_A,Pair(Symbol "unquote-splicing",Pair(sexprtion,Nil))) -> Pair(Symbol "cons",Pair(expand_quasiquote _A,Pair(sexprtion,Nil)))
  | Pair(_A,_B) -> Pair(Symbol "cons",Pair(expand_quasiquote _A,Pair(expand_quasiquote _B,Nil)))
  | _A ->  Pair(Symbol("quote"),Pair(_A, Nil)) ;;
  
 
let rec expand_pset exp = 
  match exp with
    | Nil -> Nil
    | (Pair(Pair(Symbol(a) ,Pair(exp,Nil)),Nil)) -> 
      (Pair(Pair(Symbol "lambda",Pair(Nil,Pair(Pair(Symbol "set!",Pair(Symbol(a),Pair(exp,Nil))),Nil))),Nil))    
    | Pair(Pair(Symbol(a),Pair(exp,Nil)),rest) ->
      Pair
      (Pair (Symbol "lambda",
        Pair (Pair (Symbol "h_f", Nil),
         Pair
          (Pair (Symbol "set!",
            Pair (Symbol (a),
             Pair
              (Pair (Symbol "begin",
                Pair(expand_pset rest,
                 Pair (Symbol "h_f", Nil))),
              Nil))),
          Nil))),
      Pair (exp, Nil))
      
      | _ -> raise X_no_match ;;
   
   let rec tag_parse s =
  match s with
    | Nil       -> Const(Void)
    | Bool(e)   -> Const(Sexpr(Bool(e)))
    | Char(e)   -> Const(Sexpr(Char(e)))
    | Number(e) -> Const(Sexpr(Number(e)))
    | String(e) -> Const(Sexpr(String(e)))
    | Symbol(e)   -> if(List.mem e reserved_word_list)
                      then raise X_syntax_error
                      else Var(e)
    | Pair(Symbol("unquote"),Pair(e,Nil)) -> Const(Sexpr(e))
    | Pair(Symbol("quote"),Pair(e,Nil))-> Const(Sexpr(e))
    | Pair(Symbol "if",exp) -> parse_if exp
    | Pair(Symbol "lambda",Pair(Nil, body)) -> LambdaSimple([],parse_begin body)
    | Pair(Symbol "lambda",Pair(Symbol(arg), body)) -> LambdaOpt([],arg, (parse_begin body))
    | Pair(Symbol "lambda",Pair(args, body)) -> lambda_parse args body
    | Pair(Symbol "or",exp) -> parse_or exp
    | Pair(Symbol "define",exp) -> parse_define exp 
    | Pair(Symbol "set!",exp) -> parse_set exp 
    | Pair(Symbol "begin",expr_list) -> parse_begin expr_list
    | Pair(Symbol "quasiquote",Pair(expr,Nil)) -> tag_parse(expand_quasiquote expr)
    | Pair(Symbol "cond" ,ribs) -> tag_parse(expand_cond ribs)
    | Pair(Symbol "let",Pair(parameters,body)) -> tag_parse(expand_let (parameters,body))
    | Pair(Symbol "let*",exp) -> tag_parse(expand_let_star exp)
    | Pair(Symbol "letrec",Pair(parameters,body)) -> tag_parse(expand_letrec (parameters,body))
    | Pair(Symbol "and",exp) -> tag_parse (expand_and exp)
    | Pair(Symbol "pset!",exp) ->  tag_parse(expand_pset exp) 
    | Pair(_A,_B)-> Applic((tag_parse _A),  (map_tag_parse tag_parse _B))  
  

  (* Conditionals *)
  and parse_if exp =
    match exp with 
      | Pair(test,Pair(dit,Pair(dif,Nil))) ->  parse_if_then_else test dit dif 
      | Pair(test,Pair(dit,Nil)) -> parse_if_then test dit
      | _ -> raise X_syntax_error

  and parse_if_then_else test dit dif =
    If (tag_parse test,tag_parse dit,tag_parse dif) 

  and parse_if_then test dit =
    If (tag_parse test,tag_parse dit,tag_parse Nil)

  (* Lambda *)
  and lambda_parse args body =
    let body_seq = (parse_begin body) in
     match args with
        | Pair(car, cdr) -> let str_list = pair_to_string_lst args in
           if (check_proper_list args) then LambdaSimple(str_list, body_seq) else  
          LambdaOpt((remove_last str_list), (get_last str_list) , body_seq)
        | _ -> raise X_syntax_error

  and parse_or  exp =
    match exp with 
      | Nil -> tag_parse (Bool false)
      | Pair(x,Nil) -> tag_parse x
      | Pair(first,second) -> Or (map_tag_parse tag_parse (Pair(first,second)))
      | _ -> raise X_syntax_error
  
  and parse_define exp =
    match exp with 
      |Pair(Pair(Symbol(name),arglist),expr) -> tag_parse(expand_MIT_define name arglist expr)
      |Pair(name,Pair(value,Nil)) ->  parse_simple_define name value 
      | _ -> raise X_syntax_error

  and parse_simple_define name value =
    Def(tag_parse (name),tag_parse(value))

  and parse_set exp =
    match exp with
    | Pair(Symbol var,Pair(value,Nil)) -> Set(tag_parse (Symbol var),tag_parse value)
    | _ -> raise X_syntax_error
  
  and parse_begin exp =
    match exp with
    | Nil -> Const(Void)
    | Pair(ex, Nil) -> (tag_parse ex)
    | _ -> let rec flatten exp = 
          match exp with
          |Nil -> []
          |Pair(e1,e2) -> e1::flatten e2
          |_ -> [exp] in
          Seq(List.map tag_parse (flatten exp))
                                                            
let tag_parse_expressions sexpr = List.map  tag_parse sexpr ;;

end;; (* struct Tag_Parser *)


