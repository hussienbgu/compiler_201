#use "tag-parser.ml";;
open Tag_Parser ;;

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
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

  let get_last lst = 
    List.hd (List.rev lst)
  ;;
  
  let remove_last lst=
    List.rev (List.tl (List.rev lst))
  ;;
  (* ************************************************************************************************************************ *)
  
  let rec get_index var array i = 
    match array with 
      | [] -> -1
      | car::cdr -> if ( car = var) 
                      then i
                      else get_index var cdr (i + 1);;
 
  let rec get_depth array var i = 
    match array with
      | [] -> (VarFree(var))
      | car::cdr -> 
        let pos = (get_index var car 0) in
        match (pos = -1) with
        | true -> (get_depth cdr var (i+1))
        | false-> (match (i= -1) with
                  | true -> (VarParam(var,pos))
                  | false -> (VarBound(var,i,pos)));;
    
  let type_of_Var var array = 
      (get_depth array var (-1));;
  
  let rec lexical_address e array  = 
    match e with
      | Const x -> Const' x
      | Var x -> Var'(type_of_Var x array)
      | If(tst,thn,els) -> If'(lexical_address tst array,lexical_address thn array,lexical_address els array)
      | Seq(lst) -> Seq'( (List.map (fun element -> (lexical_address element array)) (lst) )) 
      | Set(Var(var1),expr) -> Set'( (type_of_Var var1 array),(lexical_address expr array))
      | Def(Var(var1),expr) -> Def'( (type_of_Var var1 array) , lexical_address expr array)
      | Or(lst) -> Or'(List.map(fun element -> (lexical_address element array))(lst))
      | LambdaSimple(vars, body) -> LambdaSimple'(vars,lexical_address body (vars::array))
      | LambdaOpt(vars,var,body) -> LambdaOpt'(vars,var, lexical_address body ((List.append vars [var]) ::array ))
      | Applic (exp1,exp2) -> Applic' (lexical_address exp1 array,(List.map(fun element -> (lexical_address element array))(exp2))) 
      | _ -> raise X_syntax_error;;
      
  let annotate_lexical_addresses e= lexical_address e [];;
  

(* ************************************************************************************************************************ *)

  let rec is_tail_call e in_tp =
    match e with
      | Const' x -> e
      | Var' x -> e
      | If' (tst,thn,els) -> If'(is_tail_call tst false,is_tail_call thn in_tp, is_tail_call els in_tp) 
      | Seq' (list) ->  let without_last = remove_last list in
                        Seq'(List.append (List.map(fun element -> (is_tail_call element false)) (without_last)) [(is_tail_call (get_last list) in_tp)])
      | Set' (var,expr) -> Set'(var, is_tail_call expr false)
      | Def' (var,expr)-> Def'(var, is_tail_call expr false)
      | Or' (list) -> let without_last = remove_last list in
                      Or'(List.append ((List.map(fun element -> (is_tail_call element false))(without_last))) [(is_tail_call (get_last list) in_tp)])
      | LambdaSimple' (vars, body) -> LambdaSimple' (vars, is_tail_call body true)
      | LambdaOpt' (vars,var,body) -> LambdaOpt' (vars,var,is_tail_call body true)
      | Applic'(exp1,exp2) -> (match in_tp with
                  | false -> Applic'((is_tail_call exp1 false),(List.map (fun element ->  (is_tail_call element false)) (exp2)))
                  | true -> ApplicTP'((is_tail_call exp1 false),(List.map (fun element -> (is_tail_call element false)) (exp2))))
      | _ -> raise X_syntax_error
(* ********************************************************************************************************************************* *)

let count = ref 0 ;;
let counter make_zero= 
  match make_zero with
    |true -> fun ()-> (count:= 0);!count 
    |false -> fun ()->(count:= !count +1);!count;;
 
 let count2 = ref 0 ;;
 let counter2 make_zero= 
  match make_zero with
    |true -> fun ()-> (count2:= 0);!count2 
    |false -> fun ()->(count2:= !count2 +1);!count2 
   
 let rec occurs_in_read var path body =
  match body with
      | Var'(x) -> (match x with 
                    | VarParam (v1,mn1)       -> if (var = v1) then [path] else []
                    | VarBound (v1,mj1,mn1)    -> if (var = v1) then [path] else []
                    | VarFree (v) -> [])
      | If'(tst,thn,els)            -> (occurs_in_read var path tst ) @ (occurs_in_read var path thn) @ (occurs_in_read var path els)
      | Or'(lst)                       -> List.fold_right (fun a b -> (occurs_in_read var path a)@ b) lst []
      | Seq'(lst)                      -> List.fold_right (fun a b -> (occurs_in_read var path a)@ b) lst []
      | Def'(v,value)                  -> (occurs_in_read var path (Var'(v))) @ (occurs_in_read var path value)
      | BoxSet' (v,expr)-> (occurs_in_read var path expr)
      | Set'(v,value)                  -> (occurs_in_read var path value)
      | LambdaSimple'(vars,body)       ->  
                                          if (List.mem var vars) then []
                                          else (occurs_in_read var ([(counter false())] @ path) body)
      | LambdaOpt'(vars,variadic,body) -> 
                                          if (List.mem var (variadic::vars)) then []
                                          else (occurs_in_read var ([(counter false())] @ path) body)
      | Applic'(rator, rands)          -> (occurs_in_read var path rator) @
        List.fold_right (fun a b -> (occurs_in_read var path a )@ b) rands []
      | ApplicTP'(rator, rands)        -> (occurs_in_read var path rator) @
        List.fold_right (fun a b -> (occurs_in_read var path a )@ b) rands []                               
      | _ -> [] ;;

    let var_write x param  =
      match x with
             | Var'(VarParam (var,mn1)) -> (var = param)
             | Var'(VarBound (var,mj1,mn1)) -> (var = param)
             | Var'(VarFree(var)) -> (var = param)
             | _ -> raise X_syntax_error
    ;;

   let rec occurs_in_write var path body =
    match body with
      | Set'(x,exp) ->  (let check_var = var_write (Var'(x)) var in
          match check_var with
            | true -> [path]
            | false -> (occurs_in_write var path exp))
      | If'(tst,thn,els)    -> (occurs_in_write var path tst ) @ (occurs_in_write var path thn) @ (occurs_in_write var path els)
      | Or'(lst)            -> fold_right_lst occurs_in_write lst var path
      | Seq'(lst)           -> fold_right_lst occurs_in_write lst var path
      | Def'(v,value)       -> (occurs_in_write var path (Var'(v))) @ (occurs_in_write var path value)
      | BoxSet' (v,expr)    -> (occurs_in_write var path expr)                                    
      | LambdaSimple'(vars,body)       -> if (List.mem var vars) then []
                                          else (occurs_in_write var  ([(counter2 false())]@path) body)
      | LambdaOpt'(vars,variadic,body) -> if (List.mem var (variadic::vars)) then []
                                          else (occurs_in_write var  ([(counter2 false())]@path) body)
      | Applic'(rator, rands)          -> (occurs_in_write var path rator) @ fold_right_lst occurs_in_write rands var path                                          
      | ApplicTP'(rator, rands)        -> (occurs_in_write var path rator) @ fold_right_lst occurs_in_write rands var path 
      | _ -> [] 

      and fold_right_lst func lst var path = List.fold_right (fun a b -> (func var path a )@ b) lst []
  ;;


  let rec box_set_rec vars_to_box e = 
  match e with
  | Var'(VarBound (var,mjr,mnr)) -> (let is_to_box = (List.mem var vars_to_box) in
                                    match is_to_box with
                                      |true -> (BoxGet'(VarBound (var,mjr,mnr)))
                                      |_ -> e)
  | Var'(VarParam (var,mnr))     -> (let is_to_box = (List.mem var vars_to_box) in
                                    match (is_to_box) with
                                      |true ->  (BoxGet'(VarParam(var,mnr)))
                                      |_ -> e)
  | If'(test,alt,elsee)     -> If'((box_set_rec vars_to_box test ),(box_set_rec vars_to_box alt  ),(box_set_rec vars_to_box elsee))
  | Def'(var,value)         -> Def'(var, (box_set_rec vars_to_box value))
  | Or'(lst)                -> Or'(List.map (box_set_rec vars_to_box) lst)
  | Seq'(lst)               -> Seq'(List.map (box_set_rec vars_to_box) lst)
  | Set' (x,expr)           -> wd_set x expr vars_to_box
  | BoxSet'(v,e)            -> BoxSet'(v, box_set_rec vars_to_box e)                                         
  | LambdaSimple'(vars,body)-> wd_lambdasimple vars body vars_to_box
  | LambdaOpt'(vars,variadic,body) -> wd_lambdaopt vars variadic body vars_to_box
  | Applic'(rator, rands)   -> Applic'((box_set_rec vars_to_box rator), (List.map (box_set_rec vars_to_box) rands))
  | ApplicTP'(rator, rands) -> ApplicTP'((box_set_rec vars_to_box rator), (List.map (box_set_rec vars_to_box) rands))
  | _ -> e  (* Const' _ |Box' _|BoxGet' _|Var'(VarFree v) *)
  
  and wd_set x expr vars_to_box =
      match x with
      | VarFree(v) -> Set'(x,box_set_rec vars_to_box expr) 
      | VarParam(v,i) -> (let is_to_box = (List.mem v vars_to_box) in
                            match is_to_box with 
                              | false -> Set'(x,(box_set_rec vars_to_box expr)) 
                              | true -> (BoxSet'(VarParam(v,i),(box_set_rec vars_to_box expr)))
      )
      | VarBound(v,i,j) -> (let is_to_box =  (List.mem v vars_to_box) in 
                            match is_to_box with 
                              | false -> Set'(x,(box_set_rec vars_to_box expr)) 
                              | true ->  (BoxSet'( (VarBound(v,i,j)) , (box_set_rec vars_to_box expr)))
      )

  and wd_lambdasimple vars body vars_to_box=
      let vars_to_box = List.filter (fun var -> not (List.mem var vars)) vars_to_box in
      let params_to_box = List.filter (fun var -> (check_bound var body) && (same_ancstr var body)) vars in
      let body = (box_set_rec (vars_to_box @ params_to_box) body) in
      let add_to_seq = (List.map
                          (fun (x)->let y = (find_addrs vars 0 x) in
                          (Set' ((VarParam (x,y)),Box' (VarParam (x,y)))))  
                          params_to_box) in
      let body = do_body (add_to_seq @ [body]) in
      LambdaSimple'(vars,body)

  and wd_lambdaopt vars variadic body vars_to_box=
      let all_vars = vars@[variadic] in
      let vars_to_box = List.filter (fun var -> not (List.mem var all_vars)) vars_to_box in
      let params_to_box = List.filter (fun var -> (check_bound var body) && (same_ancstr var body)) all_vars in
      let body = (box_set_rec (vars_to_box @ params_to_box) body) in
      let add_to_seq    = (List.map 
                          (fun (x)->let y = (find_addrs all_vars 0 x) in
                          (Set' ((VarParam (x,y)),Box' (VarParam (x,y))))) params_to_box) in
      let body = do_body (add_to_seq @ [body]) in
      LambdaOpt'(vars,variadic,body)
  

  and check_bound var = function
    | Var'(VarParam (v1,mn1)) -> false
    | Var'(VarBound (v1,mj1,mn1)) -> (v1 = var)
    | If'(test,alt,elsee) -> (check_bound var test ) || (check_bound var alt) || (check_bound var elsee)
    | Or'(lst)    -> ormap (check_bound var) lst
    | Seq'(lst)   -> ormap (check_bound var) lst
    | LambdaSimple'(vars,body)       -> (let is_member = (List.mem var vars) in
                                          match is_member with
                                            |true -> false
                                            |_ -> (check_bound var body) )
    | LambdaOpt'(vars,variadic,body) -> (let is_member = (List.mem var (variadic::vars)) in
                                          match is_member with
                                            |true -> false
                                            |_ -> (check_bound var body) )
    | ApplicTP'(rator, rands)        -> (check_bound var rator) || ormap (check_bound var) rands
    | Applic'(rator, rands)          -> (check_bound var rator) || ormap (check_bound var) rands
    | Set'(v, value) -> (check_bound var (Var'(v))) || (check_bound var value)
    | _ -> false

  and do_body body =
      match body with
        | [] -> Const' Void
        | s::[] -> s
        | _ -> let new_body = List.fold_left (fun acc exp -> match exp with 
                      | Seq'(x) -> List.append acc x
                      | _ -> List.append acc [exp])                
      [] body in Seq'(new_body)

  and find_addrs vars location v =
     match (vars = []) with
     |true -> -1
     |false ->  match (List.hd vars = v) with
               |false -> find_addrs (List.tl vars) (location+1) (v)
               |true -> location

  and same_ancstr var body = 
      let read_occurences  =     (occurs_in_read var [] body ) in
      let write_occurences =     (occurs_in_write var [] body) in
      let pairs_list =  List.concat (List.map (fun e -> List.map (fun e' -> (e,e')) write_occurences) read_occurences) in
      let ans =  List.fold_right (fun x y -> (check_same_ancstr x) || y) pairs_list false in 
      let x  = (counter true()) + (counter2 true()) in
      if x=0  then 
      ans else ans
  
  and check_same_ancstr pair = 
      match pair with      
      |([],[]) -> false
      |([],b) -> true
      |(a,[]) -> true
      |(a,b) -> not(a=b)
  
  let box_set e = box_set_rec [] e;;

  let annotate_tail_calls e = is_tail_call e false;; 
  
  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr));;
    
  end;; (* struct Semantics *)