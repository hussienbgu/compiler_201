
#use "pc.ml";;
open PC;;
exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

  
  let make_paired nt_left nt_right nt =
        let nt = caten nt_left nt in
        let nt = pack nt(function(_, e) -> e) in 
        let nt = caten nt nt_right in 
       let nt = pack nt(function(e, _) -> e) in 
       nt;;
    

(*comments*)
let linecomment_parser s = 
  let new_line = char '\n' in
  let semicolon = char ';' in 
  let semicolontoList = pack semicolon (fun(n)->[n]) in
  let new_lineTolist = pack new_line (fun(n)->[n]) in
  let line_comment = caten semicolontoList (star(range (char_of_int 11) (char_of_int 127))) in 
  let _newLine_endofInput = caten line_comment (disj new_lineTolist  nt_end_of_input)  in
  let nt_comment = pack  _newLine_endofInput  (fun ((e,s),es) -> ' ') in 
nt_comment s;;
(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)
(*boolean*)
let boolean_parser s =
  let _hashtag = char '#' in
  let _true = char_ci 't' in
  let _false = char_ci 'f' in 
  let nt_bool = pack (caten _hashtag (disj _true _false)) (fun(hashtag,s) -> match (s) with 
                                                                | ('t') -> Bool(true)
                                                                | ('T') -> Bool(true)
                                                                | ('F') -> Bool (false) 
                                                                | ('f') -> Bool(false)
                                                                | (_) -> raise X_no_match) in
nt_bool s;;
(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)
(*numbers*)
let _digit = range '0' '9';;
let _digits = plus _digit ;;
let _neg_sign = char '-'  ;;
let _pos_sign = char '+'  ;;
let nt_epsilon2 s = ('1',s);;
let parse_sign s = 
 let _sign = pack (disj_list [_pos_sign; _neg_sign;nt_epsilon2]) (fun (e) -> match e with
                                                         | '-' -> -1
                                                         | '+' -> 1 
                                                         | _-> 1) in _sign s ;;
let rec gcd a b =
 if b = 0 then a else gcd b (a mod b);;
  
let parse_integer s =
  let sign_ = pack parse_sign (fun (e) -> if e = 1 then 1 else -1 ) in   
  let int_signed = caten sign_ _digits in
   let _signed_integer = pack int_signed  (fun(sign,num) -> (sign,num)) in _signed_integer s ;;
  

let parse_Integer s =
  let parse_ineger1= pack   parse_integer (fun (sign,num) -> 
                  (Number (Fraction (( sign*int_of_string(list_to_string(num))) , 1)))) in parse_ineger1 s;;


let parse_Fraction s =
  let div = char '/' in
  let denominator = caten div _digits in
  let _right = pack denominator  ( fun(div,num) -> num) in
  let nat_fraction = pack (caten parse_integer _right)  (fun( (sign,e),o )  ->
  let gcd_ = gcd (int_of_string(list_to_string(e)))  (int_of_string(list_to_string(o)))  in
  Number(Fraction ( sign * ((int_of_string(list_to_string(e))) / gcd_) , (int_of_string(list_to_string(o)) / gcd_ )))) in nat_fraction s;;


let parse_Floating s = 
  let _dot = char '.' in 
  let _natural = caten _dot _digits in
  let _natural_num = pack _natural ( fun(dot,num) -> num) in
  let nat_float = pack (caten parse_integer _natural_num ) (fun (((sign,e),o)) ->
      let si = float_of_int(sign) in 
      let left =    ((float_of_int(int_of_string(list_to_string(e))))) in 
      let right =   (((float_of_int(int_of_string(list_to_string(o)))))/. (10.0 ** float_of_int(List.length o))) in 
        Number(Float(si *.(left  +. right)))) in nat_float s;;
    

 let parse_number s =
   let _number = disj_list [parse_Fraction;parse_Floating;parse_Integer] in _number s;;

(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)
(*char*)
let char_parser s = 
  let character_prefix =  word "#\\"  in
  let _null   =   pack (word_ci "nul") (fun (_) ->  (char_of_int 0))  in
  let _newline =  pack (word_ci "newline") (fun x -> '\n') in
  let _return =   pack (word_ci "return")  (fun (_) ->  (char_of_int 13)) in  
  let _tab =      pack (word_ci "tab")     (fun (_) ->  (char_of_int 9))  in    
  let _formfeed = pack (word_ci "page")    (fun (_) ->  (char_of_int 12)) in
  let _space =    pack (word_ci "space")   (fun (_) ->  (char_of_int 32)) in
  let named_char = disj_list ([_null;_newline;_return;_tab;_formfeed;_space]) in
  let visiblechar = guard nt_any (fun c -> c > ' ')in
  let chars = caten character_prefix (disj named_char  visiblechar) in
  let nt_char = pack chars (function (a,c) -> Char(c)) in
  nt_char s;;
(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)
(*symbol*)
let symbol_parser s = 
  let _lowercase = range 'a' 'z' in
  let _uppercase = range 'A' 'Z' in
  let _digits = range '0' '9' in
  let _punctuation = disj_list [char '?' ; char '/' ; char '>' ; char '<' ; char '+' ; char '=' ; 
                                char '_' ; char '_' ; char '-' ; char '*' ; char '^' ; char '$' ; char '!'; char ':'] in
  let _dot =  char '.'in 
  let _symbolcharNo_Dot = disj_list[_lowercase;_uppercase;_digits;_punctuation] in
  let _symbolchar = disj  _symbolcharNo_Dot _dot in
  let x = pack (caten _symbolchar (plus _symbolchar)) (fun (s,s1) -> s::s1) in
  let _symbol  =   disj_list[x;pack _symbolcharNo_Dot (fun (a) -> [a])] in
  let _packed = pack _symbol (fun (s) -> Symbol(String.lowercase_ascii(list_to_string s))) in 
  _packed s;;
(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)
(*string*)

  let string_parser s = 
    let _return  = pack (word "\\r") (fun (_) -> '\r')  in
    let _newline = pack (word "\\n") (fun (_) -> '\n') in          
    let _tab =     pack (word "\\t") (fun (_) -> '\t')  in         
    let _page =    pack (word "\\f") (fun (_) -> '\012') in        
    let _backslash = pack (word "\\\\")   (fun (_) -> '\\') in    
    let _double_quote =  pack (word "\\\"")   (fun (_) -> '\"') in  
    let string_literal_char =  disj_list [range (char_of_int 0)(char_of_int 33);range (char_of_int 35)(char_of_int 91);range (char_of_int 93)(char_of_int 127)]  in
    let string_meta_chars = disj_list([_return;_newline;_tab;_page;_backslash;_double_quote]) in
    let _string_char = disj string_literal_char string_meta_chars in
    let x = caten (char '\034') (caten (star _string_char) (char '\034')) in
    let _string = pack x (fun (_,(s,_))-> String(list_to_string(s))) in _string s;;
 
(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)

(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)

let parse_scient_notation s =
  let _e = char_ci 'e' in
  let _numbers = disj parse_Floating parse_Integer in 
  let _left = caten _numbers _e in
  let first_side = pack _left (fun(g,h)-> match g with |(Number(Float(res)))-> res 
                                                       |(Number(Fraction(res,1))) -> float_of_int(res) | _ -> raise X_this_should_not_happen) in
 
  let _right = caten first_side _numbers in
  let final = pack _right (fun(g,h) ->      let x = match h with |(Number(Float(res)))-> res 
                                                                 |(Number(Fraction(res,1))) -> float_of_int(res) 
                                                                 | _ -> raise X_this_should_not_happen   in 
                                      (Number(Float(g *. (10. ** x))))) in not_followed_by final symbol_parser s ;; 

  let _parser_of_num s = not_followed_by (disj parse_scient_notation parse_number) symbol_parser s;;

let rec sexpr_parser s =

  let all =(disj_list[boolean_parser;
                      char_parser;
                      _parser_of_num;
                      string_parser;
                      symbol_parser;
                      list_parser;
                      dotted_list_parser;
                      quote_parser;
                      qquote_parser ;
                      unquote_parser;
                      unqspliced_parser;
                      nil_parser]) in 
  
  let _sexp =   make_paired (star _clear_whitespaces_comments) (star _clear_whitespaces_comments) all in 
    _sexp s 
  
   and sexp_comment_parser s =
    let _prefix = word "#;" in
    let _comm = caten _prefix sexpr_parser in
    let _pack = pack _comm (fun (_) -> '_' ) in _pack s 

  and _clear_whitespaces_comments s = 
    let _disj = disj_list [char(' ');linecomment_parser;sexp_comment_parser;nt_whitespace] in _disj s 

  
  and nil_parser s = 
    let left_paren = char '(' in
    let right_paren = char ')' in
    let pair_ = make_paired left_paren right_paren (star _clear_whitespaces_comments) in 
    let _pack = pack pair_ (fun (_) -> Nil) in 
    _pack s 
 
and list_parser s =
    let rec make_pair lst = 
      match lst with 
        | [] -> Nil 
        | h::t ->Pair(h,(make_pair t)) in 
    let left_paren = char '(' in 
    let right_paren = char ')' in
    let _nt = pack (star sexpr_parser) (fun(sexpr)-> make_pair sexpr) in
    let _list = make_paired left_paren right_paren _nt in
    _list s

and dotted_list_parser s =
    let rec make_pair lst = 
      if ((List.length lst) = 1) 
        then (List.hd lst) 
        else Pair((List.hd lst),make_pair (List.tl lst)) in
    let _left_paren = char '(' in 
    let _right_paren = char ')' in
    let _dot = char '.' in 
    let _pack = pack (caten (plus sexpr_parser) _dot) (fun (e,s)-> e) in  
    let _list = make_paired _left_paren _right_paren (caten _pack sexpr_parser) in
    let _flist = pack _list (fun (e,es) ->  List.append e [es]) in
    let _plist = pack _flist (fun (e) -> make_pair e) in
    _plist s

(*Quote-like forms*)

    
and quote_parser s= 
let _quoted  =  char (char_of_int 39) in
let _pack = pack  (caten  _quoted sexpr_parser) (fun (e,s) -> Pair(Symbol("quote") , Pair(s, Nil))) in _pack s 

and qquote_parser s=
let _qquoted  = (char '`') in
let _pack = pack  (caten  _qquoted sexpr_parser) (fun (e,s) -> Pair(Symbol("quasiquote") , Pair(s, Nil))) in _pack s 

and unquote_parser s = 
let _unquoted = (char ',') in
let _pack = pack  (caten  _unquoted sexpr_parser) (fun (e,s) -> Pair(Symbol("unquote") , Pair(s, Nil))) in _pack s 


  and unqspliced_parser  s= 
  let _unquoted = char ',' in
  let _unqspliced_c = caten _unquoted (char '@') in
  let _unqspliced = pack (caten _unqspliced_c  sexpr_parser) (fun (e,s) -> Pair(Symbol("unquote-splicing") , Pair(s,Nil))) in 
    _unqspliced s;;



(*-----------------------------------------------------------------------------------------------------------------------------------------------------*)
let read_sexprs s=
let (car,cdr) = test_string (star sexpr_parser) s in
car;;

end;; (* struct Reader *)