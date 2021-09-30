theory LocalLexingSpecification
imports  "LocalLexing2.LocalLexing" Regex_Equivalence.Automaton Main
begin

text "'a - terminal type
      'b - character type
      'c - nonterminal type
      'd - parse tree type"
type_synonym ('a, 'b) terminal =  "('a \<times> 'b rexp list)"
type_synonym ('a, 'b) token = "('a, 'b) terminal \<times> 'b list"

type_synonym 'a eval =  "'a rexp \<Rightarrow> 'a  list \<Rightarrow> bool"

datatype ('a, 'c) symb = Terminal 'a | Nonterminal 'c 

type_synonym ('a,  'c) rules = "'c * (('a, 'c) symb list) " 
type_synonym ('a,  'c) \<RR>' = "('a, 'c) rules list"

text "
'a
'b \<Rightarrow> parse tree type
"

datatype bias  = Left | Right | Nonassoc


datatype ('a, 'b, 'c) specs = 
  Spec
    (terminals: "('a, 'b )terminal list list") 
    (rules : "('a,  'c) \<RR>'") 
    (start : "('a, 'c) symb")
    (lexing : "'b eval")
    (pairing: "'a \<Rightarrow> bias")

(*conversion functions*)
fun to_terminal::"('a, 'b, 'c) specs \<Rightarrow> 'a set" where
  "to_terminal (Spec l _ _ _ _) = set (map fst (concat l))"
(*we want an order on the precedence of operators, *)
fun convert_order::"('a, 'b )terminal list list \<Rightarrow> ('a \<times> nat) list" where
"convert_order a = concat (map (\<lambda>(l, i) \<Rightarrow> map (\<lambda> r \<Rightarrow> (fst r, i)) l) (zip a [0..<length a])) "
(*selector generator: currently only total order on terminals*)
(*using strings for now until symbols are changed to a generic type*)

fun rank::"('a \<times> int) list \<Rightarrow> ('a,  'b) terminal \<Rightarrow> ('a, 'b ) terminal \<Rightarrow> bool" where
"rank ls (s, _) (s', _) = ((snd (hd (filter (\<lambda>(p,_). p = s) ls))) < (snd (hd (filter (\<lambda>(p,_). p = s') ls)))) "

fun selector::"('a \<times> int) list \<Rightarrow> ('a, 'b) token \<Rightarrow> ('a, 'b) token \<Rightarrow> bool" where
"selector ls (t, c) (t' ,c')=  (((length c) < (length c')) \<or> ((length c = length c')) \<and> rank ls t t')"


end