theory LocalLexing
imports CFG
begin



type_synonym ('c) lexer = " 'c list \<Rightarrow> nat \<Rightarrow> nat set"  

type_synonym ('a, 'b, 'c)token = "('a, 'b) symbol \<times> 'c list" 

type_synonym ('a,'b,'c) tokens = "('a,'b,'c) token list"

definition terminal_of_token :: "('a,'b,'c) token \<Rightarrow> ('a, 'b) symbol"
where
  "terminal_of_token t = fst t"

definition terminals :: "('a,'b,'c) tokens \<Rightarrow> ('a, 'b) sentence"
where
  "terminals ts = map terminal_of_token ts"

definition chars_of_token :: "('a,'b,'c) token \<Rightarrow> 'c list"
where
  "chars_of_token t = snd t"

fun chars :: "('a,'b,'c) tokens \<Rightarrow> 'c list"
where
  "chars [] = []"
| "chars (t#ts) = (chars_of_token t) @ (chars ts)"

fun charslength :: "('a,'b,'c) tokens \<Rightarrow> nat"
where
  "charslength cs = length (chars cs)"

definition is_lexer :: "'c lexer \<Rightarrow> bool"
where
  "is_lexer lexer = 
    (\<forall> D p l. (p \<le> length D \<and> l \<in> lexer D p \<longrightarrow> p + l \<le> length D) \<and>
              (p > length D \<longrightarrow> lexer D p = {}))"

type_synonym ('a, 'b, 'c) selector = "('a,'b,'c) token set \<Rightarrow> ('a,'b,'c) token set \<Rightarrow> ('a,'b,'c) token set"

definition is_selector :: " ('a, 'b, 'c) selector \<Rightarrow> bool"
where
  "is_selector sel = (\<forall> A B. A \<subseteq> B \<longrightarrow> (A \<subseteq> sel A B \<and> sel A B \<subseteq> B))" 

definition is_selector' :: " ('a, 'b, 'c) selector \<Rightarrow> bool"
where
"is_selector' sel = (\<forall> A B. (sel A B = sel (sel A B) B))"

definition non_empty_selector :: "('a, 'b, 'c) selector \<Rightarrow> bool"
  where
  "non_empty_selector sel= (\<forall> A B. (\<forall> (t, c) \<in> sel A B. length c > 0))"

fun by_length :: "nat \<Rightarrow> ('a,'b,'c) tokens set \<Rightarrow> ('a,'b,'c) tokens set"
where
  "by_length l tss = { ts . ts \<in> tss \<and> length (chars ts) = l }" 

fun funpower :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)"
where
  "funpower f 0 x = x"
| "funpower f (Suc n) x = f (funpower f n x)"

definition natUnion :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
where
  "natUnion f = \<Union> { f n | n. True }"


definition natUnion' :: "nat \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"
where
  "natUnion' n0 f = \<Union> { f n | n. n \<le> n0 }"

definition limit  :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "limit f x = natUnion (\<lambda> n. funpower f n x)"

definition limitOn::"'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"limitOn a f x = a \<inter> limit f x"

locale LocalLexing = CFG +
  fixes Lex :: "('a::ccompare, 'b::ccompare) symbol \<Rightarrow> ('c::ccompare) lexer"
  fixes Sel :: " ('a, 'b, 'c) selector"
  assumes Lex_is_lexer: "\<forall> t \<in> \<TT>. is_lexer (Lex t)"
  assumes Sel_is_selector: "is_selector Sel"
  assumes Sel_is_selector': "is_selector' Sel"
  assumes Sel_is_nonempty: "non_empty_selector Sel"

  assumes ccomp: "ID ccompare = Some (ccomp :: 'a comparator)"
    "ID ccompare = Some (ccomp :: 'b comparator)"
    "ID ccompare = Some (ccomp :: 'c comparator)"
  fixes Doc :: "'c list"
begin

definition admissible :: "('a,'b,'c) tokens \<Rightarrow> bool"
where
  "admissible ts = (terminals ts \<in> \<L>\<^sub>P)" 

definition Append :: "('a,'b,'c) token set \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) tokens set \<Rightarrow> ('a,'b,'c) tokens set"
where
  "Append Z k P = P \<union> 
    { p @ [t] | p t. p \<in> by_length k P \<and> t \<in> Z \<and> admissible (p @ [t])}"

definition \<X> :: "nat \<Rightarrow> ('a,'b,'c) token set"
where
  "\<X> k = {(t, \<omega>) | t l \<omega>. t \<in> \<TT> \<and> l \<in> Lex t Doc k \<and> \<omega> = take l (drop k Doc)}"

definition \<W> :: "('a,'b,'c) tokens set \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) token set"
where
  "\<W> P k =  { u. u \<in> \<X> k \<and> (\<exists> p \<in> by_length k P. admissible (p@[u])) }"

definition \<Y> :: "('a,'b,'c) token set \<Rightarrow> ('a,'b,'c) tokens set \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) token set"
where
  "\<Y> T P k = Sel T (\<W> P k)" 

(*Token based proofs*)

fun \<P> :: "nat \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) tokens set"
and \<Q> :: "nat \<Rightarrow> ('a,'b,'c) tokens set"
and \<Z> :: "nat \<Rightarrow> nat \<Rightarrow> ('a,'b,'c) token set"
where
  "\<P> 0 0 = {[]}"
| "\<P> k (Suc u) = limit (Append (\<Z> k (Suc u)) k) (\<P> k u)"
| "\<P> (Suc k) 0 = \<Q> k"
| "\<Z> k 0 = {}"
| "\<Z> k (Suc u) = \<Y> (\<Z> k u) (\<P> k u) k"
| "\<Q> k = natUnion (\<P> k)"

definition \<PP> :: "('a,'b,'c) tokens set"
where
  "\<PP> = \<Q> (length Doc)"

(*set of token sets in that are wellformed*)
definition ll :: "('a,'b,'c) tokens set"
where 
  "ll = { p . p \<in> \<PP> \<and> charslength p = length Doc \<and> terminals p \<in> \<L> }"

end

end
