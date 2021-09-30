theory CFG
imports Main Containers.Containers
begin


type_synonym ('a, 'b) symbol = "('a + 'b)"

type_synonym ('a, 'b) rule = "('a , 'b) symbol \<times> ('a , 'b) symbol list"

type_synonym ('a, 'b) sentence = "('a , 'b) symbol list"

locale CFG =
  fixes \<A> :: "'a::ccompare set" (*nonterminal set*)
  fixes \<B> :: "'b::ccompare set" (*terminal set*)
  fixes \<RR> :: "('a, 'b) rule set"
  fixes \<S> ::"'a"
  assumes finite_grammar:"finite \<RR>"
  assumes finite_terminals:"finite \<B>"
  assumes startsymbol_dom: "\<S> \<in> \<A>"        
  assumes validRules: "\<forall> (N, \<alpha>) \<in> \<RR>. N \<in> (Inl ` \<A>) \<and> (\<forall> s \<in> set \<alpha>. s \<in> (Inl ` \<A>) \<union> (Inr ` \<B>))"
begin

definition \<NN>::"('a, 'b) symbol set" where
"\<NN> = Inl ` \<A>"


definition \<TT>::"('a, 'b) symbol set" where
"\<TT> = Inr ` \<B>"

definition \<SS>::"('a, 'b) symbol" where
"\<SS> = Inl \<S>"


lemma  disjunct_symbols:"\<TT> \<inter> \<NN> = {}"
  by(auto simp add: \<TT>_def \<NN>_def)


definition is_terminal :: "('a, 'b) symbol \<Rightarrow> bool"
where
  "is_terminal = case_sum (\<lambda> t. False) (\<lambda> s. s \<in> \<B>) "

definition is_nonterminal :: "('a, 'b) symbol \<Rightarrow> bool"
where
  "is_nonterminal = case_sum  (\<lambda> s. s \<in> \<A>) (\<lambda> t. False)"

lemma is_nonterminal_startsymbol:"is_nonterminal  \<SS>"
  by (simp add: is_nonterminal_def startsymbol_dom \<SS>_def)

definition is_symbol :: "('a, 'b) symbol \<Rightarrow> bool"
where
  "is_symbol s = (is_terminal s \<or> is_nonterminal s)"

lemma \<SS>_symbol:"is_symbol \<SS>"
  by (auto simp add: is_symbol_def \<SS>_def is_nonterminal_def startsymbol_dom)

definition is_sentence :: "('a, 'b) sentence \<Rightarrow> bool"
where
  "is_sentence s =  list_all is_symbol s"

definition is_word :: "('a, 'b) sentence \<Rightarrow> bool"
where
  "is_word s = list_all is_terminal s"
   
definition derives1 :: "('a, 'b) sentence \<Rightarrow> ('a, 'b) sentence \<Rightarrow> bool"
where
  "derives1 u v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> is_sentence x
        \<and> is_sentence y
        \<and> (N, \<alpha>) \<in> \<RR>)"  

definition derivations1 :: "(('a, 'b) sentence \<times> ('a, 'b) sentence) set"
where
  "derivations1 = { (u,v) | u v. derives1 u v }"

definition derivations :: "(('a, 'b) sentence \<times> ('a, 'b) sentence) set"
where 
  "derivations = derivations1^*"

definition derives :: "('a, 'b) sentence \<Rightarrow> ('a, 'b) sentence \<Rightarrow> bool"
where
  "derives u v = ((u, v) \<in> derivations)"

definition is_derivation :: "('a, 'b) sentence \<Rightarrow> bool"
where
  "is_derivation u = derives [\<SS>] u"

definition \<L> :: "('a, 'b) sentence set"
where
  "\<L> = { v | v. is_word v \<and> is_derivation v}"

definition \<L>_t::"'b list set" where
"\<L>_t = (map projr )` \<L>"

lemma word_proj[simp]:"is_word b \<Longrightarrow> map (Inr ) (map projr b) = b"
  apply(induction b)
   apply(auto simp add: is_word_def is_terminal_def split: sum.splits)
  done
lemma " map Inr `  \<L>_t =  \<L>"
  apply(auto simp add:  \<L>_def  \<L>_t_def simp del: map_map)
using word_proj 
  by (metis (no_types, lifting) imageI mem_Collect_eq)


  
definition "\<L>\<^sub>P"  :: "('a, 'b) sentence set"
where
  "\<L>\<^sub>P = { u | u v. is_word u \<and> is_derivation (u@v) }"

end

end

