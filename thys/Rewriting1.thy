theory Rewriting1
  imports LocalLexingSpecification Pattern1 DerivationTrees1 DerivationTrees_Ambiguity
  Containers.Containers
begin
text "Grammar Rewriting implementing the rewriting based on patterns as in Pattern1"



text "can this be defined using transitive closure"
(*alternative*)
(*describes patter [A, \<alpha>, \<circ>X\<delta>, alternative_rule]*)
type_synonym ('a, 'b) pattern = "('a, 'b) symbol \<times> ('a, 'b) symbol list \<times> ('a, 'b) symbol list \<times> ('a, 'b) symbol list"


type_synonym ('a, 'c) rule = "('a, 'c) symbol \<times> ('a, 'c) symbol list"

lemma csorted_set_to_list:
  assumes "ID ccompare = Some (c::('a::ccompare)  comparator)"
          "finite s"
  shows"set (csorted_list_of_set (s::('a::ccompare  set))) = s \<and> distinct (csorted_list_of_set (s::('a::ccompare  set)))"
proof -
  have 1:"class.linorder (le_of_comp c) (lt_of_comp c)" using ID_ccompare' [OF assms(1)] comparator.linorder by blast
  show ?thesis using linorder.set_sorted_list_of_set [OF 1 assms(2)] assms(2) 
      linorder.distinct_sorted_list_of_set [OF 1] unfolding csorted_list_of_set_def assms(1) by auto
qed

type_synonym ('a, 'c) assoc_group = "('a, 'c) rule set \<times> bias"
type_synonym ('a, 'c) disambig = "(('a, 'c) rule \<times> ('a, 'c) rule) set"

(*datatype ('a, 'c ) grammar = Grammar (nonterms: "('a, 'c) symbol set") (terms: "('a, 'c) symbol set")(rules:"('a, 'c) rule set") (start: "('a, 'c) symbol") 
*)
type_synonym ('a, 'c ) grammar =  "('a, 'c) symbol set \<times> ('a, 'c) symbol set \<times> 
  ('a, 'c) rule set \<times>('a, 'c) symbol"(*\<NN> \<TT> \<RR> \<SS>*)

type_synonym ('a,'c) recursrel = "(('a,  'c) symbol \<times> ('a, 'c) symbol) set"

fun fresh::"((('a, 'c) symbol) \<Rightarrow> nat option) \<Rightarrow> ('a, 'c) symbol \<Rightarrow> ((('a, 'c) symbol) \<Rightarrow> nat option)"  where
"fresh m s = (if m s = None then  m(s \<mapsto> 1)  else m(s \<mapsto> (the (m s)) + 1))"



fun convert::"nat \<Rightarrow> ('a, 'c) symbol \<Rightarrow> ('a \<times> nat, 'c) symbol" where
"convert a = (case_sum (\<lambda> t. Inl (t, a)) Inr) "

fun convert_back::"('a \<times> nat, 'c) symbol \<Rightarrow> ('a, 'c) symbol" where
"convert_back s= (case_sum (\<lambda> t . Inl (fst t)) Inr) s"

fun convert_back_sentence::"('a \<times> nat, 'c) symbol list\<Rightarrow> ('a, 'c) symbol list" where
"convert_back_sentence l= map convert_back l"
fun basic_convert::"('a, 'c) symbol \<Rightarrow> ('a \<times> nat, 'c ) symbol" where
"basic_convert a = convert 0 a"

fun stage0::"('a, 'c) grammar \<Rightarrow> ('a \<times> nat, 'c) grammar " where
"stage0 (\<NN>, \<TT>, R, s) = (((convert 0) ` \<NN>), ((convert 0) ` \<TT>), ((\<lambda>(n, l). ((convert 0 n), map (convert 0 ) l))` R) ,(convert 0 s))"

context CFG
begin

definition new_nonterm::"('a \<times> nat) set" where
"new_nonterm = ((\<lambda> a. (a, 0))  ` \<A>)"

term case_sum
definition new_term::"'b  set" where
"new_term = \<B>"  

definition rules::"('a \<times> nat,  'b) rule set" where
"rules = ((\<lambda>(n, l). ((convert 0 n), map (convert 0 ) l))` \<RR>)"

definition start::"'a \<times> nat" where
"start =  (\<S>, 0)"

lemma start_valid:"start \<in> new_nonterm"
by (auto simp add: startsymbol_dom  start_def new_nonterm_def)

lemma h1:"(a, b) \<in> local.rules \<Longrightarrow> a \<in> Inl ` (\<lambda>a. (a, 0)) ` \<A>"
proof -
  assume "(a, b) \<in> rules"
  then obtain n  l where n:"(n, l) \<in> \<RR> \<and> (a = (convert 0 n)) \<and> b = map (convert 0) l" using rules_def by auto
  then have "n \<in> Inl ` \<A>" using validRules by blast
  with n have "a  \<in> (convert 0) ` Inl ` \<A>" by blast
  then show ?thesis by auto
qed

lemma h2:"(a, b) \<in> local.rules \<Longrightarrow> s \<in> set b \<Longrightarrow> s \<notin> Inr ` new_term \<Longrightarrow> s \<in> Inl ` (\<lambda>a. (a, 0)) ` \<A> "
proof - 
  assume assms:"(a, b) \<in> rules" "s \<in> set b" "s \<notin> Inr ` new_term"
  then obtain n  l where n:"(n, l) \<in> \<RR> \<and> (a = (convert 0 n)) \<and> b = map (convert 0) l" using rules_def by auto
  then have "\<forall> s \<in> set l . s \<in> (Inl ` \<A>) \<union> (Inr ` \<B>)" using validRules by fast
  with n have "\<forall> s \<in> set b . s \<in> ((convert 0) `(Inl ` \<A>) \<union> (Inr ` \<B>))" by force
  then have "\<forall> s \<in> set b . s \<in> ((convert 0) `(Inl ` \<A>)) \<union> (Inr ` \<B>)" by blast
  then have "\<forall> s \<in> set b . s \<in> (Inl `(\<lambda> a. (a, 0)) ` \<A>) \<union> (Inr ` new_term)" using new_term_def by auto
  with assms show ?thesis by auto 
qed

lemma finite_rules:"finite rules"
  by (auto simp add: finite_grammar rules_def)

interpretation grammar2: CFG new_nonterm new_term rules start
  apply(unfold_locales)
   apply(auto simp add: startsymbol_dom  start_def new_nonterm_def)
     apply(auto simp add: h1 h2 finite_rules)
  apply (auto simp add: new_term_def finite_terminals)
  done

lemma terminal_equality:"grammar2.is_terminal x \<Longrightarrow> is_terminal (convert_back x)"
  apply(auto simp add: grammar2.is_terminal_def is_terminal_def new_term_def)
  by (smt (verit, ccfv_threshold) case_sum_inject disjE_realizer grammar2.is_terminal_def new_term_def surjective_sum)

lemma terminal_equality':"is_terminal x \<Longrightarrow> grammar2.is_terminal (convert 0 x)"
  apply(auto simp add: grammar2.is_terminal_def is_terminal_def new_term_def)
  by (smt (verit, ccfv_threshold) case_sum_inject disjE_realizer grammar2.is_terminal_def new_term_def surjective_sum)

lemma nonterminal_equality:"grammar2.is_nonterminal x \<Longrightarrow> is_nonterminal (convert_back x)"
proof -
  assume "grammar2.is_nonterminal x"
  then have "case_sum (\<lambda> s. s \<in> new_nonterm) (\<lambda> t. False) x"  by (simp add:grammar2.is_nonterminal_def)
  then obtain s where 1:"x  = Inl s \<and> s \<in> ((\<lambda> a. (a, 0))  ` \<A>)" using new_nonterm_def 
    by (metis old.sum.simps(5) old.sum.simps(6) sumE)
  then obtain s' where valid:"s = (s', 0) \<and> s' \<in> \<A>" by blast
  with 1 have "convert_back x = Inl s'" by simp
  with valid  show ?thesis using is_nonterminal_def by simp
qed
(*list all helpers*)

lemma list_all_map:"list_all f (map g b) \<Longrightarrow> list_all (f \<circ> g) b"
  by (simp add: list.pred_map)

lemma list_all_implies:"list_all f b \<Longrightarrow> \<forall> x . (f x\<longrightarrow> g x) \<Longrightarrow> list_all g b"
  using list_all_pos_neg_ex by blast

lemma list_all2_implies:"list_all2 f b b' \<Longrightarrow> \<forall> x y. (f x y\<longrightarrow> g x y) \<Longrightarrow> list_all2 g b b'"
  using list_all2_mono by blast
lemma list_all2_implies_list_all:"list_all2 (\<lambda> x y. f x) b b' \<Longrightarrow> list_all f b" 
proof (induction b arbitrary: b')
  case Nil
  then show ?case by simp
next
  case (Cons a b)
  then obtain x xs where"b' = x#xs" by (meson list_all2_Cons1) 
  with Cons(2) have "(\<lambda>x y. f x) a x \<and>list_all2 (\<lambda>x y. f x) b xs" by blast
  with Cons(1) have "f a \<and> list_all f b" by blast
  then show ?case by simp
qed

lemma nonterminal_equality':"is_nonterminal x \<Longrightarrow> grammar2.is_nonterminal (convert 0 x)"
proof -
  assume "is_nonterminal x"
  then have "case_sum (\<lambda> s. s \<in> \<A>) (\<lambda> t. False) x"  by (simp add: is_nonterminal_def)
  then obtain s where 1:"x  = Inl s \<and> s \<in> \<A>"  
    by (metis old.sum.simps(5) old.sum.simps(6) sumE)
  then obtain s'::"('a \<times> nat)" where valid:"s' = (\<lambda> a. (a, 0)) s \<and> s' \<in> new_nonterm" using new_nonterm_def by blast
  with 1 have "convert 0 x = Inl s'" by simp
  with valid grammar2.is_nonterminal_def  show ?thesis  by fastforce
qed

lemma backconversion:"N = convert_back (convert n N)"
proof (cases N)
  case (Inl a)
  then show ?thesis by simp
next
  case (Inr b)
  then show ?thesis by simp
qed

lemma backconversion_sen:"N = convert_back_sentence (map (convert n) N)"
proof (induction N)
  case Nil
  then show ?case by auto
next
  case (Cons a N)
  have "convert_back_sentence (map (convert n) (a # N)) = (convert_back (convert n a))#N" using Cons by simp
  then show ?case using backconversion by auto
qed

lemma rule_equality:"(N, \<alpha>) \<in> rules \<Longrightarrow> (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>"
proof -
  assume "(N, \<alpha>) \<in> rules"
  then obtain N' \<alpha>' where alt:"N = convert 0 N' \<and> \<alpha> = map (convert 0) \<alpha>' \<and> (N', \<alpha>') \<in> \<RR>" using rules_def by auto
  then have "N' = convert_back N \<and> \<alpha>' = convert_back_sentence \<alpha>" using backconversion backconversion_sen by auto
  with alt show ?thesis by auto
qed

lemma rule_equality':"\<forall> (N, \<alpha>) \<in> \<RR> . (convert 0 N, map (convert 0) \<alpha> ) \<in> rules"
  using rules_def by auto

fun convertback_rule::"('a \<times> nat, 'b) rule \<Rightarrow> ('a, 'b) rule" where
"convertback_rule (N, a) = (convert_back N, convert_back_sentence a)"

lemma convertback_rule_split:"fst (convertback_rule s) = (convert_back (fst s)) 
  \<and> snd (convertback_rule s) = (convert_back_sentence (snd s))"
  apply(cases s) by simp

lemma start_conversion:"convert 0 \<SS> = grammar2.\<SS>"
  using grammar2.\<SS>_def  \<SS>_def local.start_def by auto

lemma start_conversion':"\<SS> = convert_back grammar2.\<SS>"
  using grammar2.\<SS>_def  \<SS>_def local.start_def by auto

lemma equality:"grammar2.Tree_wf T \<Longrightarrow> (s, a) = DeriveFromTree T \<Longrightarrow> \<exists> T'. Tree_wf T' 
  \<and> (convert_back s, convert_back_sentence a) = DeriveFromTree T'"
proof (induction T arbitrary: s a)
  case (Leaf x)
  then have 1:"grammar2.is_terminal x" by simp
  from Leaf(2) have s:"s = x \<and> a = [x]" by simp
  then have a:"convert_back_sentence a = [convert_back x]" by simp
  from 1 have terminal:"is_terminal (convert_back x)" using terminal_equality by blast
  obtain leaf where def:"leaf = (Leaf (convert_back x))" by blast
  with terminal have wf:"Tree_wf leaf" by simp
  from def a s have  "(convert_back s, convert_back_sentence a )= DeriveFromTree leaf" by simp
  with wf show ?case by blast  
next
  case (Inner x)
  then have 1:"grammar2.is_nonterminal x" by simp
  from Inner(2) have s:"s = x \<and> a = [x]" by simp
  then have a:"convert_back_sentence a = [convert_back x]" by simp
  from 1 have terminal:"is_nonterminal (convert_back x)" using nonterminal_equality by blast 
  obtain leaf where def:"leaf = (Inner (convert_back x))" by blast
  with terminal have wf:"Tree_wf leaf" by simp
  from def a s have  "(convert_back s, convert_back_sentence a )= DeriveFromTree leaf" by simp
  with wf show ?case by blast
next
  case (DT r b)
  then have validrule:"r \<in> rules" by auto (*need implication that *)
  obtain N \<alpha> where na:"N = fst r \<and> \<alpha> = snd r" by blast
  with validrule have valid_rule:"(convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>" using rule_equality by auto
  from na have \<alpha>_def:"(map (\<lambda> t . fst (DeriveFromTree t)) b)  = \<alpha>" 
    using DT(2) grammar2.TreeSym_equal_DeriveFrom_root'' by fastforce
  from DT.prems(1) have "snd r = concat (map grammar2.TreeSym b)" by simp (*downright impossible to convert unless ? define specific conversion function*)
  (*just need lemma that derives root is equal to TreeSym*)
  then have "snd r = concat (map (\<lambda> t . [fst (DeriveFromTree t)]) b)" using grammar2.TreeSym_implies_DeriveFrom_root by presburger
  with na have "convert_back_sentence \<alpha> = concat (map (\<lambda> t . [convert_back (fst (DeriveFromTree t))]) b)" by auto
  (*how to apply IH on all subtrees in list?*)
  from DT(2) have "\<forall> i \<in> set b . grammar2.Tree_wf i" by (auto simp add: list_all_def)
  with DT(1) have "\<forall> x \<in> set b .(\<exists>T'. Tree_wf T' \<and> convertback_rule (DeriveFromTree x) 
    = DeriveFromTree T') " by (metis convertback_rule.cases convertback_rule.simps)
  then have "list_all (\<lambda> T . \<exists> T'. Tree_wf T' \<and> convertback_rule (DeriveFromTree T) 
    = DeriveFromTree T') b"  by (simp add:list_all_def)
  then obtain b'' where b'':"list_all2 (\<lambda> T' T . Tree_wf T' \<and> convertback_rule (DeriveFromTree T) 
    = DeriveFromTree T') b'' b" using implied_existence' by fast
  then have "list_all2 (\<lambda> T' T . Tree_wf T') b'' b" using list_all2_implies by fast
  then have wf_subtrees:"list_all Tree_wf b''" using list_all2_implies_list_all by auto
  from b'' have "list_all2  (\<lambda> T' T . convertback_rule (DeriveFromTree T) 
    = DeriveFromTree T') b'' b" using list_all2_implies by fast
  then have "list_all2  (\<lambda> T' T .  
     DeriveFromTree T' = (\<lambda> t. convertback_rule (DeriveFromTree t)) T) b'' b" using list_all2_mono by fastforce
  with list_all2_map2 have 2:"map (\<lambda> t. convertback_rule (DeriveFromTree t)) b = map DeriveFromTree b''" by force
  then have "map fst (map (\<lambda> t. convertback_rule (DeriveFromTree t)) b) = map fst (map DeriveFromTree b'')" by simp
  then have "map (\<lambda> t. fst (convertback_rule (DeriveFromTree t))) b = map (\<lambda> t. fst (DeriveFromTree t)) b''" 
    using map_map [where ?f="fst" and ?g="(\<lambda> t. convertback_rule (DeriveFromTree t))" and ?xs="b"] 
    map_map [where ?f="fst" and ?g="DeriveFromTree" and ?xs="b''"] sorry (*Composition weird*)
  then have "map (\<lambda> t . convert_back (fst (DeriveFromTree t))) b = map (\<lambda> t. fst (DeriveFromTree t)) b''"
    using map_map convertback_rule_split by auto
  then have "map convert_back (map (\<lambda> t . fst (DeriveFromTree t)) b) = map (\<lambda> t. fst (DeriveFromTree t)) b''" 
      using map_map [where ?f="convert_back" and ?g="\<lambda> t. fst (DeriveFromTree t)"] sorry (*again composition*)
  then have valid_subtrees':"convert_back_sentence \<alpha> = concat (map TreeSym b'')" using TreeSym_equal_DeriveFrom_root'' 
    \<alpha>_def by auto  
  from DT.prems(2) have a_def:"a = (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b))" by simp

  from 2 have "map snd (map (\<lambda> t. convertback_rule (DeriveFromTree t)) b) = map snd (map DeriveFromTree b'')" by simp
  then have "map (\<lambda> t. snd (convertback_rule (DeriveFromTree t))) b = map (\<lambda> t. snd (DeriveFromTree t)) b''" 
    using map_map [where ?f="fst"] sorry (*should jus be this rule application*)
  then have subderiv_eq:"map (\<lambda> t . convert_back_sentence (snd (DeriveFromTree t))) b = map (\<lambda> t. snd (DeriveFromTree t)) b''"
    using map_map convertback_rule_split by auto
   then have "map convert_back_sentence (map (\<lambda> t . snd (DeriveFromTree t)) b) = map (\<lambda> t. snd (DeriveFromTree t)) b''" 
      using map_map [where ?f="convert_back" and ?g="\<lambda> t. fst (DeriveFromTree t)"] sorry 
  (*using concat_map or something*)
  from map_concat [where ?f="convert_back" and ?xs="(map (\<lambda> t . snd (DeriveFromTree t)) b)"]
  have "convert_back_sentence a = (concat( map (convert_back_sentence )
     (map (\<lambda>subtree .  (snd (DeriveFromTree subtree))) b)))" 
     by (metis convert_back_sentence.simps map_eq_conv a_def)
  then have deriv:"convert_back_sentence a = (concat( map (\<lambda>subtree . (convert_back_sentence (snd (DeriveFromTree subtree)))) b))" 
     using map_map [where ?f="convert_back_sentence" and ?g="(\<lambda>subtree .  (snd (DeriveFromTree subtree)))" and ?xs="b"] sorry
     (*using \<open>map (\<lambda>t. convert_back_sentence (snd (DeriveFromTree t))) b = map (\<lambda>t. snd (DeriveFromTree t)) b''\<close> 
       \<open>map convert_back_sentence (map (\<lambda>t. snd (DeriveFromTree t)) b) = map (\<lambda>t. snd (DeriveFromTree t)) b''\<close> by presburger
     *)
   then have derive':"convert_back_sentence a = (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b''))" 
     using subderiv_eq by simp
  obtain T' where tree:"T' = (DT (convert_back N, convert_back_sentence \<alpha>) b'')" by blast
  then have wf:"Tree_wf T'" using valid_rule valid_subtrees'  wf_subtrees by auto
   from na have "N = s" using DT.prems(2) by simp
  with tree derive' have "DeriveFromTree T' = (convert_back s, convert_back_sentence a)" by simp
  with wf show ?case by auto
qed

fun convert_tree::"('a \<times> nat, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree" where
"convert_tree (Leaf s) = Leaf (convert_back s)"|
"convert_tree (Inner s) = Inner (convert_back s)"|
"convert_tree (DT r b) = DT (convertback_rule r) (map convert_tree b)"


lemma equality':"Tree_wf T \<Longrightarrow> \<exists> T' . grammar2.Tree_wf T' 
  \<and> T = (convert_tree T') \<and> (fst (DeriveFromTree T')) = convert 0 (fst (DeriveFromTree T)) 
    \<and> (snd (DeriveFromTree T')) = map (convert 0) (snd (DeriveFromTree T)) "
proof (induction T)
  case (Leaf x)
  then have 1:"is_terminal x" by simp
  from 1 have "grammar2.is_terminal (convert 0 x)" using terminal_equality' by blast
  then have 2:"grammar2.Tree_wf (Leaf (convert 0 x))" by simp
  have 3:"convert_back (convert 0 x) = x" by (metis backconversion)
  then show ?case using 2 by fastforce 
next
  case (Inner x)
  then have 1:"is_nonterminal x" by simp
  from 1 have "grammar2.is_nonterminal (convert 0 x)" using nonterminal_equality' by blast
  then have 2:"grammar2.Tree_wf (Inner (convert 0 x))" by simp
  have 3:"convert_back (convert 0 x) = x" by (metis backconversion)
  then show ?case using 2 by fastforce
next
  case (DT r b)
  then have r:"r \<in> \<RR> \<and> snd r = (map (\<lambda> t. (fst (DeriveFromTree t))) b)" 
      by (simp add :TreeSym_equal_DeriveFrom_root'') 
  obtain N \<alpha> where na:"(N, \<alpha>) = r" apply(cases r) by blast
  with r have valid_rule:"(convert 0 N, map (convert 0) \<alpha>) \<in> rules" using rule_equality' by blast
  have convertback:"convertback_rule (convert 0 N, map (convert 0) \<alpha>) = r" using na 
    by (metis backconversion backconversion_sen convertback_rule.simps)
  (*subtrees*)
  from DT(2) have "list_all Tree_wf b" by simp
  then have "list_all ( \<lambda> t. \<exists>T'. grammar2.Tree_wf T' \<and> t = convert_tree T' \<and> 
    fst (DeriveFromTree T') = convert 0 (fst (DeriveFromTree t)) 
      \<and> snd (DeriveFromTree T') = map (convert 0) (snd (DeriveFromTree t))) b" 
    using DT(1) list.pred_mono_strong by force
  then obtain b' where b':"list_all2 ( \<lambda>T' t.  grammar2.Tree_wf T' \<and> t = convert_tree T' \<and> 
    fst (DeriveFromTree T') = convert 0 (fst (DeriveFromTree t))  
    \<and> snd (DeriveFromTree T') = map (convert 0) (snd (DeriveFromTree t)))b' b" using implied_existence' by fast
  then have 1:"list_all grammar2.Tree_wf b'" and 2:"list_all2 ( \<lambda>T' t.   convert_tree T' = t)b' b"
    and 3:"list_all2 ( \<lambda>T' t. fst (DeriveFromTree T') = convert 0 (fst (DeriveFromTree t)) ) b' b"
    and sndderiv:"list_all2 ( \<lambda>T' t. snd (DeriveFromTree T') = map (convert 0) (snd (DeriveFromTree t)) ) b' b"
      apply (metis (no_types, lifting) list_all2_implies_list_all list_all2_implies)
    using b' list_all2_implies apply fast using b' list_all2_implies apply fast using list_all2_implies b' by fast
  from 2 list_all2_map have 4:"map convert_tree b' = b" by blast
  from 3 have "map (\<lambda> t. fst (DeriveFromTree t)) b' = map (\<lambda> t. convert 0 (fst (DeriveFromTree t))) b" 
    by (metis list_all2_map2)
  then have "concat (map grammar2.TreeSym b') = map (convert 0) (map (\<lambda> t. (fst (DeriveFromTree t))) b)"
    using map_map grammar2.TreeSym_equal_DeriveFrom_root'' by simp
  then have subtree_deriv:"concat (map grammar2.TreeSym b') = map (convert 0)  \<alpha>" using na r by auto
  from sndderiv have "map (\<lambda> t. snd (DeriveFromTree t)) b' = map (\<lambda> t. map (convert 0) (snd (DeriveFromTree t))) b" 
    by (metis list_all2_map2)
  then have "(map (\<lambda> t. snd (DeriveFromTree t)) b') = map (\<lambda> t. map (convert 0) (snd (DeriveFromTree t))) b" by blast
  with  map_map have "(map (\<lambda> t. snd (DeriveFromTree t)) b') = map (map (convert 0)) (map (\<lambda> t. (snd (DeriveFromTree t))) b)"
    by auto
  then have "concat (map (\<lambda> t. snd (DeriveFromTree t)) b') = concat (map 
      (map (convert 0)) (map (\<lambda> t. (snd (DeriveFromTree t))) b))" by simp
  with map_concat have final:"concat (map (\<lambda> t. snd (DeriveFromTree t)) b') = map (convert 0) 
    (concat (map (\<lambda> t. snd (DeriveFromTree t)) b))" by metis
  obtain T where T:"T = DT (convert 0 N, map (convert 0) \<alpha>) b'" by blast
  then have wf:"grammar2.Tree_wf T" using valid_rule subtree_deriv 1 by auto
  from convertback 4 T have conv:"convert_tree T = (DT r b)" by simp
  from T na have root:"fst (DeriveFromTree T) = convert 0 (fst (DeriveFromTree (DT r b)))" by auto
  from T na final have deriv:"snd (DeriveFromTree T) = map (convert 0) (snd (DeriveFromTree (DT r b)))" by auto
  then show ?case using wf conv root by auto
qed

lemma terminal_equality2_help:"grammar2.is_terminal x \<Longrightarrow> (is_terminal \<circ> convert_back) x"
  using terminal_equality by simp

lemma grammar2_is_word_implies_is_word:"grammar2.is_word xa \<Longrightarrow> is_word (convert_back_sentence xa)"
  apply(simp add: grammar2.is_word_def is_word_def)
  using terminal_equality2_help list_all_map [where ?f="is_terminal" and ?g="convert_back" and ?b="xa"]
    list_all_implies list.pred_map by blast

lemma grammar2_derivations:
  assumes "grammar2.is_derivation xa"
  shows "is_derivation  (convert_back_sentence xa)"
proof -
  from assms obtain T where" DeriveFromTree T = (grammar2.\<SS>, xa) \<and> grammar2.Tree_wf T" 
    by (auto simp add: grammar2.is_derivation_def dest!: grammar2.derives_implies_Derivation grammar2.DerivationSymbol_implies_DerivTree 
        [OF _ grammar2.\<SS>_symbol])
  then obtain T' where "Tree_wf T' \<and> DeriveFromTree T' = (\<SS>, 
    convert_back_sentence xa)"  by (metis equality start_conversion')
  then show ?thesis using DerivationTree_implies_Derivation 
      Derivation_implies_derives is_derivation_def by fastforce
qed

lemma grammar2_is_word_derivations:"grammar2.is_word xa \<Longrightarrow> grammar2.is_derivation xa \<Longrightarrow>  
  is_derivation (convert_back_sentence xa) \<and> is_word (convert_back_sentence xa)"
  using  grammar2_is_word_implies_is_word grammar2_derivations by auto

lemma terminal_equality2_help':"is_terminal x \<Longrightarrow> (grammar2.is_terminal \<circ> (convert 0)) x"
  using terminal_equality' by simp

lemma is_word_implies_grammar2_is_word:"is_word xa \<Longrightarrow> grammar2.is_word (map (convert 0) xa)"
  apply(simp add: grammar2.is_word_def is_word_def del: convert.simps)
  using terminal_equality2_help' list_all_map [where ?f="grammar2.is_terminal" and ?g="convert 0" and ?b="xa"]
    list_all_implies list.pred_map by blast

lemma word_derivat:
  assumes "DeriveFromTree tree = (\<SS>, xa) " "Tree_wf tree" 
   (*would use completeness lemma*) 
  shows "grammar2.is_derivation  (map (convert 0) xa)" 
proof -
  from assms obtain T' where T':"grammar2.Tree_wf T' 
  \<and> tree = (convert_tree T') \<and> (fst (DeriveFromTree T')) = convert 0 \<SS> \<and> 
    (snd (DeriveFromTree T'))  = map (convert 0) xa" using equality' by force
  then have "DeriveFromTree T'= (grammar2.\<SS>, map (convert 0) xa)" 
    by (metis prod.collapse start_conversion) 
  then show ?thesis using T' grammar2.DerivationTree_implies_Derivation 
      grammar2.Derivation_implies_derives grammar2.is_derivation_def by fastforce
 qed

lemma grammar2_is_word_derivations':"is_word xa \<Longrightarrow> DeriveFromTree tree = (\<SS>, xa)  \<Longrightarrow>Tree_wf tree \<Longrightarrow> 
  grammar2.is_word (map (convert 0)xa ) \<and> grammar2.is_derivation (map (convert 0) xa)"
  using word_derivat is_word_implies_grammar2_is_word by blast

lemma is_word_projr:"is_word xa \<Longrightarrow> map projr xa = map projr (map (convert 0) xa)"
  apply(auto simp add: is_word_def is_terminal_def)
  by (metis old.sum.simps(5) old.sum.simps(6) projr_def sum.exhaust_sel)

lemma is_word_projr':"grammar2.is_word xa \<Longrightarrow> map projr xa = map projr (convert_back_sentence xa)"
  apply(auto simp add: grammar2.is_word_def grammar2.is_terminal_def)
   by (metis old.sum.simps(5) old.sum.simps(6) projr_def sum.exhaust_sel)

theorem grammar2_eq:"grammar2.\<L>_t = \<L>_t" 
 apply(auto simp add: \<L>_t_def grammar2.\<L>_t_def  \<L>_def  grammar2.\<L>_def is_derivation_def 
      dest!: derives_implies_Derivation DerivationSymbol_implies_DerivTree [OF _ \<SS>_symbol])
  using grammar2_is_word_derivations is_word_projr' is_derivation_def apply fast  
  apply(auto simp add: grammar2.is_derivation_def 
        dest!: grammar2.derives_implies_Derivation grammar2.DerivationSymbol_implies_DerivTree  )
  using grammar2_is_word_derivations' is_word_projr grammar2.is_derivation_def by blast

end
(*main invariant of rewriting:*)
end