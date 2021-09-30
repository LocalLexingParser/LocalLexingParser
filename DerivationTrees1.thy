theory DerivationTrees1
  imports  "OperatorAmbiguity" "LocalLexing2.Ladder"  "LocalLexing2.TheoremD6" 
begin
text "extends CFG derivations with derivation trees"

section "supporting lemmas for reasoning on the list of subtrees"
lemma list_all2_map:"list_all2 (\<lambda> x y . f x = y) xs ys \<Longrightarrow> map f xs = ys" 
  by (metis (mono_tags) list.rel_eq list.rel_map(1))

lemma list_all2_map2:"list_all2 (\<lambda> x y . f x = g y) xs ys \<Longrightarrow> map f xs = map g ys" 
  by (simp add: list.rel_map(2) list_all2_map)

lemma list_all_implies_list_all_zip:"length y = length x \<Longrightarrow> 
list_all f x \<Longrightarrow> list_all (\<lambda> (x, y) . f x) (zip x y)"
proof (induct x arbitrary: y)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then have "length y > 0" by force 
  then obtain b ys where y:"y = b#ys" by (meson gr0_implies_Suc length_Suc_conv)
  with Cons have 1:"list_all (\<lambda>(x, y). f x) (zip x ys)" by simp
  have "(\<lambda>x y. f x) a b" using Cons(3) by simp 
  then show ?case using list_all2_Cons1 1 y by simp 
qed

lemma list_all_and:"list_all f x \<Longrightarrow> list_all g x \<Longrightarrow> list_all (\<lambda> y. f y \<and> g y) x"
  by (simp add: list_all_iff)

lemma list_all_implies_list_all2:"length x = length y \<Longrightarrow> 
list_all f x \<Longrightarrow> list_all2 (\<lambda> x y . f x) x y"
proof (induct x arbitrary: y)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then have "length y > 0" by force 
  then obtain b ys where y:"y = b#ys" by (meson gr0_implies_Suc length_Suc_conv)
  with Cons have 1:"list_all2 (\<lambda>x y. f x) x ys" by simp
  have "(\<lambda>x y. f x) a b" using Cons(3) by simp 
  then show ?case using list_all2_Cons1 1 y by simp 
qed

lemma list_all_implies_list_all2':"length x = length y \<Longrightarrow> 
list_all f x \<Longrightarrow> list_all2 (\<lambda> y x. f x) y x"
proof (induct x arbitrary: y)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then have "length y > 0" by force 
  then obtain b ys where y:"y = b#ys" by (meson gr0_implies_Suc length_Suc_conv)
  with Cons have 1:"list_all2 (\<lambda>y x. f x) ys x" by simp
  have "(\<lambda>x y. f x) a b" using Cons(3) by simp 
  then show ?case using list_all2_Cons1 1 y by simp 
qed

lemma list_all_reduce:"list_all (\<lambda> (x, y) . f y) b \<Longrightarrow> list_all f (map snd b)"
  apply(induct b) by auto


lemma list_all2_compose':"list_all2 a x y \<and> list_all2 b x y \<longleftrightarrow> list_all2 (\<lambda> x y. a x y \<and> b x y) x y"
  apply(simp add: list_all2_iff) by fastforce

lemma list_all2_compose:"list_all2 a x y \<Longrightarrow> list_all2 b x y \<Longrightarrow> list_all2 (\<lambda> x y. a x y \<and> b x y) x y"
  apply(simp add: list_all2_iff) by fastforce

lemma list_all2_implies_list_all_fst:"list_all2 (\<lambda> x y. (b x)) x y \<Longrightarrow> list_all b x"
  apply(induct x arbitrary: y) apply auto 
  apply (meson list_all2_Cons1) by (meson list_all2_Cons1) 

lemma list_all2_implies_list_all_snd:"list_all2 (\<lambda> x y. (b y)) x y \<Longrightarrow> list_all b y"
  apply(induct y arbitrary: x) apply auto apply (meson list_all2_Cons2) by (meson list_all2_Cons2) 



section "Subtree Checks"

datatype  ('a, 'b) derivtree =  Leaf "('a, 'b) symbol"  | Inner "('a, 'b) symbol" | DT "('a, 'b) rule"  "(('a, 'b) derivtree) list" 


fun DeriveFromTree::"('a, 'b) derivtree \<Rightarrow> (('a, 'b) symbol \<times> ('a, 'b) sentence)" where
"DeriveFromTree (DT s  l ) = (fst s, (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) l)))"|
"DeriveFromTree (Leaf s) = (s, [s])"|
"DeriveFromTree (Inner s) = (s, [s])"

lemma DT_induct[case_names ProperTree DegTree Leaf]:
  assumes "(\<And>r ts. (\<And>x. x \<in> set ts \<Longrightarrow> P x) \<Longrightarrow> ts \<noteq> [] \<Longrightarrow> P (DT r ts))"
  and "\<And>s. P (DT s [])"
  and "(\<And>l. P (Leaf l))"
  and "(\<And>l. P (Inner l))"
  shows "P t"
  using assms
  by (induction t) blast+

context CFG begin

definition splits_at' :: "('a, 'b) sentence \<Rightarrow> nat \<Rightarrow> ('a, 'b) sentence \<Rightarrow> ('a, 'b) symbol \<Rightarrow> ('a, 'b) sentence \<Rightarrow> bool"
where
  "splits_at' \<delta> i \<alpha> N \<beta> = (i < length \<delta> \<and> \<alpha> = take i \<delta> \<and> N = \<delta> ! i \<and> \<beta> = drop (Suc i) \<delta>)"

lemma splits_at_combine: "splits_at' \<delta> i \<alpha> N \<beta> \<Longrightarrow> \<delta> = \<alpha> @ [N] @ \<beta>"
  by (simp add: id_take_nth_drop splits_at'_def)

lemma splits_at_combine_dest: "Derives1 a i r b \<Longrightarrow> splits_at' a i \<alpha> N \<beta> \<Longrightarrow> b = \<alpha> @ (snd r) @ \<beta>"
  by (metis (no_types, lifting) Derives1_drop Derives1_split append_assoc append_eq_conv_conj 
      length_append splits_at'_def)

lemma Derives1_nonterminal: 
  assumes "Derives1 a i r b"
  assumes "splits_at' a i \<alpha> N \<beta>"
  shows "fst r = N \<and> is_nonterminal N"
proof - 
  from assms have fst: "fst r = N"
    by (metis Derives1_split append_Cons nth_append_length splits_at'_def)
  then have "is_nonterminal N"
    by (metis Derives1_def assms(1) prod.collapse rule_nonterminal_type)
  with fst show ?thesis by auto
qed
lemma Derives1_rule: "Derives1 a i r b \<Longrightarrow> r \<in> \<RR>"
  by (auto simp add: Derives1_def)
  
lemma splits_at_ex: "Derives1 \<delta> i r s \<Longrightarrow> \<exists> \<alpha> N \<beta>. splits_at' \<delta> i \<alpha> N \<beta>"
by (simp add: Derives1_bound splits_at'_def)

lemma splits_at_implies_Derives1: "splits_at' \<delta> i \<alpha> N \<beta> \<Longrightarrow> is_sentence \<delta> \<Longrightarrow> r\<in> \<RR> \<Longrightarrow> fst r = N
 \<Longrightarrow> Derives1 \<delta> i r (\<alpha>@(snd r)@\<beta>)"
by (metis (no_types, lifting) Derives1_def is_sentence_concat length_take 
  less_or_eq_imp_le min.absorb2 prod.collapse splits_at_combine splits_at'_def)

lemma splits_at_append: "splits_at' u i u1 N u2 \<Longrightarrow> splits_at' (u@v) i u1 N (u2@v)"
  using splits_at'_def 
  by (smt (z3) append.assoc append_eq_conv_conj hd_append2 hd_drop_conv_nth le_add1 
      le_eq_less_or_eq length_0_conv length_append length_append_singleton 
      length_drop length_take min.absorb2 not_le splits_at_combine zero_less_diff)

lemma Derives1_append_suffix: 
  assumes Derives1: "Derives1 v i r w"
  assumes u: "is_sentence u"
  shows "Derives1 (v@u) i r (w@u)"   
proof -
  have "\<exists> \<alpha> N \<beta>. splits_at' v i \<alpha> N \<beta>" using assms splits_at_ex by auto
  then obtain \<alpha> N \<beta> where split_v: "splits_at' v i \<alpha> N \<beta>" by blast
  have split_w: "w = \<alpha>@(snd r)@\<beta>" using assms split_v splits_at_combine_dest by blast 
  have split_uv: "splits_at' (v@u) i \<alpha> N (\<beta>@u)"   
    by (simp add: split_v splits_at_append)
  have is_sentence_uv: "is_sentence (v@u)"
    using Derives1 Derives1_sentence1 is_sentence_concat u by blast 
  show ?thesis
    using  Derives1 Derives1_nonterminal Derives1_rule append_assoc is_sentence_uv 
        split_uv split_v split_w splits_at_implies_Derives1 by simp
qed
lemma splits_at_append_prefix:
  "splits_at' v i \<alpha> N \<beta> \<Longrightarrow> splits_at' (u@v) (i + length u) (u@\<alpha>) N \<beta>"
  apply (auto simp add: splits_at'_def)
  by (simp add: nth_append)

lemma Derives1_append_prefix: 
  assumes Derives1: "Derives1 v i r w"
  assumes u: "is_sentence u"
  shows "Derives1 (u@v) (i + length u) r (u@w)"
proof -
  have "\<exists> \<alpha> N \<beta>. splits_at' v i \<alpha> N \<beta>" using assms splits_at_ex by auto
  then obtain \<alpha> N \<beta> where split_v: "splits_at' v i \<alpha> N \<beta>" by blast
  have split_w: "w = \<alpha>@(snd r)@\<beta>" using assms split_v splits_at_combine_dest by blast 
  have split_uv: "splits_at' (u@v) (i + length u) (u@\<alpha>) N \<beta>"
    by (simp add: split_v splits_at_append_prefix)
  with  Derives1 split_v have r:"fst r = N" using Derives1_nonterminal by fast
  have rule:"r \<in> \<RR>" using Derives1 Derives1_rule by fast
  have is_sentence_uv: "is_sentence (u@v)"
    using Derives1 Derives1_sentence1 is_sentence_concat u by blast 
  
  with split_uv rule split_w r  show ?thesis using  splits_at_implies_Derives1 by fastforce
qed

lemma Derivation_append_prefix: "Derivation v D w \<Longrightarrow> is_sentence u \<Longrightarrow>
  Derivation (u@v) (derivation_shift D 0 (length u)) (u@w)"
proof (induct D arbitrary: u v w)
  case Nil thus ?case by auto
next
  case (Cons d D)
    then have "\<exists> x. Derives1 v (fst d) (snd d) x \<and> Derivation x D w" by auto
    then obtain x where x: "Derives1 v (fst d) (snd d) x \<and> Derivation x D w" by blast
    with Cons have induct: "Derivation (u@x) (derivation_shift D 0 (length u)) (u@w)" by auto
    have Derives1: "Derives1 (u@v) ((fst d) + length u) (snd d) (u@x)"
      by (simp add: Cons.prems(2) Derives1_append_prefix x) 
    show ?case 
      apply simp
      apply (rule_tac x="u@x" in exI)
      by (simp add: Cons.hyps Cons.prems(2) Derives1 x)
qed     

end


context CFG begin

fun is_leaf::"('a, 'b) derivtree \<Rightarrow> bool" where
"is_leaf (DT _  d) =  ([]= d)"|
"is_leaf (Leaf _) = True"|
"is_leaf (Inner _) = True"

fun TreeRoot::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) symbol" where
"TreeRoot (DT s _ ) = fst s"|
"TreeRoot (Leaf s) = s"|
"TreeRoot (Inner s ) = s"

fun isTree::"('a, 'b) derivtree \<Rightarrow> bool" where
"isTree (Leaf _ ) = False"|
"isTree _ = True"

fun subtrees1::"('a, 'b) derivtree \<Rightarrow> ('a, 'b)derivtree list" where
"subtrees1 (DT s l) = l"|
"subtrees1 _ = []"

fun subtrees::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree list" where
"subtrees (DT s l) = ((DT s l)#(concat( map (\<lambda>sub . (subtrees sub)) l)))"|
"subtrees d = [d]" 

(*should subtree be reflexive or not? \<Longrightarrow> probably yes*)
fun is_subtree::"('a, 'b) derivtree \<Rightarrow> ('a, 'b)derivtree  \<Rightarrow> bool" where
"is_subtree (DT s l) d= (if (d \<in> set l) then True else  True \<in> set (map (\<lambda> s. is_subtree s d) l))"|
"is_subtree d _= False"

fun TreeSym::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) symbol list" where
"TreeSym (DT s _ ) = [fst s]"|
"TreeSym (Inner s) = [s]"|
"TreeSym (Leaf s) = [s]"

lemma TreeSym_equal_DeriveFrom_root:"(s, a) = DeriveFromTree T \<Longrightarrow> TreeSym T = [s]"
proof (induction T)
  case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT x1a x2a)
  then show ?case by auto
qed

lemma TreeSym_equal_DeriveFrom_root':"s = [fst (DeriveFromTree T)] \<Longrightarrow> TreeSym T = s"
proof (induction T)
case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT x1a x2a)
  then show ?case by auto
qed


lemma TreeSym_equal_DeriveFrom_root'':"map (\<lambda> t . fst (DeriveFromTree t)) b = concat (map TreeSym b)"
  apply(induct b) apply simp
  using TreeSym_equal_DeriveFrom_root' by simp

lemma TreeSym_implies_DeriveFrom_root:"TreeSym T = x \<Longrightarrow> x = [fst (DeriveFromTree T)]"
proof (induction T)
case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT x1a x2a)
then show ?case by auto
qed

(*Traversal Functions*)
primrec preorder ::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) symbol list" where
"preorder (Leaf s) = [s]" |
"preorder (Inner s) = [s]" |
"preorder (DT s l) = concat (map preorder l)" 

(*approach parallel to Derivation to add by replacing inner*)
primrec split::"('a, 'b) derivtree \<Rightarrow> nat" where 
"split (Leaf s) = 1" |
"split (Inner s) = 1" |
"split (DT s l) = fold (+) (map split l) 0"

primrec contains::"nat \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> ('a, 'b) symbol \<Rightarrow> bool" where
"contains n (Leaf s) s'= (if n = 0 then s = s' else False)" |
"contains n (Inner s) s'= (if n = 0 then s = s' else False)" |
"contains n (DT s l) s'= False"

(*
primrec foldTree::"('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (symbol \<Rightarrow> 'b) \<Rightarrow> (symbol \<Rightarrow> 'b)  \<Rightarrow> 'b \<Rightarrow> derivtree \<Rightarrow> 'b" where
"foldTree f f_leaf f_inner b (Leaf s) = f_leaf s"|
"foldTree f f_leaf f_inner b (Inner s) = f_inner s"|
"foldTree f f_l f_i b (DT s l) = (fold (\<lambda>t b'. f (foldTree f f_l f_i b' t) b')  l b)"
*)

lemma deriv_simp:"DT r s = DT r' s' \<Longrightarrow> r' = r \<and> s = s'"
  using derivtree.inject by auto
(* (\<forall> t \<in> set l . Tree_valid  t)) *)
fun Tree_wf::"('a, 'b) derivtree \<Rightarrow> bool" where
"Tree_wf (DT s l) = ((snd s=  concat (map TreeSym l)) \<and> (s \<in> \<RR> ) \<and> list_all Tree_wf l)"|
"Tree_wf (Leaf s) = is_terminal s"|
"Tree_wf (Inner s) = is_nonterminal s"


(*how to best handle this? because a derivtree changes only one nonterminal to something, whereas arbitrary left derivations could *)

fun Tree_wf1::"('a, 'b) derivtree \<Rightarrow> bool" where
"Tree_wf1 (DT s l) = ((snd s=  concat (map (\<lambda>s. [fst (DeriveFromTree s )]) l)) \<and> (s \<in> \<RR> ) \<and> list_all Tree_wf1 l)"|
"Tree_wf1 (Leaf s) = is_terminal s"|
"Tree_wf1 (Inner s) = is_nonterminal s"


fun TreeDerives::"('a, 'b) symbol \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> ('a, 'b) sentence \<Rightarrow> bool" where
"TreeDerives s T sen = ((s, sen) = DeriveFromTree T)"

fun TreeDerives1::"('a, 'b) sentence \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> ('a, 'b) sentence \<Rightarrow> bool" where
"TreeDerives1 u T v = (\<exists> x y N \<alpha>. u = x@[N]@y \<and> is_word x \<and> is_sentence y \<and> DeriveFromTree T = (N, \<alpha>))"

fun tree_deriv::"('a, 'b) derivation \<Rightarrow> bool" where
"tree_deriv [] = True" |
"tree_deriv ((n,s,r)#D) = snd (foldr (\<lambda>(n',s',r') (n'', b). (if n' \<le> n'' then (n' + length r', b) else (n', False))) D (n + length r, True))"

(*tree insertion function needed as helper for insertion*)
fun tree_insert::"('a, 'b) derivtree \<Rightarrow> nat list \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> ('a, 'b)derivtree" where
"tree_insert d _ (Leaf s) = d"|
"tree_insert (DT (s, r) st) (n#N) d' = (if n > length r then  (DT (s, r) st)  else
(if (is_nonterminal (r!n)) then ( (DT (s, r) (list_update st n (tree_insert (st !n) N d')))) else (DT (s, r) st)))" |
"tree_insert (DT (s, r) st) []  _ = (DT (s, r) st)"|
"tree_insert (Inner s) [] (DT (s', r') st') = (if s = s' then (DT (s',r') st') else (Inner s))"|
"tree_insert (Inner s) _ _ = (Inner s)"|
"tree_insert (Leaf s) n st = Leaf s"

lemma DeriveFromTreeDT_root_nonterm:"Tree_wf1 (DT s l) \<Longrightarrow> is_nonterminal (fst (DeriveFromTree (DT s l)))"
  apply(simp add: is_nonterminal_def)
  using validRules by auto

lemma DeriveFromTreeLeaf_root_terminal:"Tree_wf1 (Leaf s) \<Longrightarrow> is_terminal (fst (DeriveFromTree (Leaf s)))"
  by auto

lemma DeriveFromTreeInner_root_nonterminal:"Tree_wf1 (Inner s) \<Longrightarrow> is_nonterminal (fst (DeriveFromTree (Inner s)))"
  by auto

lemma DeriveFromTree_root_symbol:"Tree_wf1 d \<Longrightarrow> is_symbol (fst (DeriveFromTree (d)))"
proof(induction d)
  case (Leaf x)
  then have "is_terminal (fst (DeriveFromTree (Leaf x)))" using DeriveFromTreeLeaf_root_terminal by blast
  then show ?case using is_symbol_def by blast
next
  case (Inner x)
  then have "is_nonterminal (fst (DeriveFromTree (Inner x)))" using DeriveFromTreeInner_root_nonterminal by blast
  then show ?case using is_symbol_def by blast
next
  case (DT x1a x2a)
  then have "is_nonterminal (fst (DeriveFromTree (DT x1a x2a)))" using DeriveFromTreeDT_root_nonterm by blast
  then show ?case by auto
qed

(*Tree Construction Lemmas*)
(*unused*)
(*
lemma tree_append1:"(DeriveFromTree (DT (s, r) l) = (s, \<alpha>)) \<Longrightarrow> (DeriveFromTree (t) = (s', \<alpha>')) \<Longrightarrow> 
  \<exists> u v . u@[s']@v = r \<Longrightarrow> DeriveFromTree (DT (s, r) l'') = (s,  u@\<alpha>'@v)"
  *)
(*do only one level replacement, and can try to use this inductively*)
(*crucial lemma for following*)
(*
lemma subtrees_subderivations:"(DeriveFromTree (DT r l) = (s, \<alpha>)) \<Longrightarrow> s' \<in> set \<alpha> \<Longrightarrow>
 \<exists> t u' u v v' . u'@ u@[s']@v@v' = \<alpha> \<and>(DeriveFromTree t  = (s'', u@[s']@v))"
  apply(auto)
  
*) 
lemma append_prepend_nil: " s = s' \<and> u = [] \<and> v = [] \<Longrightarrow> [s] = u@[s']@v"
  by(auto)
lemma append_prepend_nil1: "[s] = u@[s']@v \<Longrightarrow> s = s' \<and> u = [] \<and> v = [] "
  by (simp add: Cons_eq_append_conv)
(*
lemma subtrees_deriv1:"(preorder (DT r l) = \<alpha>) \<Longrightarrow>  \<forall>s' \<in> set \<alpha> . \<exists> d \<in> set (subtrees (DT r l)) . preorder d= [s']"
proof (induction arbitrary: \<alpha> rule: DeriveFromTree.induct )
  case(2 s)
  from this have s0:"\<alpha> = [s] " by auto
  from this have s1:"set \<alpha> = {s}" by auto
  from 2 and s0 have p:"DeriveFromTree (Leaf s) = (s, [s])" by auto
  have refl:"(Leaf s) \<in> set (subtrees (Leaf s))" by auto
  from p and refl have "\<exists> x \<in> set (subtrees (Leaf s)). DeriveFromTree (x) = (s, [s])" by auto
  from this and s1 have "\<forall>s' \<in> set \<alpha> . \<exists> x \<in> set (subtrees (Leaf s)). DeriveFromTree (x) = (s', [s'])" by auto
  from this show ?case by auto
next
  case(3 s)
  from this have s0:"\<alpha> = [s]" by auto
  from this have s1:"set \<alpha> = {s}" by auto
  from 3 and s0 have p:"DeriveFromTree (Inner s) = (s, [s])" by auto
  have refl:"(Inner s) \<in> set (subtrees (Inner s))" by auto
  from p and refl have "\<exists> x \<in> set (subtrees (Inner s)). DeriveFromTree (x) = (s, [s])" by auto
  from this and s1 have "\<forall>s' \<in> set \<alpha> . \<exists> x \<in> set (subtrees (Inner s)). DeriveFromTree (x) = (s', [s'])" by auto
  from this show ?case by auto
next
  case(1 s l)
  from this have "\<forall> s \<in> set \<alpha> . \<exists> x \<in> set l . s \<in> set (preorder x)" by auto
  from this have s0:"s' \<in> set \<alpha> \<Longrightarrow> \<exists> x \<in> set l . s' \<in> set (preorder x)" by (drule bspec)
  from this obtain x' where s1:"s' \<in> set \<alpha> \<Longrightarrow> x'\<in> set l" and s2:"s' \<in> set \<alpha> \<Longrightarrow> s' \<in> set (preorder x')" by blast
  from this and 1 have "s' \<in> set \<alpha> \<Longrightarrow> \<exists> d \<in> set (subtrees x') . preorder  d =  [s']" by auto
  from s1 and this have "s' \<in> set \<alpha> \<Longrightarrow> \<exists> d \<in> set (subtrees(DT s l)) . preorder  d =  [s']" by auto
  from this have "\<forall>s' \<in> set \<alpha> . \<exists> d \<in> set (subtrees(DT s l)) . preorder  d =  [s']" 
  from this show ?case by auto
qed
*)

(*
lemma replace_nonterminal:"(preorder (DT r l) = \<alpha>) \<Longrightarrow>  \<forall>s' \<in> set \<alpha> . \<exists> d \<in> set (subtrees (DT r l)) . preorder d= [s']"


lemma Tree_append:"(DeriveFromTree (DT r l) = (s, \<alpha>)) \<Longrightarrow> (DeriveFromTree (t) = (s', \<alpha>')) \<Longrightarrow>
  \<exists> u v . u@[s']@v = \<alpha> \<Longrightarrow> DeriveFromTree (DT r l'') = (s,  u@\<alpha>'@v)"
  apply(induction rule: DeriveFromTree.induct)
     
*)
end
context CFG
begin

lemma list_all_implies:"list_all f b \<Longrightarrow> \<forall> x . (f x\<longrightarrow> g x) \<Longrightarrow> list_all g b"
  using list_all_pos_neg_ex by blast


(*possible use LeftDerivationFix or something similar to construct trees (trees exist for all LeftDerivationIntros*)
fun symbol_to_tree::"('a, 'b) symbol \<Rightarrow> ('a, 'b) derivtree" where
"symbol_to_tree s = (if is_terminal s then (Leaf s) else (Inner s))"
fun deconstruct_rule::"('a, 'b) rule \<Rightarrow> ('a, 'b) derivtree" where
"deconstruct_rule r = DT r (map symbol_to_tree (snd r))"

lemma symbol_to_tree_id:"(\<lambda> s .(snd (DeriveFromTree (symbol_to_tree s))))s = [s]"
  by simp

lemma symbol_to_tree_id':"concat (map (\<lambda> s .(snd (DeriveFromTree (symbol_to_tree s))))xs) = xs"
  using symbol_to_tree_id by simp

lemma symbol_to_tree_id'':"concat (map (\<lambda> s .(snd (DeriveFromTree s))) (map symbol_to_tree xs)) = xs"
  using symbol_to_tree_id' arg_cong [OF map_map [where ?f="(\<lambda> s 
  .snd (DeriveFromTree s))" and ?g="symbol_to_tree"]
  , where ?f="concat" and ?xs1="xs"] o_def [where ?f="(\<lambda> s 
  .snd (DeriveFromTree s))" and ?g="symbol_to_tree"] by simp  
  

lemma deconstruct_derive:"(DeriveFromTree (deconstruct_rule r)) = r"
  using symbol_to_tree_id'' by auto

lemma validRules1:"r \<in> \<RR> \<Longrightarrow> \<forall> x \<in> set (snd r) .  x \<in> \<NN> \<union> \<TT>" 
  apply(insert validRules)
  apply(drule bspec)
   apply simp
  apply(auto simp add: snd_def \<NN>_def \<TT>_def)
  done

lemma validRules2:"r \<in> \<RR> \<Longrightarrow>
          xa \<in> set (snd r) \<Longrightarrow>
          \<not> (case xa of Inl t \<Rightarrow> False | Inr s \<Rightarrow> s \<in> \<B>) \<Longrightarrow> case xa of Inl s \<Rightarrow> s \<in> \<A> | Inr t \<Rightarrow> False"
  apply(insert validRules)
  apply(drule bspec)
   apply(simp)
  apply(auto simp add: snd_def)
  done
  
lemma TreeSym_singleton:"[r] = (TreeSym \<circ> symbol_to_tree) r"
  by auto
lemma TreeSym_singleton1:" (TreeSym \<circ> symbol_to_tree) = (\<lambda> x . [x])"
  by auto

lemma Tree_sym_sym_to_tree_id:"r =  concat (map (TreeSym \<circ> symbol_to_tree) (r))" 
  by (auto simp add: TreeSym_singleton1)
 
lemma deconstruct_derive_valid:"r \<in> \<RR> \<Longrightarrow>Tree_wf (deconstruct_rule r)"
  apply(auto)
   apply(auto simp add: is_nonterminal_def is_word_def is_terminal_def list_all_def)
  using Tree_sym_sym_to_tree_id apply fastforce
  using validRules2 by fast  

(*Default Tree of rule*)
lemma Derives1ex_Tree:
  assumes  "Derives1 [s] 0 r \<alpha>" and "is_nonterminal s"
  shows "\<exists> tree . Tree_wf tree \<and> (DeriveFromTree tree) = (s, \<alpha>)"
proof -
  from assms have valid:"r \<in> \<RR> \<and> s = fst r" by (auto simp add: Derives1_def)
  from assms have "snd r = \<alpha>" by (auto simp add: Derives1_def)
  from this and valid have "r = (s, \<alpha>)" by auto
  from this and valid show ?thesis apply(rule_tac x="deconstruct_rule r" in exI)  
    using deconstruct_derive_valid  deconstruct_derive by auto
qed


fun derivation_to_tree::"('a, 'b) derivation \<Rightarrow> ('a, 'b) derivtree" where
"derivation_to_tree (d#D)= deconstruct_rule (snd d)"|
"derivation_to_tree [] = undefined" (*maybe Inner?*)

lemma Derives1_Tree:
  assumes  "Derives1 [s] 0 r \<alpha>" and "is_nonterminal s"
  shows "Tree_wf (deconstruct_rule r) \<and> (DeriveFromTree (deconstruct_rule r)) = (s, \<alpha>)"
proof -
  from assms have valid:"r \<in> \<RR> \<and> s = fst r" by (auto simp add: Derives1_def)
  from assms have "snd r = \<alpha>" by (auto simp add: Derives1_def)
  from this and valid have "r = (s, \<alpha>)" by auto
  from this and valid show ?thesis  using deconstruct_derive_valid using deconstruct_derive by auto
qed



lemma DerivationsAppend:
  "is_sentence a \<Longrightarrow> is_sentence a'\<Longrightarrow>Derivation a D b \<Longrightarrow> Derivation a' D' b' \<Longrightarrow> \<exists> D''. Derivation  (a@a') D'' (b@b')
      \<and> length D'' = length D' + length D "
proof(induction D arbitrary: a b)
  case Nil
  from this have "a = b" by auto
  from Nil and this have "Derivation (a@a') (derivation_shift D' 0 (length a)) (b@b')" using Derivation_append_prefix by fast
  from this show ?case by auto
next
  case (Cons d D)
  then have "\<exists> x. Derives1 a (fst d) (snd d) x \<and> Derivation x D b" by auto
  then obtain x where x: "Derives1 a (fst d) (snd d) x \<and> Derivation x D b" by blast
  then have 1:"is_sentence x " by auto
  from  Cons(1)[OF 1 Cons(3)] x Cons(5) have 
    induct0:"\<exists> D'' . Derivation (x@a') D'' (b@b') \<and> length D'' = length D' + length D" by blast
  then obtain D'' where induct1:"Derivation (x@a') D'' (b@b') 
    \<and> length D'' = length D' + length D" by  blast
  from x and Cons  have "Derives1 (a@a') (fst d) (snd d) (x@a')" by (simp add:Derives1_append_suffix)
  with induct1 have "Derivation (a@a') (d#D'') (b@b') \<and>  length (d#D'') = length D' + length (d#D)" by auto
  then show ?case by fast
qed

(*
lemma Derivation_implies_is_sentence:"Derivation a D b \<Longrightarrow> is_sentence a"
*)
(*provable in local lexing \<Longrightarrow> should one try to shift things into CFG?*)
(*
lemma Derivation_concat:"Derivation v D w \<Longrightarrow> Derivation v' D' w' 
  \<Longrightarrow> \<exists> D''. Derivation (v@v') D'' (w@w')"
 *)
lemma list_all_hd:"list_all is_sentence (l#s) \<Longrightarrow> is_sentence l" 
  by simp

lemma list_all_tl:"list_all is_sentence (l#s) \<Longrightarrow> list_all is_sentence s" 
  by simp

lemma list_all_take:"list_all f b \<Longrightarrow> list_all f (take n b)"
  apply (simp add:list_all_def) by (meson in_set_takeD)


lemma list_all_drop:"list_all f b \<Longrightarrow> list_all f (drop n b)"
  apply (simp add:list_all_def) by (meson in_set_dropD)


lemma is_sentence_concat':"list_all is_sentence l \<Longrightarrow> is_sentence (concat l)"
  apply(induct l) apply simp using is_sentence_concat by simp


lemma DerivationAppend:"list_all is_sentence s_m \<Longrightarrow>  length s_m = length \<alpha>_m \<Longrightarrow>list_all2 
  (\<lambda> D (s, a) . Derivation s D a) D (zip s_m \<alpha>_m) \<Longrightarrow> \<exists> D' . Derivation (concat s_m) D' (concat \<alpha>_m)"
proof (induction D arbitrary:s_m \<alpha>_m)
  case Nil
  then have "(zip s_m \<alpha>_m) = []" by blast
  then have "s_m =  [] \<and>  \<alpha>_m = []" by (metis length_greater_0_conv zip_eq_Nil_iff Nil(2))
  then have "Derivation (concat s_m) [] (concat \<alpha>_m)" by simp
  then show ?case by blast
next
  case (Cons a D)
  from Cons(4) have 1:"(\<lambda> D (s, a) . Derivation s D a) a ((hd s_m), (hd \<alpha>_m)) 
  \<and> list_all2 (\<lambda> D (s, a) . Derivation s D a) D (zip (tl s_m) (tl \<alpha>_m)) " using list_all2_Cons1 
    by (smt (verit, del_insts) case_prod_conv hd_Cons_tl 
        list.distinct(1) list.rel_inject(2) zip_Cons_Cons zip_eq_Nil_iff)
  have len_tl:"length (tl s_m) = length (tl \<alpha>_m)" using Cons by simp
  have "set (tl s_m) \<subseteq> set s_m" apply(cases s_m) apply simp by auto
  then have tl_sentence:"list_all is_sentence (tl s_m)" using Cons(2) list_all_def by (metis subsetD)
  with 1 Cons(1) len_tl obtain D' where tl:"Derivation (concat (tl s_m)) D' (concat (tl \<alpha>_m))" by blast
  from 1 have hd:"Derivation (hd s_m) a (hd \<alpha>_m)" by simp
  from Cons have "length s_m > 0" by auto
  then have  hd':"is_sentence (hd s_m)" apply(cases s_m) apply simp using Cons(2) by simp
  from tl_sentence have tl':"is_sentence (concat (tl s_m))" using is_sentence_concat' by blast
  from hd  have 2:"\<exists> D'' . Derivation ((hd s_m)@(concat (tl s_m))) D'' ((hd \<alpha>_m)@(concat (tl \<alpha>_m)))"
    using DerivationsAppend [OF hd' tl'] tl by blast 
  from Cons have "length s_m > 0 \<and> length \<alpha>_m > 0" by auto
  then have "concat s_m = (hd s_m)@(concat (tl s_m)) \<and> concat \<alpha>_m = (hd \<alpha>_m)@(concat (tl \<alpha>_m))" 
    by (metis concat.simps(2) hd_Cons_tl length_greater_0_conv) 
  then show ?case using 2 by auto
qed

lemma hd_is_symbol:"is_sentence (a#m) \<Longrightarrow> is_symbol a"
  using is_sentence_def by simp 

lemma DerivationAppend':"is_sentence s_m \<Longrightarrow>  length s_m = length \<alpha>_m 
  \<Longrightarrow> list_all2 (\<lambda>D (s, a). Derivation [s] D a) D (zip s_m \<alpha>_m) \<Longrightarrow> 
  \<exists> D' . Derivation s_m D' (concat \<alpha>_m) \<and> length D' = length (concat D)"
proof (induction D arbitrary:s_m \<alpha>_m)
  case Nil
  then have "(zip s_m \<alpha>_m) = []" by blast
  then have "s_m =  [] \<and>  \<alpha>_m = []" by (metis length_greater_0_conv zip_eq_Nil_iff Nil(2))
  then have 1:"Derivation s_m [] (concat \<alpha>_m)" by simp
  have "length [] = length (concat [])" by simp
  with 1 show ?case by blast
next
  case (Cons a D)
  from Cons(4) have 1:"(\<lambda> D (s, a) . Derivation [s] D a) a ((hd s_m), (hd \<alpha>_m)) 
  \<and> list_all2 (\<lambda> D (s, a) . Derivation [s] D a) D (zip (tl s_m) (tl \<alpha>_m)) " using list_all2_Cons1 
    by (smt (verit, del_insts) case_prod_conv hd_Cons_tl 
        list.distinct(1) list.rel_inject(2) zip_Cons_Cons zip_eq_Nil_iff)
  have len_tl:"length (tl s_m) = length (tl \<alpha>_m)" using Cons by simp
  have "set (tl s_m) \<subseteq> set s_m" apply(cases s_m) apply simp by auto
  then have tl_sentence:"list_all is_symbol (tl s_m)" 
    using Cons(2) list_all_def is_sentence_def  by (metis subsetD)
  then have tl':"is_sentence (tl s_m)" by (simp add: is_sentence_def)
  with 1 Cons(1) len_tl obtain D' where tl:"Derivation (tl s_m) D' (concat (tl \<alpha>_m)) 
    " and tl_len:" length D' = length (concat D)" by blast 
  from 1 have hd:"Derivation [(hd s_m)] a (hd \<alpha>_m)" by simp
  from Cons have "length s_m > 0" by auto
  with Cons(2) have "is_symbol (hd s_m)" using hd_is_symbol by (metis length_greater_0_conv list.collapse)
  then have  hd':"is_sentence [(hd s_m)]" using is_sentence_def by simp
  
  have "\<exists> D'' . Derivation ((hd s_m)#(tl s_m)) D'' ((hd \<alpha>_m)@(concat (tl \<alpha>_m))) 
      \<and>  length D'' = length D' + length a"
    using DerivationsAppend [OF hd' tl' hd tl] by simp
  with tl_len have 2:"\<exists> D'' . Derivation ((hd s_m)#(tl s_m)) D'' ((hd \<alpha>_m)@(concat (tl \<alpha>_m))) 
      \<and>  length D'' = length (concat (a#D))" by auto
  from Cons have "length s_m > 0 \<and> length \<alpha>_m > 0" by auto
  then have "s_m = (hd s_m)#(tl s_m) \<and> concat \<alpha>_m = (hd \<alpha>_m)@(concat (tl \<alpha>_m))" 
    by (metis concat.simps(2) hd_Cons_tl length_greater_0_conv) 
  then show ?case using 2 by auto
qed


lemma implied_existence':"list_all (\<lambda> x . \<exists>y. P x y) b
  \<Longrightarrow> \<exists> D'. list_all2 (\<lambda> y x  . P x y)  D' b"
proof (induction b)
  case Nil
  then show ?case by blast
next
  case (Cons a b)
  then obtain  x where hd:"P a x" by auto
  from Cons have "list_all (\<lambda>x. \<exists>y. P x y) b" by simp
  with Cons(1) obtain D' where "list_all2 (\<lambda> y x . P x y) D' b"  by auto
  then show ?case using hd by blast
qed

lemma is_sentence_hd:"is_sentence (a # u) \<Longrightarrow> is_sentence [a]" 
  using is_sentence_def by simp
lemma is_sentence_split:"is_sentence u  \<Longrightarrow> s' = map (\<lambda> a . [a]) u \<Longrightarrow> list_all is_sentence s'"
  apply(induct u arbitrary:s') apply simp using is_sentence_hd by (simp add: is_sentence_cons) 

lemma "list_all2 (\<lambda>y x. (case x of (x, y) \<Rightarrow> \<lambda>d. Derivation x d y) y) D' (zip s' \<alpha>') \<Longrightarrow>
   list_all2 (\<lambda>D (s, a). Derivation s D a) D' (zip s' \<alpha>')"
  by(auto intro: list_all2_mono)
  

lemma DerivationSplit:"Derivation s D \<alpha>  \<Longrightarrow>
  \<exists> s' D' \<alpha>' . concat \<alpha>' = \<alpha> \<and>  s' = map (\<lambda> a . [a]) s\<and> length \<alpha>' = length s' \<and> list_all2 
  (\<lambda> D (s, a) . Derivation s D a) D' (zip s'  \<alpha>')"
proof (induction D arbitrary: s)
  case Nil
  then have 1:"s = \<alpha>" by simp
  then obtain \<alpha>' s' where 2:"\<alpha>' = map (\<lambda> a . [a]) \<alpha>" and 3:"s' = map (\<lambda> a . [a]) s" 
      by auto
  then have 4:"concat \<alpha>' = \<alpha> \<and> length \<alpha>' = length s'"  by (auto simp add: 1)
  with 1 3 2 have "(\<forall>(x, y) \<in> set (zip s' \<alpha>').  x =  y)" by (metis list_eq_iff_zip_eq)
  then have 5:"(\<forall>(x, y) \<in> set (zip s' \<alpha>') .  Derivation x [] y)" by simp
    then have 5:"(\<forall>(x, y) \<in> set (zip s' \<alpha>') . (\<exists> d. Derivation x d y))" by blast

  then have "list_all (\<lambda> (x, y). (\<exists> d . Derivation x d y))(zip s' \<alpha>')" using Ball_set_list_all 
    by auto
  then have "list_all (\<lambda>x. \<exists>y. (case x of (x, y) \<Rightarrow> \<lambda>d. Derivation x d y) y) (zip s' \<alpha>')" 
    by(auto simp add: list_all_def)
  then obtain D' where  "list_all2 (\<lambda> D (s, a) . Derivation s D a) D' (zip s'  \<alpha>')" 
       using implied_existence' 
      [where ?b="(zip s' \<alpha>')" and ?P="\<lambda>(x, y) d. Derivation x d y"] by (auto intro: list_all2_mono) (*case resolution*)
  then show ?case using 4 3 by auto
next
  case (Cons a D)
  from Cons have "\<exists> x .Derives1 s (fst a) (snd a) x \<and> Derivation x D \<alpha>" by auto 
  then obtain u  where 1:"Derives1 s (fst a) (snd a) u" and 2:"Derivation u D \<alpha>" by blast
  from 1 have u_is_sentence:"is_sentence u" by auto
  from 2 Cons obtain s' D' \<alpha>' where  3:"s' = map (\<lambda> a . [a]) u \<and> concat \<alpha>' = \<alpha> \<and> 
  length \<alpha>' = length s' \<and>list_all2 (\<lambda> D (s, a) . Derivation s D a) D' (zip s' \<alpha>')" by metis(*using a take *)
  (*split Derives 1*)
  with u_is_sentence have s'_is_sentence:"list_all is_sentence s'" using is_sentence_split by blast 
  from 1 obtain x y N r where l:"s = x @ [N] @ y
        \<and> u = x @ r @ y \<and> is_sentence x
        \<and> is_sentence y
        \<and> (N, r) \<in> \<RR>
        \<and> (snd a) = (N, r) \<and> (fst a) = length x" using Derives1_def by auto
  (*using a take drop lemma*)
  then have 4:"Derives1 [N] 0 (N, r) r" using Derives1_def by auto
  obtain n_prefix where n:"n_prefix = length x" using l by simp
  (*prefix*)
  from 3 obtain D_pref s_pref \<alpha>_pref  where prefix:"\<alpha>_pref = take n_prefix \<alpha>' \<and>
    D_pref = take n_prefix D' \<and> s_pref = take n_prefix s'" by simp
  then have prefix_situation:"s_pref = take n_prefix (map (\<lambda> a . [a]) u)  \<and> list_all2 
  (\<lambda> D (s, a) . Derivation s D a) D_pref (zip s_pref \<alpha>_pref)" by (metis take_zip  3 list_all2_takeI) 
  (*postfix*)
  obtain n_postfix where n':"n_postfix = length x + length r" using l by simp
  from 3 obtain D_post s_post \<alpha>_post  where postfix:"\<alpha>_post = drop n_postfix \<alpha>' \<and>  
    D_post = drop n_postfix D' \<and> s_post = drop n_postfix s'" by simp
  then have post_fix_situation:"s_post = drop n_postfix (map (\<lambda> a . [a]) u)  \<and> list_all2 
  (\<lambda> D (s, a) . Derivation s D a) D_post (zip s_post \<alpha>_post)" 
    by (metis 3 drop_zip  list_all2_dropI )
  (*middle*)
  from 3 obtain D_m s_m \<alpha>_m  where middle:"\<alpha>_m = take (length r) (drop n_prefix \<alpha>') \<and>  
    D_m = take (length r) (drop n_prefix D') \<and> s_m = take (length r) (drop n_prefix s')" by simp
  then have middle_situation:"s_m = take (length r) (drop n_prefix (map (\<lambda> a . [a]) u))  \<and> list_all2 
  (\<lambda> D (s, a) . Derivation s D a) D_m (zip s_m \<alpha>_m)" 
    by (metis 3 drop_zip take_zip list_all2_dropI list_all2_takeI)
  with n l have "s_m  = (map (\<lambda> a . [a]) r)" by auto
  (*from the postfix situation*)
   from middle postfix prefix have "\<alpha>_pref@\<alpha>_m@\<alpha>_post = \<alpha>'" using n n' 
    by (metis append.assoc append_take_drop_id take_add) 
  then have concat:"concat (\<alpha>_pref@[(concat \<alpha>_m)]@\<alpha>_post) = \<alpha>" using 3 by auto(*holds by length etc*)
  (*use concatenation of derivations*)
  from middle have len:"length \<alpha>_m = length s_m" using 3 by simp
  from middle have "set s_m \<subseteq> set s'" by (metis set_drop_subset set_take_subset subset_trans)
  then have middle_is_sentence:"list_all is_sentence s_m" by (metis subset_eq s'_is_sentence list_all_def )
  from middle_situation have "concat s_m = r" using l n by auto
  then obtain D' where "Derivation r  D' (concat \<alpha>_m)" 
    using DerivationAppend [OF middle_is_sentence] len middle_situation by fastforce
  with 4 have "Derivation [N] ((0, (N, r))#D') (concat \<alpha>_m)" by auto
  then have "list_all2 (\<lambda> D (s, a) . Derivation s D a) [((0, (N, r))#D')] (zip [[N]] [concat \<alpha>_m])" by simp
  then have "
  list_all2 (\<lambda> D (s, a) . Derivation s D a) ((D_pref)@[((0, (N, r))#D')]@D_post) ((zip s_pref \<alpha>_pref)
  @(zip [[N]] [concat \<alpha>_m])@(zip s_post \<alpha>_post))"  
    by (metis  post_fix_situation prefix_situation list_all2_appendI)
  then have deriv:"list_all2 (\<lambda> D (s, a) . Derivation s D a) ((D_pref)@[((0, (N, r))#D')]@D_post)
    (zip (s_pref@[[N]]@s_post) (\<alpha>_pref@[concat \<alpha>_m]@\<alpha>_post))" 
    by (auto simp add: 3 postfix prefix) (*need length too*)

  have len':"length (s_pref@[[N]]@s_post) = length (\<alpha>_pref@[concat \<alpha>_m]@\<alpha>_post)"
    by (auto simp add: 3 postfix prefix)
  from prefix postfix  3 have "s_pref = take n_prefix (map (\<lambda> a . [a]) u)" by blast
  then have s0:"s_pref = (map (\<lambda> a . [a]) x)" using take_map l n by simp
   from prefix postfix n' 3 l have "s_post = drop n_postfix(map (\<lambda> a . [a]) u)" by blast
   then have s1:"s_post = (map (\<lambda> a . [a]) y)" using drop_map l n' by simp
   have s2:" [[N]]= map (\<lambda> a . [a]) [N]" by simp 
   from s0 s1 s2  l have " s_pref@[[N]]@s_post = (map (\<lambda> a . [a]) s)" by auto   
  then show ?case using deriv concat len' by metis
qed

(*might be unnecessary*)
lemma length_concat:"length (concat (drop n D)) \<le> length (concat D) \<and>  length (concat (take n D)) \<le> length (concat D)"
proof -
  have "(take n D)@(drop n D) = D" by simp
  then have "length (concat (take n D)) + length (concat (drop n D)) = length (concat D)" 
    by (metis  concat_append length_append) 
  then show ?thesis by simp
qed

lemma concat_empty:"list_all (\<lambda> d. d = []) D \<Longrightarrow> concat D = []"
  apply(induct D) apply simp by simp

lemma list_map_eq_iff_zip_f_eq:"map f x = y \<Longrightarrow> length x = length y \<and> 
  (\<forall> (x', y') \<in> (set (zip x y)) . f x' = y')"
proof (induct x arbitrary: y)
  case Nil
  then show ?case by auto
next
  case (Cons a x)
  obtain y ys where 1:"map f (a#x) = y#ys" by simp
  then have "map f x = ys" by simp 
  with Cons have 2:"length x = length ys \<and> 
  (\<forall> (x', y') \<in> (set (zip x ys)) . f x' = y')" by simp
  have "f a = y" using 1 by auto
  then have "(\<forall> (x', y') \<in> (set (zip (a#x) (y#ys))) . f x' = y')" using 2 by force
  then show ?case using 1 using Cons.prems by force
qed

lemma DerivationSplit':"Derivation s D \<alpha>  \<Longrightarrow>
  \<exists> D' \<alpha>' . concat \<alpha>' = \<alpha> \<and> length \<alpha>' = length s \<and> list_all2 
  (\<lambda> D (s, a) . Derivation [s] D a) D' (zip s  \<alpha>') 
  \<and> list_all (\<lambda> D' .  length D' \<le> length D) D' 
  \<and> length (concat D') = length D"
proof (induction D arbitrary: s)
  case Nil
  then have 1:"s = \<alpha>" by simp
  then obtain \<alpha>' where 2:"\<alpha>' = map (\<lambda> a . [a]) \<alpha>"  
      by auto
  then have 4:"concat \<alpha>' = \<alpha> \<and> length \<alpha>' = length s"  by (auto simp add: 1)
  with 1 2 have "(\<forall>(x, y) \<in> set (zip s \<alpha>').  [x] =  y)" using list_map_eq_iff_zip_f_eq by fast 
  then have 5:"(\<forall>(x, y) \<in> set (zip s \<alpha>') .  Derivation [x] [] y)" by simp
  then have 5:"(\<forall>(x, y) \<in> set (zip s \<alpha>') . (\<exists> d. Derivation [x] d y \<and> d = []))" by blast
  then have "list_all (\<lambda> (x, y). (\<exists> d . Derivation [x] d y \<and> d = []))(zip s \<alpha>')" using Ball_set_list_all 
    by auto
  then have "list_all (\<lambda>x. \<exists>y. (case x of (x, y) \<Rightarrow> \<lambda>d. Derivation [x] d y \<and> d = []) y) (zip s \<alpha>')" 
    by (auto simp add: list_all_def)
  then obtain D' where  "list_all2 (\<lambda> D (s, a) . Derivation [s] D a \<and>  D = []) D' (zip s  \<alpha>')" 
    using implied_existence' 
      [where ?b="(zip s \<alpha>')" and ?P="\<lambda>(x, y) d. Derivation [x] d y \<and> d = []"] 
      by (auto intro: list_all2_mono)   (*case resolution*)
  then have 6:"list_all2 (\<lambda> D (s, a) . Derivation [s] D a) D' (zip s  \<alpha>')" 
      and "list_all2 (\<lambda> D (s, a) .  D = []) D' (zip s  \<alpha>')" 
    using list_all2_compose' [where ?a= "(\<lambda> D (s, a) . Derivation [s] D a)" and ?b="(\<lambda> D (s, a) . D = [])"]
    by (auto intro: list_all2_mono) (*case resolution?*)
  then have 7:"list_all (\<lambda> d . d = []) D'"  using 
      list_all2_implies_list_all_fst [where ?b="(\<lambda> d . d = [])" and ?y=" (zip s \<alpha>')"] by (auto intro: list_all2_mono)  (*case resolution*)
  then have 8:"concat D' = []" using concat_empty by blast
  from 7 have 9: "list_all (\<lambda> D' .length D' \<le>  length []) D'" using list_all_implies by simp 
  from 8 have "length (concat D') = length []" by auto
  with 4 6 9 have "concat \<alpha>' = \<alpha> \<and> length \<alpha>' = length s \<and> list_all2 (\<lambda>D (s, a). Derivation [s] D a) D' (zip s \<alpha>')
    \<and> list_all (\<lambda>D'. length D' \<le> length []) D'
    \<and> length (concat D') = length []" by simp
  then show ?case by blast
next
  case (Cons a D)
  from Cons have "\<exists> x .Derives1 s (fst a) (snd a) x \<and> Derivation x D \<alpha>" by auto 
  then obtain u  where 1:"Derives1 s (fst a) (snd a) u" and 2:"Derivation u D \<alpha>" by blast
  from 1 have u_is_sentence:"is_sentence u" by auto
  from 2 Cons obtain  D' \<alpha>' where  3:"concat \<alpha>' = \<alpha> \<and> 
  length \<alpha>' = length u \<and>list_all2 (\<lambda> D (s, a) . Derivation [s] D a) D' (zip u \<alpha>')
    \<and> list_all (\<lambda>D'. length D' \<le> length D) D' \<and> length (concat D') = length D" 
    by metis
  from 1 obtain x y N r where l:"s = x @ [N] @ y
        \<and> u = x @ r @ y \<and> is_sentence x
        \<and> is_sentence y
        \<and> (N, r) \<in> \<RR>
        \<and> (snd a) = (N, r) \<and> (fst a) = length x" using Derives1_def by auto
  (*using a take drop lemma*)
  then have 4:"Derives1 [N] 0 (N, r) r" using Derives1_def by auto
  obtain n_prefix where n:"n_prefix = length x" using l by simp
  (*prefix*)
  from 3 obtain D_pref s_pref \<alpha>_pref  where prefix:"\<alpha>_pref = take n_prefix \<alpha>' \<and>
    D_pref = take n_prefix D' \<and> s_pref = take n_prefix u" by simp
  then have prefix_situation:"list_all2 
  (\<lambda> D (s, a) . Derivation [s] D a) D_pref (zip s_pref \<alpha>_pref)" 
    by (metis take_zip  3 list_all2_takeI [where ?n="n_prefix"] prefix)
  (*prefix length*)
  from prefix 3 have  ass:"list_all (\<lambda>D' .length D' \<le>  length D) D_pref" 
    using list_all_take by blast
  then have pre_len:"list_all (\<lambda>D'. length D' \<le> length (a#D)) D_pref" using list_all_implies by force
  

  (*postfix*)
  obtain n_postfix where n':"n_postfix = length x + length r" using l by simp
  from 3 obtain D_post s_post \<alpha>_post  where postfix:"\<alpha>_post = drop n_postfix \<alpha>' \<and>  
    D_post = drop n_postfix D' \<and> s_post = drop n_postfix u" by simp
  then have post_fix_situation:"list_all2 
  (\<lambda> D (s, a) . Derivation [s] D a) D_post (zip s_post \<alpha>_post)" 
    by (metis 3 drop_zip  list_all2_dropI)
  (*postfix length*)
  from postfix 3 have  ass:"list_all (\<lambda>D' .length D' \<le>  length D) D_post" 
    using list_all_drop by blast
  then have post_len:"list_all (\<lambda>D'. length D' \<le> length (a#D)) D_post" using list_all_implies by force
  
(*middle*)
  from 3 obtain D_m s_m \<alpha>_m  where middle:"\<alpha>_m = take (length r) (drop n_prefix \<alpha>') \<and>  
    D_m = take (length r) (drop n_prefix D') \<and> s_m = take (length r) (drop n_prefix u)" by simp
  then have middle_situation:" list_all2 
  (\<lambda> D (s, a) . Derivation [s] D a) D_m (zip s_m \<alpha>_m)" 
    by (metis 3 drop_zip take_zip list_all2_dropI list_all2_takeI)
  (*middle length*)
  from middle 3 have  ass:"list_all (\<lambda>D'. length D' \<le> length D) D_m" 
    using list_all_drop list_all_take by blast
  then have middle_len:"list_all (\<lambda>D'. length D' \<le> length (a#D)) D_m" using list_all_implies by fastforce
  
    (*something like this, that the split preserves the number of derivations*)
  from 3 middle have middle_concat:"length (concat D_m) \<le> length D" using length_concat 
    by (metis le_trans)

  from  n l middle have s_m_r:"s_m =  r" by auto
  (*from the postfix situation*)
   from middle postfix prefix have "\<alpha>_pref@\<alpha>_m@\<alpha>_post = \<alpha>'" using n n' 
    by (metis append.assoc append_take_drop_id take_add) 
  then have concat:"concat (\<alpha>_pref@[(concat \<alpha>_m)]@\<alpha>_post) = \<alpha>" using 3 by auto(*holds by length etc*)
  (*use concatenation of derivations*)
  from middle have len:"length \<alpha>_m = length s_m" using 3 by simp
  from middle have "set s_m \<subseteq> set u" by (metis set_drop_subset set_take_subset subset_trans)
  then have middle_is_sentence:"list_all is_symbol s_m" 
    by (metis subset_eq u_is_sentence list_all_def is_sentence_def)

  from l have is_sentence_r:"is_sentence r" using rule_\<alpha>_type by blast
  from len s_m_r have len':"length r = length \<alpha>_m" by simp
  (*combine middle *)
  from s_m_r obtain D'' where D'':"Derivation r  D'' (concat \<alpha>_m) \<and> length D'' = length (concat D_m)"
    using DerivationAppend' [OF is_sentence_r len']  middle_situation by blast (*to be altered*)
  (*have to encode that DerivationAppend actually ensures length to be smaller*)
  then have middle_length:"length D'' \<le> (length D)" using middle_concat by simp  (*this has to come from middle somehow*)
  
  from D'' 4 have "Derivation [N] ((0, (N, r))#D'') (concat \<alpha>_m)" by auto
  then have "list_all2 (\<lambda> D (s, a) . Derivation [s] D a) [((0, (N, r))#D'')] (zip [N] [concat \<alpha>_m])" 
      by simp
  then have "
  list_all2 (\<lambda> D (s, a) . Derivation [s] D a) ((D_pref)@[((0, (N, r))#D'')]@D_post) ((zip s_pref \<alpha>_pref)
  @(zip [N] [concat \<alpha>_m])@(zip s_post \<alpha>_post))"  
    using  post_fix_situation prefix_situation list_all2_appendI by metis
  then have deriv:"list_all2 (\<lambda> D (s, a) . Derivation [s] D a) ((D_pref)@[((0, (N, r))#D'')]@D_post)
    (zip (s_pref@[N]@s_post) (\<alpha>_pref@[concat \<alpha>_m]@\<alpha>_post))" 
    using  3 postfix prefix by simp(*need length too*)

  from middle_length have "length ((0, (N, r))#D'') \<le> length (a#D)" by auto
  then have "list_all (\<lambda>D'. length D' \<le> length (a # D)) [((0, (N, r))#D'')]" using list_all_def by simp
  then have len:"list_all (\<lambda>D'. length D' \<le> length (a # D)) ((D_pref)@[((0, (N, r))#D'')]@D_post)"
    using pre_len post_len by simp

  from middle prefix n n' have "D_pref@D_m = take n_postfix D'" by (simp add: take_add)
  with postfix  have "D_pref@D_m@D_post=  D'" by (metis append.assoc append_take_drop_id) 
  then have "length (concat (D_pref)) + 
      length (concat D_post) + length (concat (D_m)) = length (concat D')" by auto
      (*check for statement over D'*)
  with 3 have D_eq_sub:"length (concat (D_pref)) + 
      length (concat D_post) + length (concat (D_m)) = length D" by simp
  have a:"length (((0, (N, r))#D'')) = length (concat D_m) + 1 " using D'' by auto
  have "length (concat ((D_pref)@[((0, (N, r))#D'')]
        @D_post)) = length (concat (D_pref)) + length ((0, (N, r))#D'') + length (concat D_post)" by simp
  then have  concat':"length (concat ((D_pref)@[((0, (N, r))#D'')]@D_post)) = length (a # D)" 
    using D_eq_sub a by simp

  have len':"length (s_pref@[N]@s_post) = length (\<alpha>_pref@[concat \<alpha>_m]@\<alpha>_post)"
    using  3 postfix prefix by simp
  from prefix postfix  3 have "s_pref = take n_prefix u" by auto
  then have s0:"s_pref = x" using take_map l n by simp
  from prefix postfix n' 3 l have "s_post = drop n_postfix  u" by blast
  then have s1:"s_post =  y" using drop_map l n' by simp
  have s2:" [N]=  [N]" by simp 
  from s0 s1 s2  l have " s_pref@[N]@s_post = s" by auto   
  
  then show ?case using deriv concat len' len concat' by metis
qed


lemma list_all2_Px_D:"list_all2 P xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists> y \<in> set ys . P x y"
  apply(induction  xs ys rule: list.rel_induct)
  by auto
(*how do we imply that there exist trees that fill all nonterminals such that *)

lemma DerivationSymbol_implies_DerivTree:
  shows "Derivation [s] D \<alpha> \<Longrightarrow> is_symbol s \<Longrightarrow>\<exists> tree . (DeriveFromTree tree) = (s, \<alpha>) \<and> Tree_wf tree"
proof (induct "length D" arbitrary: s \<alpha> D  rule:nat_less_induct)
  case 1
  then show ?case 
  (*Base Case*)
  proof (cases "length D = 0")
    case True
    then have "D = []" by simp
    with 1  have alph:"\<alpha> = [s]" by auto
    {assume "is_terminal s"
      with alph have "(DeriveFromTree (Leaf s)) = (s, \<alpha>) \<and> Tree_wf (Leaf s)" by simp
    }
    then have nonterm:"is_terminal s \<Longrightarrow> DeriveFromTree (Leaf s) = (s, \<alpha>) \<and> Tree_wf (Leaf s)" by simp
    {assume "is_nonterminal s"
      with alph have "(DeriveFromTree (Inner s)) = (s, \<alpha>) \<and> Tree_wf (Inner s)" by simp
    }
  then have terminal:"is_nonterminal s \<Longrightarrow> DeriveFromTree (Inner s) = (s, \<alpha>) \<and> Tree_wf (Inner s)" by simp
  with nonterm 1(3) show ?thesis apply (auto simp add: is_symbol_def) using nonterm 
     apply blast using terminal by blast
next
  (*Induction Step*)
    case False
    then obtain d D'' where D''_def:"d#D'' = D" by (metis derivation_to_tree.cases length_0_conv)
    with 1  have "\<exists> x .Derives1 [s] (fst d) (snd d) x \<and> Derivation x D'' \<alpha>" by auto 
  then obtain x where 0:"Derives1 [s] (fst d) (snd d) x" and 2:"Derivation x D'' \<alpha>" by blast 
  (*need additional ordering lemma*)
  from 0 have valid:"x = snd (snd d) \<and> (snd d) \<in> \<RR> \<and> s = fst (snd d)" 
    using Derives1_def  append_prepend_nil1 by fastforce
  from valid have "is_sentence x" apply(cases "snd d") using 2 by simp
  then have x:"list_all is_symbol x" using is_sentence_def by simp
  with 2 obtain  D' \<alpha>' where deriv_split:"concat \<alpha>' = \<alpha>  \<and> 
  length x = length \<alpha>' " and  deriv_split':"list_all2 (\<lambda> D (s, a) . Derivation [s] D a) D' (zip x \<alpha>')"
    and deriv_split_smaller:"list_all (\<lambda>D'. length D' \<le> length D'') D'"
    using DerivationSplit' by metis
  then have lenD':"length D'  = length (zip x \<alpha>')" using list_all2_lengthD by blast 
  (*smaller condition*)
  from deriv_split_smaller have "list_all (\<lambda>D'. length D' < length D) D'" 
    using list_all_implies D''_def by fastforce
  then have D'_length:"list_all (\<lambda> (D', (s, a)). length D' < length D) (zip D' (zip x \<alpha>'))" using lenD' 
    list_all_implies_list_all_zip [where ?x="D'" and ?y="(zip x \<alpha>')" and ?f="(\<lambda>D'. length D' < length D)"]
    by(auto simp add: list_all_def) (*case resoltuion again*)

  have "(\<lambda> D (s, a) . ((\<lambda> D (s, a) .  is_symbol s) D (s, a)) \<and> 
    ((\<lambda> D (s, a) . Derivation [s] D a \<and> is_symbol s) D (s, a))) = 
    (\<lambda> D (s, a). Derivation [s] D a \<and> is_symbol s)" by auto
  from deriv_split have "list_all (\<lambda> (s, a) .  is_symbol s)  (zip x \<alpha>')" using list_all_implies_list_all_zip
    x by metis
  then have is_symb:"list_all2 (\<lambda> D (s, a) .  is_symbol s) D' (zip x \<alpha>')" using x 
    using lenD' list_all_implies_list_all2' by metis 
  then have "list_all2 (\<lambda> D (s, a) . Derivation [s] D a \<and> is_symbol s) D' (zip x \<alpha>')" 
    using list_all2_compose [OF deriv_split' is_symb] (*case resolution*) by (auto intro: list_all2_mono)
  then have prev4:"list_all (\<lambda> (D, (s, a)). Derivation [s] D a \<and> is_symbol s) (zip D' (zip x \<alpha>'))" 
    by (simp add: list_all_def list_all2_iff) 
  then have 4:"list_all (\<lambda> (D', (s, a)). Derivation [s] D' a \<and> is_symbol s \<and> length D' < length D) (zip D' (zip x \<alpha>'))" 
    using list_all_and [OF prev4 D'_length] by (auto simp add: list_all_def) (*case resolution*) 
  from 1 have "\<forall>x xa xb.  length x < length D  \<longrightarrow>
            Derivation [xa] x xb \<longrightarrow> is_symbol xa \<longrightarrow> 
      (\<exists>tree. DeriveFromTree tree = (xa, xb) \<and> Tree_wf tree)" by blast
  then have 5:"\<forall> x .(\<lambda> (D', (s, a)). Derivation [s] D' a \<and> is_symbol s \<and> length D' < length D) x
         \<longrightarrow>(\<lambda> (D, (s, a)). \<exists> t . DeriveFromTree t = (s, a) \<and> Tree_wf t) x" by blast
  have "list_all (\<lambda> (D, (s, a)). \<exists> t . DeriveFromTree t = (s, a) \<and> Tree_wf t) (zip D' (zip x \<alpha>'))" 
    using list_all_implies [OF 4 5]  by blast
  then have "list_all (\<lambda> (s, a). \<exists> t . DeriveFromTree t = (s, a) \<and> Tree_wf t) (map snd (zip D' (zip x \<alpha>')))" 
    using list_all_reduce [where ?f="\<lambda> (s, a) . \<exists> t . DeriveFromTree t = (s, a) \<and> Tree_wf t" 
        and ?b="(zip D' (zip x \<alpha>'))"] by blast
  then have "list_all (\<lambda> (s, a). \<exists> t . DeriveFromTree t = (s, a) \<and> Tree_wf t) (zip x \<alpha>')" 
    using zip_eq_conv [OF lenD'] by force
  then have " list_all (\<lambda>x. \<exists>y. (case x of (s, a) \<Rightarrow> \<lambda>t. DeriveFromTree t = (s, a) \<and> Tree_wf t) y) (zip x \<alpha>')"
    by (auto simp add: list_all_def)
  then obtain b'' where b'':"list_all2 (\<lambda> t (s, a). DeriveFromTree t = (s, a) \<and> Tree_wf t) b'' (zip x \<alpha>')"
    using implied_existence' 
       [where ?b="zip x \<alpha>'" and ?P="(\<lambda> (s, a) t. DeriveFromTree t = (s, a) \<and> Tree_wf t)"]  by (auto intro: list_all2_mono) (*case *)
  from b'' have "list_all2 (\<lambda> t (s, a). DeriveFromTree t = (s, a)) b'' (zip x \<alpha>') \<and> list_all Tree_wf b''"
    using list_all2_compose' [where ?a=" (\<lambda>t (s, a). DeriveFromTree t = (s, a)) " 
         and ?b=" (\<lambda>t (s, a). Tree_wf t)"] list_all2_implies_list_all_fst [where ?b="Tree_wf"] 
    by (auto simp add: list_all_def  intro: list_all2_mono dest:list_all2_Px_D)    (*case*)

  
  then have subtrees:"list_all Tree_wf b'' \<and> map (DeriveFromTree) b'' = zip x \<alpha>'" using list_all2_map by auto
  then have "map fst (map DeriveFromTree b'') = x \<and> map snd (map DeriveFromTree b'') = \<alpha>'" 
      using deriv_split by force
  then have 2:"(map (\<lambda> t. (fst (DeriveFromTree t))) b'') = x \<and>
  (map (\<lambda> t. snd (DeriveFromTree t)) b'') = \<alpha>'" 
    by force
  then have subtrees_deriv:"concat (map (\<lambda> t. snd (DeriveFromTree t)) b'') = \<alpha>" using deriv_split by simp
  from 2 have 3:"concat (map TreeSym b'') = x" 
    by (metis (no_types, lifting) TreeSym_equal_DeriveFrom_root' concat_map_singleton map_eq_conv)
  obtain T where "T = DT (snd d) b''" by blast
  then have "Tree_wf T \<and> DeriveFromTree T = (s, \<alpha>)" using valid subtrees_deriv 3 subtrees by simp
  then show ?thesis by blast
  qed
qed

(*Lemma connecting trees to derivations*)

lemma implied_existence:"list_all (\<lambda> x . \<exists>D. Derivation [fst (DeriveFromTree x)] D (snd (DeriveFromTree x))) b
  \<Longrightarrow> \<exists> D'. list_all2 (\<lambda> tree D . Derivation [fst (DeriveFromTree tree)] D 
  (snd (DeriveFromTree tree))) b  D'"
proof (induction b)
  case Nil
  then show ?case by blast
next
  case (Cons a b)
  then obtain  D where hd:"Derivation [fst (DeriveFromTree a)] D (snd (DeriveFromTree a))" by auto
  from Cons have "list_all (\<lambda>x. \<exists>D. Derivation [fst (DeriveFromTree x)] D (snd (DeriveFromTree x))) b" by simp
  with Cons(1) obtain D' where "list_all2 (\<lambda> tree D . Derivation [fst (DeriveFromTree tree)] D 
  (snd (DeriveFromTree tree))) b  D'" by blast
  then show ?case using hd by blast
qed

lemma DerivationTree_implies_Derivation_helper:
"list_all2 (\<lambda>tree D. Derivation [fst (DeriveFromTree tree)] D (snd (DeriveFromTree tree))) b D' 
\<Longrightarrow>list_all2 (\<lambda>D (s, a). Derivation s D a) D' (zip (map (\<lambda>t. [fst (DeriveFromTree t)]) b) 
  (map (\<lambda>t. snd (DeriveFromTree t)) b))"
proof (induct D' arbitrary: b)
  case Nil
  then show ?case by simp
next
  case (Cons a D')
  then have "length b = length (a#D')" using list_all2_conv_all_nth by blast
  then obtain x xs where l:"b=x#xs" by (metis length_Suc_conv)
  with Cons have "Derivation [fst (DeriveFromTree x)] a (snd (DeriveFromTree x))" by blast
  from l Cons have "list_all2 (\<lambda>D (s, a). Derivation s D a) D' 
  (zip (map (\<lambda>t. [fst (DeriveFromTree t)]) xs) (map (\<lambda>t. snd (DeriveFromTree t)) xs))" by simp
  then show ?case using l Cons by simp
qed

lemma Tree_wf_implies_is_sentence:"Tree_wf t \<Longrightarrow> is_sentence [fst (DeriveFromTree t)]"
proof (induct t)
  case (Leaf x)
  then have "is_symbol x" by auto
  then have "is_sentence [x]" using is_sentence_def by simp
  then show ?case by auto
next
  case (Inner x)
  then have "is_symbol x" by auto
  then have "is_sentence [x]" using is_sentence_def by simp
  then show ?case by auto
next
  case (DT r b)
  then have "is_symbol (fst r)" using validRules is_nonterminal_def by auto
  then show ?case using is_sentence_def by simp
qed


(*need theorem reordering now, as the derivation based proof relies on LocalLexing*)
lemma DerivationTree_implies_Derivation:
  shows "Tree_wf tree \<Longrightarrow> \<exists> D. Derivation [fst (DeriveFromTree tree)] D 
  (snd (DeriveFromTree tree))"
proof (induct tree)
  case (Leaf x)
  then have "[fst (DeriveFromTree (Leaf x))] =  
  (snd (DeriveFromTree (Leaf x)))" by auto
  then have "Derivation [fst (DeriveFromTree (Leaf x))] []  
  (snd (DeriveFromTree (Leaf x)))" by auto
  then show ?case by blast
next
  case (Inner x)
  then have "[fst (DeriveFromTree (Inner x))] =  
  (snd (DeriveFromTree (Inner x)))" by auto
  then have "Derivation [fst (DeriveFromTree (Inner x))] []  
  (snd (DeriveFromTree (Inner x)))" by auto
  then show ?case by blast
next
  case (DT r b)
  then have 1:"r \<in> \<RR> \<and> list_all Tree_wf b \<and> fst (DeriveFromTree (DT r b)) = fst r" by simp
  from DT have match:"snd r = map (\<lambda> t. fst (DeriveFromTree t)) b \<and> 
    snd (DeriveFromTree (DT r b)) = concat ( map (\<lambda> t. snd( DeriveFromTree t)) b)" 
    by (metis (no_types, lifting) DeriveFromTree.simps(1) TreeSym_equal_DeriveFrom_root' 
        Tree_wf.simps(1) concat_map_singleton map_eq_conv snd_conv)
  (*from those subtres*)
  from 1 have "list_all (\<lambda> x . \<exists>D. Derivation [fst (DeriveFromTree x)] D 
    (snd (DeriveFromTree x))) b" using list.pred_mono_strong DT(1) 1  by force
  then obtain D' where D':"list_all2 (\<lambda> tree D . Derivation [fst (DeriveFromTree tree)] D 
  (snd (DeriveFromTree tree))) b  D'"  using implied_existence by presburger (*list_all obtain?*)
  obtain b' b'' where helper:"b' = (map (\<lambda> t. [fst (DeriveFromTree t)])b) 
  \<and> b'' = (map (\<lambda> t. snd (DeriveFromTree t))b) \<and> length b' = length b''" by simp
  have helper':"concat b' = (map (\<lambda> t. fst (DeriveFromTree t))b)" by (simp add: helper)
  from 1 have "\<forall> i \<in> set b . Tree_wf i" using list_all_def by metis
  then have "\<forall> s \<in> set b' . \<exists> t \<in> set b . s = [fst (DeriveFromTree t)] \<and> Tree_wf t"
      using helper by auto 
    with  Tree_wf_implies_is_sentence have "\<forall> s \<in> set b' . is_sentence s" by auto
  then have is_sentence:"list_all is_sentence b'" using list_all_def by metis
  from helper  D' have "list_all2 (\<lambda>D (s, a). Derivation s D a) D' (zip b' b'')"
    using DerivationTree_implies_Derivation_helper by fastforce
  then obtain D''  where  "Derivation (map (\<lambda> t. fst (DeriveFromTree t)) b) D'' 
  (concat ( map (\<lambda> t. snd( DeriveFromTree t)) b))" using DerivationAppend [OF is_sentence] helper helper' 
    by force
  then have 2:"Derivation (snd r) D'' (snd (DeriveFromTree (DT r b)))" by (simp add: match)
  from 1 have 3:"Derives1 [(fst r)] 0 r (snd r)" using Derives1_def 
    by (metis append_Nil2 is_sentence_def length_0_conv list_all_simps(2) prod.collapse self_append_conv2)
  with 2 have "Derivation [(fst r)] ((0, r)#D'') (snd (DeriveFromTree (DT r b)))" by auto 
  then show ?case using 1 by metis
qed

lemma DeriveFromTree_implies_is_derivation:"DeriveFromTree tree = (\<SS>, xa) \<Longrightarrow> Tree_wf tree \<Longrightarrow> is_derivation xa"
  by (metis DerivationTree_implies_Derivation  Derivation_implies_derives fst_conv is_derivation_def snd_conv)

lemma is_derivation_implies_DeriveFromTree:"is_derivation x \<Longrightarrow> \<exists> tree . DeriveFromTree tree = (\<SS>, x) \<and> Tree_wf tree"
  apply(auto simp add: is_derivation_def dest!: derives_implies_Derivation) 
  using DerivationSymbol_implies_DerivTree \<SS>_symbol by blast

lemma Derives1_symbol_0:"Derives1 [s] l r x \<Longrightarrow> l = 0"
  by (metis Derives1_split append_prepend_nil1 length_0_conv)

lemma Derivation_implies_DerivTree:
  shows "Derivation [s] D \<alpha> \<Longrightarrow> is_nonterminal s \<Longrightarrow> \<exists> t. (DeriveFromTree t) = (s, \<alpha>)"
  using DerivationSymbol_implies_DerivTree by fastforce


lemma DT_implies_Derives1:
  assumes "DeriveFromTree (DT r l) = (a, b)" and "Tree_wf1 (DT r l)" 
  shows "Derives1 [a]  0  r (snd r)"
proof -
  from assms have a:"a = fst r" by auto
  from assms have "r \<in> \<RR>" by auto
  from this and a show ?thesis apply(simp add: Derives1_def) apply(rule_tac x="[]" in exI)
    apply(rule_tac x="[]" in exI) apply(rule_tac x="fst r" in exI)
    apply(simp) done
qed


end

end