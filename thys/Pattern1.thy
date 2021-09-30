theory Pattern1
  imports OperatorAmbiguity DerivationTrees_Ambiguity Containers.Containers

begin
type_synonym ('a, 'b) pattern = "(('a, 'b) symbol \<times> ('a, 'b) symbol list \<times> ('a, 'b) symbol list \<times> ('a, 'b) symbol list)"

(*need to specify transitive closure*)
locale Pattern  = OperatorAmbiguity +
  fixes \<P> :: "('a, 'b) pattern list"
  assumes Pattern_valid: "\<forall>(s, r1, r1' , r2) \<in> (set \<P>) . (s, r2) \<in> \<RR> \<and> (s, r1@r1') \<in> \<RR>"
  assumes Pattern_safety:"\<forall>(s, r1, r1', r2) \<in> (set \<P>) . ((s, r2), (s, r1@r1')) \<in> (Priority \<union> Left \<union> Right)" (*possibly stronger specification needed*)
  assumes Pattern_right_left:"\<forall>(s, r1, r1', r2) \<in> (set \<P>) . r1 = [] \<or> (r1' = [s] \<and> r1 \<noteq> [])"

  (*? filters on left nonterminal, so patterns are in priority or Left ?*)
assumes Pattern_safety_left:"\<forall>(s, r1, r1', r2) \<in> set \<P> . r1 = [] \<Longrightarrow>  ((s, r2), (s, r1@r1')) \<in>  (Priority \<union> Left)"
assumes Pattern_safety_right:"\<forall>(s, r1, r1', r2) \<in> set \<P> . (r1' = [s] \<and> r1 \<noteq> []) \<Longrightarrow>  ((s, r2), (s, r1@r1')) \<in>  (Priority \<union> Right)"


begin

section "Interpretation of patterns as one level filters
        
        then need to additionally prove that the rewriting algorithm rewrites a grammar in such a 
        way that all pattern assumptions are fulfilled"


fun containsRule::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) rule \<Rightarrow> bool" where
"containsRule (DT r' b) r = (if r' = r then True else False)"|
"containsRule _ _= False"

(*termination of subtree measures?*)

(*function denoting conflict freedom in left direction*)
function containsRuleLeft::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) rule \<Rightarrow> bool" where
"containsRuleLeft (DT r' b) r = (if r' = r then True else containsRuleLeft (hd b) r )"|
"containsRuleLeft (Inner s) r = False" |
"containsRuleLeft (Leaf s) r = False"
        apply(auto)
by (metis derivtree.distinct(5) insert_left.simps(2) insert_left.simps(3))
termination
  by (metis derivtree.distinct(5) insert_left.simps(2) insert_left.simps(3))
function containsRuleRight::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) rule \<Rightarrow> bool" where
"containsRuleRight (DT r' b) r = (if r' = r then True else containsRuleRight (last b) r )"|
"containsRuleRight (Inner s) r = False"|
"containsRuleRight (Leaf s)  r = False"
  apply(auto) 
  by (metis derivtree.distinct(5) insert_left.simps(2) insert_left.simps(3))
termination by (metis derivtree.distinct(5) insert_left.simps(2) insert_left.simps(3))

  thm "derivtree.distinct"
  thm "insert_left.simps"
fun filtered::"('a, 'b) derivtree \<Rightarrow> ('a, 'b)rule \<Rightarrow> bool" where
"filtered T r= (\<not>(containsRule T r))"

fun patterns::"('a, 'b) rule \<Rightarrow> ('a, 'b) pattern set" where
"patterns r = {(s, r1, r1', r2) \<in> set \<P> . (s, r1@r1') = r}"

(*definition via all patterns?*)
fun filter'::"('a, 'b) pattern \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"filter' (s, [], r1', r2) (DT r b) = (\<not> containsRuleRight (hd b) (s, r2))"|
"filter' (s, r1, [s'], r2) (DT r b) = (\<not> containsRuleLeft (last b) (s, r2))"|
"filter' _ _ = True"

fun valid_root_pattern::"('a, 'b) pattern \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"valid_root_pattern (s, r1, r1', r2)  (DT r b) = (if (s, r1@r1') = r then 
  (filter' (s, r1, r1', r2) (DT r b)) else True)" |
"valid_root_pattern _ _ = True"

lemma pattern_inapp_implies_true:"(s, r1@r1') \<noteq> r \<Longrightarrow> valid_root_pattern (s, r1, r1', r2)  (DT r b)"
  by simp

fun valid_tree_pattern::"('a, 'b) pattern \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"valid_tree_pattern p (DT r b) = (valid_root_pattern p (DT r b) \<and> list_all (valid_tree_pattern p) b) "|
"valid_tree_pattern p _ = True"

fun valid_tree1::"('a, 'b) derivtree \<Rightarrow> bool" where 
"valid_tree1 T = (\<forall> p \<in> set \<P> . valid_tree_pattern p T)"

fun valid_tree::"('a, 'b) derivtree \<Rightarrow> bool" where
"valid_tree (DT r b)  = (\<forall> p \<in> set \<P> . valid_root_pattern p (DT r b) \<and> (\<forall> t \<in> set b . valid_tree t))"|
"valid_tree _ = True"

(*have to add tree wellformed to ensure that there actually exist the needed values*)
lemma  exclusion_implies_patterns:"Tree_wf x \<Longrightarrow> \<not> valid_tree x \<Longrightarrow> \<exists>a aa ab b. (a, aa, ab, b) \<in> set \<P>"
proof(induction x)
  case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT r b)
  from DT.prems have "\<exists> p \<in> set \<P> . \<not> valid_root_pattern p (DT r b) \<or> (\<exists> t \<in> set b . \<not> valid_tree t)" by auto
  {
    assume "\<exists> p \<in> set \<P> . \<not> valid_root_pattern p (DT r b)"
    then obtain p where "\<not> valid_root_pattern p (DT r  b)" by blast
    then have " \<exists>a aa ab b. (a, aa, ab, b) \<in> set \<P>" sorry (*probably has to be based on wellformedness*)
  }
   show ?case sorry
qed
section "leftrecursive Ea \<Longrightarrow> rightrecursive bE \<Longrightarrow> valid_pattern Ea bE \<Longrightarrow> if a d
erivation is banned by this pattern, it is also banned by the operator ambiguity scheme"



lemma caseDT:"\<not> (leftconflictfree r s) \<Longrightarrow> s = (DT r' b')"
  sorry



lemma soundness_root:"\<forall> p \<in> set \<P>. valid_root_pattern p T \<Longrightarrow> conflictfree_root T" 
proof (induction T)
  case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT r b)
  {assume L1:"\<not> conflictfree_root (DT r b)"
  then have "(\<exists> s \<in> set (leftspine1 (DT r b)) .  \<not> (leftconflictfree r s)) \<or> 
             (\<exists> s \<in> set (rightspine1 (DT r b)) .  \<not> (rightconflictfree r s))" by auto
  (*assume "(\<exists> s \<in> set (leftspine1 (DT r b)) .  \<not> (leftconflictfree r s))"
  then obtain s where child:"s \<in> set (leftspine1 (DT r b))" and conflict:"(\<not> (leftconflictfree r s))" by blast
  from conflict obtain r' where "s = (DT r' b')" using caseDT by blast
  with conflict have "(r, r') \<in> (Priority \<union> Left)" by simp
  *) (*need additional case distinction on rightspine/leftspine*)
  have "(\<exists> p \<in> set \<P> . \<not> valid_root_pattern p (DT r b))" sorry
}
  from this have "\<forall> p \<in> set \<P>. valid_root_pattern p (DT r b) \<Longrightarrow> conflictfree_root (DT r b)" by fast
  (*need to construct that r' is contained in subtree under pattern and therefore a violation*)
  with DT.prems show ?case by blast
qed
  

subsection "Equivalence proof with regards to rotation system"
lemma pattern_soundness:"valid_tree T \<Longrightarrow> conflict_free T"
proof (induction T)
  case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT r b)
  {assume L1:"\<not> conflict_free (DT r b)"
  then have assms:"\<not> (conflictfree_root (DT r b) \<or> (\<exists> subtree \<in> set b . \<not> conflict_free subtree))" sorry
  {assume "\<not> (conflictfree_root (DT r b))"
    with soundness_root have "(\<exists> p \<in> set \<P> . \<not> valid_root_pattern p (DT r b))" by blast
      then have "\<not> (valid_tree (DT r b))" by auto
  } 
  from this have 1:"\<not> (conflictfree_root (DT r b)) \<Longrightarrow>  \<not>(valid_tree (DT r b))" by blast
  {
    assume "(\<exists> subtree \<in> set b . \<not> conflict_free subtree)"
    then obtain s where s:"s \<in> set b \<and> \<not> conflict_free s" by blast
    with DT.IH have "\<not> valid_tree s" by blast
    with s have " (\<exists> s \<in> set b . \<not> valid_tree s)" by blast
    from this have "\<not> (\<forall> s \<in> set b. valid_tree s)" by blast
    from this have "\<not> (valid_tree (DT r b))"  apply(auto) using exclusion_implies_patterns sorry (*wf based needed*)
  }
  with assms 1 have "\<not> (valid_tree (DT r b))" by blast
  }
  with DT.prems show ?case by blast 
qed
  
(*proof by contradiction, assume a tree is not conflict free, then the conflict will also hurt the filtering assumption*)
(*hat this is equivalent to either the disambiguation system in either Derivation Trees or LeftDerivations*)


  (*by (metis butlast.simps(2) drop_last list.simps(3)) (*invalid possible*)
*)
lemma "\<exists> s \<in> set (rightspine1 (DT r b)). \<not> rightconflictfree r s \<Longrightarrow> \<not> conflictfree_root (DT r b)"
proof - 
  assume assms:"\<exists> s \<in> set (rightspine1 (DT r b)). \<not> rightconflictfree r s" 
  {assume "conflictfree_root (DT r b)"
    then have "\<forall> s \<in> set (rightspine1 (DT r b)) . rightconflictfree r s" using conflictfree_root.simps(1) by blast
  }
  then show ?thesis using assms by blast
qed

subsection "Relation of valid pattern semantics as used in rewriting vs disambiguation"
(*relation of semantics of patterns*)
lemma right_contains_implies_conflict:"(r, r') \<in> (Priority \<union> Left)
   \<Longrightarrow> containsRuleRight (hd b) r'  \<Longrightarrow> \<exists>s \<in> set (leftspine1 (DT r b)) .  \<not>(leftconflictfree r s)"
  sorry

(*relation of semantics of patterns*)
lemma left_contains_implies_conflict:"(r, r') \<in> (Priority \<union> Right)
   \<Longrightarrow> containsRuleLeft (last b) r'  \<Longrightarrow> \<exists>s \<in> set (rightspine1 (DT r b)) . \<not> (rightconflictfree r s)"
  sorry

lemma pattern_completeness_root:"conflictfree_root T \<Longrightarrow> \<forall> p \<in> set \<P> . valid_root_pattern p T"
proof (induction T)
  case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT r b)
  {
    assume assms0: "\<exists> p \<in> set \<P> . \<not> valid_root_pattern p (DT r b)" 
    then obtain p  where  valid:"\<not> valid_root_pattern p (DT r b)" "p \<in> set \<P>"by blast
    (*the transitivity of patterns (itself only level 1 filtering) then implies an violation along left or right spine*)
    then obtain s r1 r1' r2 where p:"p = (s, r1, r1', r2)"   apply (cases p) by simp
    with valid have r1_r:"(s, r1@r1') = r" using pattern_inapp_implies_true by blast
    (*still have to prove why valid_root_pattern wrong implies r = s1@s1'*)
    with valid p have filter:"\<not> (filter' (s, r1, r1', r2) (DT r b))"  by auto
    from valid p have assms:"r1 = [] \<or> (r1' = [s] \<and> r1 \<noteq> [])" using Pattern_right_left by fast (*pattern right left correct assumption?*)
    {
      assume left:"r1 = []"
      with filter have rightcontain:"containsRuleRight (hd b) (s, r2)" using filter'.simps(1) by blast 
      (*containsright then applies that there exists a DT in hd b such that (s, r2) is its rule*)
      (*(\<forall> s \<in> set (leftspine1 (DT r b)) .  (leftconflictfree r s)*)
      from left valid p have " (r, (s, r2)) \<in> (Priority \<union> Left)" using Pattern_safety_left sorry
      with r1_r rightcontain right_contains_implies_conflict have 
          "\<exists>s\<in>set (leftspine1 (DT r b)). \<not> leftconflictfree r s" by blast
      then have "\<not> conflictfree_root (DT r b)" by fastforce  
    }
    then have  leftcase:"r1 = [] \<Longrightarrow> \<not> conflictfree_root (DT r b)" by blast
    {
      assume right:"r1' = [s]" "r1 \<noteq> []"
      with filter have leftcontain:"containsRuleLeft (last b) (s, r2)" using filter.simps(2) sorry
      from right valid p have "(r, (s, r2)) \<in> (Priority \<union> Right)" using Pattern_safety_right sorry
      with r1_r leftcontain have "\<exists> s \<in> set (rightspine1 (DT r b)). \<not> rightconflictfree r s" 
          using left_contains_implies_conflict by blast
      then have "\<not> conflictfree_root (DT r b)" by auto
    }
    (*case distinction on filtering*)
    with leftcase assms have "\<not> conflictfree_root (DT r b)" by blast
  }
  with DT.prems show ?case by blast
qed

lemma conflictfree_sub:"\<exists> t \<in> set b.\<not> conflict_free t \<Longrightarrow>\<not> conflict_free (DT r b)"
proof -
  assume assms:"\<exists> t \<in> set b.\<not> conflict_free t"
  {assume "conflict_free (DT r b)"
    then have "list_all conflict_free b" by simp 
    then have "\<forall> t \<in> set b. conflict_free t" using list_all_def by metis
  }
  then have "\<exists> t \<in> set b.\<not> conflict_free t \<Longrightarrow>\<not> conflict_free (DT r b)" by blast
  with assms  show ?thesis by blast
qed


(*? are the pattern definitions even correct*)
lemma pattern_completeness:"conflict_free T \<Longrightarrow> valid_tree T"
proof (induction T)
  case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT r b)
  {
    assume "\<not> valid_tree (DT r b)"
    from this have assms:"(\<exists> p \<in> set \<P> . \<not> valid_root_pattern p (DT r b) \<or> (\<exists> t \<in> set b . \<not> valid_tree t))" by simp
    {
      assume "\<exists> p \<in> set \<P> . \<not> valid_root_pattern p (DT r b)" 
      (*then obtain p where " \<not> valid_root_pattern p (DT r b)" by auto*)
      then have "\<not> conflictfree_root (DT r b)" using pattern_completeness_root by blast
      then have "\<not> conflict_free (DT r b)" by auto
    }
    then have 1:"(\<exists> p \<in> set \<P> . \<not> valid_root_pattern p (DT r b)) \<Longrightarrow> \<not> conflict_free (DT r b)" by blast
    {
      assume  "\<exists> t \<in> set b . \<not> valid_tree t"
      then have "\<exists> t \<in> set b.\<not> conflict_free t" using DT.IH by blast
      then have "\<not> conflict_free (DT r b)" using conflictfree_sub by blast
    }
    with 1 assms have "\<not> conflict_free (DT r b)" by blast
  }
  with DT.prems show ?case by blast
qed
(*assume something is not filtered according to the patterns and their axioms, 
prove that this would also constitute a violation under disambiguition rules*)

definition new_nonterm1::"('a \<times> nat, 'b) symbol set" where
"new_nonterm1 = undefined"

term case_sum
definition new_term1::"('a \<times> nat, 'b) symbol set" where
"new_term1 = (case_sum (\<lambda> t. Inl (t, 0)) Inr) ` \<TT>"  

definition rules1::"('a \<times> nat,  'b) rule set" where
"rules1 = undefined"

definition start1::"('a \<times> nat, 'b) symbol" where
"start1 = case_sum (\<lambda> t. Inl (t, 0)) Inr \<SS>  "

end


end
