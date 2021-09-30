theory Pattern
  imports OperatorAmbiguity DerivationTrees1 DerivationTrees_Ambiguity

begin
type_synonym ('a, 'b) pattern = "(('a, 'b) symbol \<times> ('a, 'b) symbol list \<times> ('a, 'b) symbol list \<times> ('a, 'b) symbol list)"

locale Pattern  = OperatorAmbiguity +
  fixes \<P> :: "('a, 'b) pattern set"
  assumes Pattern_valid: "\<forall>(s, r1, r1' , r2) \<in> \<P> . (s, r2) \<in> \<RR> \<and> (s, r1@r1') \<in> \<RR>"
  assumes Pattern_safety:"\<forall>(s, r1, r1', r2) \<in> \<P> . ((s, r2), (s, r1@r1')) \<in> (Priority \<union> Left \<union> Right)" (*possibly stronger specification needed*)
  assumes Pattern_right_left:"\<forall>(s, r1, r1', r2) \<in> \<P> . r1 = [] \<or> r1' = [s]"
  assumes Pattern_nonempty:"\<P> \<noteq> {}" (*seemed necessary*)
begin 
(*should prove for pattern that this is equivalent to either the disambiguation system in either Derivation Trees or LeftDerivations*)
(*prove validity of tree accoording to pattern*)
fun containsRule::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) rule \<Rightarrow> bool" where
"containsRule (DT r' b) r = (if r' = r then True else (\<exists> t \<in> set b . containsRule t r))"|
"containsRule _ _= False"
fun filtered::"('a, 'b) derivtree \<Rightarrow> ('a, 'b)rule \<Rightarrow> bool" where
"filtered T r= (\<not>(containsRule T r))"

fun patterns::"('a, 'b) rule \<Rightarrow> ('a, 'b) pattern set" where
"patterns r = {(s, r1, r1', r2) \<in> \<P> . (s, r1@r1') = r}"

(*definition via all patterns?*)

fun valid_root_pattern::"('a, 'b) pattern \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"valid_root_pattern (s, r1, r1', r2)  (DT r b) = (if (s, r1@r1') = r then 
  (filtered (b ! (length r1)) (s, r2)) else True)" |
"valid_root_pattern _ _ = True"

fun valid_tree_pattern::"('a, 'b) pattern \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"valid_tree_pattern p (DT r b) = (valid_root_pattern p (DT r b) \<and> list_all (valid_tree_pattern p) b) "|
"valid_tree_pattern p _ = True"

fun valid_tree1::"('a, 'b) derivtree \<Rightarrow> bool" where 
"valid_tree1 T = (\<forall> p \<in> \<P> . valid_tree_pattern p T)"

fun valid_tree::"('a, 'b) derivtree \<Rightarrow> bool" where
"valid_tree (DT r b)  = (\<forall> p \<in> \<P> . valid_root_pattern p (DT r b) \<and> (\<forall> t \<in> set b . valid_tree t))"|
"valid_tree _ = True"

(*have to add tree wellformed to ensure that there actually exist the needed values*)
lemma  exclusion_implies_patterns:"Tree_wf x \<Longrightarrow> \<not> valid_tree x \<Longrightarrow> \<exists>a aa ab b. (a, aa, ab, b) \<in> \<P>"
proof(induction x)
  case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT r b)
  from DT.prems have "\<exists> p \<in> \<P> . \<not> valid_root_pattern p (DT r b) \<or> (\<exists> t \<in> set b . \<not> valid_tree t)" by auto
  {
    assume "\<exists> p \<in> \<P> . \<not> valid_root_pattern p (DT r b)"
    then obtain p where "\<not> valid_root_pattern p (DT r  b)" by blast
    then have " \<exists>a aa ab b. (a, aa, ab, b) \<in> \<P>" sorry (*probably has to be based on wellformedness*)
  }
   show ?case sorry
qed
section "leftrecursive Ea \<Longrightarrow> rightrecursive bE \<Longrightarrow> valid_pattern Ea bE \<Longrightarrow> if a d
erivation is banned by this pattern, it is also banned by the operator ambiguity scheme"
lemma caseDT:"\<not> (leftconflictfree r s) \<Longrightarrow> s = (DT r' b')"
  sorry  
lemma soundness_root:"\<forall> p \<in> \<P>. valid_root_pattern p T \<Longrightarrow> conflictfree_root T" 
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
  have "(\<exists> p \<in> \<P> . \<not> valid_root_pattern p (DT r b))" sorry
}
  from this have "\<forall> p \<in> \<P>. valid_root_pattern p (DT r b) \<Longrightarrow> conflictfree_root (DT r b)" by fast
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
    with soundness_root have "(\<exists> p \<in> \<P> . \<not> valid_root_pattern p (DT r b))" by blast
      then have "\<not> (valid_tree (DT r b))" by auto
  } 
  from this have 1:"\<not> (conflictfree_root (DT r b)) \<Longrightarrow>  \<not>(valid_tree (DT r b))" by blast
  {
    assume "(\<exists> subtree \<in> set b . \<not> conflict_free subtree)"
    then obtain s where s:"s \<in> set b \<and> \<not> conflict_free s" by blast
    with DT.IH have "\<not> valid_tree s" by blast
    with s have " (\<exists> s \<in> set b . \<not> valid_tree s)" by blast
    from this have "\<not> (\<forall> s \<in> set b. valid_tree s)" by blast
    from this have "\<not> (valid_tree (DT r b))"  apply(auto) using exclusion_implies_patterns sorry
  }
  with assms 1 have "\<not> (valid_tree (DT r b))" by blast
  }
  with DT.prems show ?case by blast 
qed
  
(*proof by contradiction, assume a tree is not conflict free, then the conflict will also hurt the filtering assumption*)
(*hat this is equivalent to either the disambiguation system in either Derivation Trees or LeftDerivations*)
lemma pattern_completeness_root:"conflictfree_root T \<Longrightarrow> \<forall> p \<in> \<P> . valid_root_pattern p T"
proof (induction T)
  case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT r b)
  {
    assume "\<exists> p \<in> \<P> . \<not> valid_root_pattern p T" 
    then obtain p where "\<not> valid_root_pattern p T" by blast
    then have "\<not> conflictfree_root T" sorry
  }
  then show ?case sorry
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
    from this have "(\<exists> p \<in> \<P> . \<not> valid_root_pattern p (DT r b) \<or> (\<exists> t \<in> set b . \<not> valid_tree t))" by simp
    {
      assume "\<exists> p \<in> \<P> . \<not> valid_root_pattern p (DT r b)" 
      then obtain p where " \<not> valid_root_pattern p (DT r b)" by auto
      then have "\<not> valid_tree (DT r b)" sorry
    }
    then have "\<not> valid_tree (DT r b)" sorry
  }
  show ?case sorry
qed

  subsection "if banned by operator precedence ambiguity, patterns also ban this"
end
