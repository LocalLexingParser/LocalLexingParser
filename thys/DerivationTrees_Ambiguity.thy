theory DerivationTrees_Ambiguity
  imports  "OperatorAmbiguity" "DerivationTrees1" "LocalLexing2.Ladder"  "LocalLexing2.TheoremD6" 
begin
context OperatorAmbiguity
begin
(*termination measure on subtrees? e.g. induction*)
(*rotation via insert?*)
function insert_left::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree" where
"insert_left (Leaf a) _ = (Leaf a)" |
"insert_left (Inner a) (DT r b) = (if (fst r = a) then (DT r b) else (Inner a))"|
"insert_left  (Inner a ) _ = (Inner a)"|
"insert_left (DT r b) (DT r' b') = (DT r ((insert_left (hd b) (DT r' b'))#(tl b)))"|
"insert_left (DT r b) _ = (DT r b)"
  sorry
termination sorry
(* (DT r b, DT r' b') ~> (last b, DT r' b')*)
function insert_right::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree" where
"insert_right (Leaf a) _ = (Leaf a)" |
"insert_right (Inner a) (DT r b) = (if (fst r = a) then (DT r b) else (Inner a))"|
"insert_right  (Inner a ) _ = (Inner a)"|
"insert_right (DT r b) (DT r' b') = (DT r ((butlast b)@[insert_right (last b) (DT r' b')]))"|
"insert_right (DT r b) _ = (DT r b)"
  apply(auto) sorry
termination sorry

lemma root_symbol:"DeriveFromTree (DT r b) = (s', a') \<Longrightarrow> fst r = s'"
  by auto
(*how to use assumptions in induction*)
lemma insertion_left_effect:
  shows "DeriveFromTree t = (s, a) \<Longrightarrow> DeriveFromTree (DT r b) = (s', a') \<Longrightarrow> hd a = s' \<Longrightarrow>DeriveFromTree (insert_left t (DT r b)) = (s, a'@(tl a))"
proof(induct t arbitrary: s a rule: derivtree.induct)
  case (Leaf x)(*does not hold by contradiction*)
  then show ?case sorry
next
  case (Inner x)
  then  have eq:"s = x"  "a = [x]" by auto  
  then  have ins:"insert_left (Inner x) (DT r b) = (DT r b)" sorry
  from Inner.prems(1) have tl:"tl a = []" by auto
  have eq1:"s = s'" using Inner.prems by auto
  have "fst r = s'" using root_symbol Inner.prems(2) by blast 
  then have "fst r = x" using eq eq1 by blast
  then show ?case using ins by simp 
next
  case (DT r' b')
  from DT.prems(1) have root:"fst r' = s" by simp
  obtain left where "left = hd b'" by blast
  obtain tree where nodedef:"tree = insert_left (DT r' b') (DT r b)" by blast 
  then have node:"tree =  (DT r' ((insert_left (hd b') (DT r b))#(tl b')))" sorry
  obtain x' where hd:"x' = hd b'"  by blast
  then have xset:"x' \<in> set b'" (*need to have b' nonempty*) sorry
  obtain s'' a'' where hd1:"DeriveFromTree x' = (s'', a'')" by fastforce
  then have hd2:"a'' = snd (DeriveFromTree x')" by auto
  obtain tl_deriv where tl_deriv:"tl_deriv = map (\<lambda>s . (snd (DeriveFromTree s))) (tl b')" by blast
  obtain l'' where tl_concat:" l''= concat(tl_deriv)" by blast
  with hd2 DT.prems(1) hd have  concat:"a''@l'' = a" apply(auto)  sorry
  have "a'' \<noteq> []" using hd1 sorry(*wf lemma*)
  with concat have tl:"tl a = (tl a'')@l''" by force   
  have "hd a'' = s'" sorry (*need lemmas*)
  with DT(1) xset hd1 DT.prems(2) have "DeriveFromTree (insert_left x' (DT r b)) = (s'', a' @ tl a'')" by blast
  then have " a' @ tl a'' = snd (DeriveFromTree (insert_left x' (DT r b)))" by simp
  with tl_deriv hd have map:"(a'@tl a'')#tl_deriv= 
      map (\<lambda>s . (snd (DeriveFromTree s))) ((insert_left (hd b') (DT r b))#(tl b'))" using Cons_eq_map_conv by force
  with tl_concat tl have "concat ((a'@tl a'')#tl_deriv) = (a'@tl a)" by simp
  with map node root have "DeriveFromTree tree = (s, a'@(tl a))" by simp
  with nodedef show ?case by blast
qed



lemma insertion_right_effect:
  shows "DeriveFromTree t = (s, a) \<Longrightarrow> DeriveFromTree (DT r b) = (s', a') \<Longrightarrow> last a = s' \<Longrightarrow>DeriveFromTree (insert_right t (DT r b)) = (s, (butlast a)@a')"
proof(induct t arbitrary: s a rule: derivtree.induct)
  case (Leaf x)(*does not hold by contradiction*)
  then show ?case sorry
next
  case (Inner x)
  then  have eq:"s = x"  "a = [x]" by auto  
  then  have ins:"insert_right (Inner x) (DT r b) = (DT r b)" sorry
  from Inner.prems(1) have tl:"tl a = []" by auto
  have eq1:"s = s'" using Inner.prems by auto
  have "fst r = s'" using root_symbol Inner.prems(2) by blast 
  then have "fst r = x" using eq eq1 by blast
  then show ?case using ins by simp 
next
  case (DT r' b')
  from DT.prems(1) have root:"fst r' = s" by simp
  obtain left where "left = hd b'" by blast
  obtain tree where nodedef:"tree = insert_right (DT r' b') (DT r b)" by blast 
  then have node:"tree =  (DT r' ((butlast b')@[(insert_right (last b') (DT r b))]))" sorry
  obtain x' where last:"x' = last b'"  by blast
  then have xset:"x' \<in> set b'" (*need to have b' nonempty*) sorry
  obtain s'' a'' where last1:"DeriveFromTree x' = (s'', a'')" by fastforce
  then have last2:"a'' = snd (DeriveFromTree x')" by auto
  obtain butlast_deriv where butlast:"butlast_deriv = map (\<lambda>s . (snd (DeriveFromTree s))) (butlast b')" by blast
  obtain l'' where bl_concat:" l''= concat(butlast_deriv)" by blast
  with last2 DT.prems(1) last have  concat:"l''@a'' = a" apply(auto)  sorry
  have "a'' \<noteq> []" using last1 sorry(*wf lemma*)
  with concat have tl:"butlast a = l''@(butlast a'')"  using butlast_append by metis
  have "last a'' = s'" sorry (*need lemmas over derive*)
  with DT(1) xset last1 DT.prems(2) have "DeriveFromTree (insert_right x' (DT r b)) = (s'', (butlast a'')@a')" by blast
  then have "(butlast a'')@a' = snd (DeriveFromTree (insert_right x' (DT r b)))" by simp
  with butlast last have map:"butlast_deriv@[(butlast a'')@a']= 
      map (\<lambda>s . (snd (DeriveFromTree s))) (butlast b'@[(insert_right (last b') (DT r b))])" by simp
  with bl_concat tl have "concat (butlast_deriv@[(butlast a'')@a']) = ((butlast a)@a')" by simp
  with map node root have "DeriveFromTree tree = (s, (butlast a)@a')" by simp
  with nodedef show ?case by blast
qed
(*derivation append?*)


(*define trees to be wellformed*)
section "Rightspine / Leftspine"
fun children::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree list" where
"children (DT a b) = (DT a b)#(concat (map children b))"|
"children a = [a]"

(*for now only include actual rule applications*)
fun leftmost_children::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree list" where
"leftmost_children (DT a []) = [(Inner (fst a))]"|
"leftmost_children (DT a b) = (DT a b)#(leftmost_children (hd b))"|
"leftmost_children a = []"

 (*nontermination because b is not nonempty*)


fun rightmost_children::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree list" where
"rightmost_children (DT a []) = [(Inner (fst a))]"|
"rightmost_children (DT a b) = (DT a b)#(leftmost_children (last b))"|
"rightmost_children a = []"


fun leftspine1::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree list" where
"leftspine1 (DT a b)= (case (hd b) of (DT a' b') \<Rightarrow> rightmost_children (hd b) | a \<Rightarrow> [])"|
"leftspine1 _ = []"

fun rightspine1::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree list" where
"rightspine1 (DT a b)= (case (last b) of (DT a' b') \<Rightarrow> leftmost_children (last b) | a \<Rightarrow> [])"|
"rightspine1 _ = []"


fun leftmost_item::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree" where
"leftmost_item (DT a []) = (DT a [])"|
"leftmost_item (DT a b) = (case (hd b) of (DT a' b') \<Rightarrow> leftmost_item (hd b) | a \<Rightarrow> a)"|
"leftmost_item a = a"    

function rightmost_item::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree" where
"rightmost_item (DT a []) = (DT a [])"|
"rightmost_item (DT a (b#B)) = (case (last (b#B)) of (DT a' b') \<Rightarrow> rightmost_item (last (b#B)) | a \<Rightarrow> a)"|
"rightmost_item a = a"    
  apply(auto) sorry
termination sorry

lemma rotation: 
  assumes "DeriveFromTree (DT r t) = (s, a)" " DeriveFromTree (DT r' t') = (s, b)" 
  "(s = last a) \<and> (s = hd b) " "a \<noteq> []" "b \<noteq> []" 
  shows "DeriveFromTree (insert_right (DT r t)  (DT r' t')) = DeriveFromTree (insert_left  (DT r' t') (DT r t))"
proof -
  from assms insertion_right_effect have deriv1:"DeriveFromTree (insert_right  (DT r t)  (DT r' t')) = (s, (butlast a)@b)" by fast
  from assms insertion_left_effect have deriv2:"DeriveFromTree (insert_left  (DT r' t')  (DT r t)) = (s, a@(tl b))"  by metis
  from assms have eq1:"(butlast a)@b =  (butlast a)@[s]@(tl b)" by fastforce
  from assms have eq2:"a@(tl b) = (butlast a)@[s]@(tl b)" by simp
  show ?thesis using deriv1 deriv2 eq1 eq2 by simp
qed

lemma rotation': 
  assumes \<alpha>E:"DeriveFromTree (DT r t) = (s, a)"  and E\<beta>:"DeriveFromTree (DT r' t') = (s, b)" and E3:"DeriveFromTree (DT r'' t'') = (s, c)"  
  and nonterms:"(s = last a) \<and> (s = hd b) " "a \<noteq> []" "b \<noteq> []" 
shows "DeriveFromTree (insert_right (DT r t)  (insert_left (DT r' t') (DT r'' t'' ))) = 
      DeriveFromTree (insert_left  (DT r' t') (insert_right (DT r t) (DT r'' t'')))"
proof -
  
  from assms insertion_right_effect have "DeriveFromTree (insert_right  (DT r t)  (DT r'' t'')) = (s, (butlast a)@c)" by fast
  with E\<beta> nonterms have deriv1: "DeriveFromTree (insert_left  (DT r' t') (insert_right (DT r t) (DT r'' t''))) = (s, (butlast a)@c@(tl b))" 
    using insertion_left_effect by fastforce
  from assms insertion_left_effect have "DeriveFromTree (insert_left  (DT r' t')  (DT r'' t'')) = (s, c@(tl b))"  by metis
  with \<alpha>E nonterms have deriv2:"DeriveFromTree (insert_right (DT r t)  (insert_left (DT r' t') (DT r'' t'' ))) = (s, (butlast a)@c@(tl b))" 
    using insertion_right_effect by fastforce
  show ?thesis using deriv1 deriv2  by simp
qed


(*proof insertion via all left/right subtrees?*)
(*define conflict between to trees a certain leftmost and rightmost element*)

(*parent and leftspine child \<Rightarrow> certain conflicts*)
fun leftconflictfree::"('a, 'b) rule \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"leftconflictfree r  T  = (case T of (DT r' _) \<Rightarrow> ((r, r') \<notin> Priority \<and> (r, r') \<notin> Left) | _ \<Rightarrow> True)"

fun rightconflictfree::"('a, 'b) rule \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"rightconflictfree r  (DT r' _) = ((r, r') \<notin> Priority \<and> (r, r') \<notin> Right)" |
"rightconflictfree _ _ = True"

fun conflictfree_root::"('a,'b) derivtree \<Rightarrow> bool" where 
"conflictfree_root (DT r b) = ((\<forall> s \<in> set (leftspine1 (DT r b)) .  (leftconflictfree r s)) \<and> 
      (\<forall>s \<in> set (rightspine1 (DT r b)) . (rightconflictfree r s)))"|
"conflictfree_root _ = True"
fun conflict_free::"('a, 'b) derivtree \<Rightarrow> bool" where
"conflict_free (DT r b) = (conflictfree_root (DT r b) \<and> list_all conflict_free b)"|
"conflict_free _ = True"


fun conflict_free'::"('a, 'b) derivtree \<Rightarrow> bool" where
"conflict_free' (DT r b) = (rightconflictfree r (last b) \<and> leftconflictfree r (hd b) \<and> list_all conflict_free' b)"|
"conflict_free' _ = True"
(*iteration function with predecessor tree and current subtree \<Rightarrow> helps proving that all derive the same*)

(*how to prove atomicity?*)
fun rotate_left_sub::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree\<Rightarrow> ('a, 'b) derivtree" where
"rotate_left_sub \<mu>E E\<gamma> E b= undefined"

(*lets define it if there exists a conflict on the root of this tree it rotates else unchanged*)
fun rotate_left::"('a, 'b) derivtree \<Rightarrow>  ('a, 'b) derivtree" where
"rotate_left T= undefined"
(*or how to do this?*)

lemma rotate_left_preserves:"(DeriveFromTree (rotate_left T)) = (DeriveFromTree T)"
  sorry

fun rotate_right::"('a, 'b) derivtree \<Rightarrow>  ('a, 'b) derivtree" where
"rotate_right T= undefined"
(*or how to do this?*)

lemma rotate_right_preserves:"(DeriveFromTree (rotate_right T)) = (DeriveFromTree T)"
  sorry

fun measure::"('a , 'b) derivtree \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"measure T T1 = undefined"
(*rotate only reduces distance measure etc \<Longrightarrow> lexicographically or something*)
lemma rotate_monotonic:"measure T (rotate_right T)"
  sorry

lemma conflict_case:"rotate_left T = T \<Longrightarrow> is_conflict_free T"
  sorry
(*one atomic case of rotation \<Longrightarrow> for each node find conflict, else go through tree in preorder*)

(*what to do with multiple conflicts on same depth*)

fun rotatetree::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree option" where
"rotatetree T = undefined"


(*to prove termination, then for one \<Longrightarrow> safety of rotation and *)

(*main lemma, rotation doesn't change relative position to subtree (middle Tree*)
(*this probably can be used for the termination metric*)
(*termination because depth of potential conflicts only gets reduced?*)
function tree_order::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree" where
"tree_order T = (case (rotatetree T) of None \<Rightarrow> T | (Some T') \<Rightarrow>tree_order T')"
  by auto
termination sorry 

(*output of tree rotations is conflict free & valid tree*)
theorem tree_safety:"conflict_free (tree_order T)"
  sorry


(*alternative proof \<Longrightarrow> new conflicts being resolved won't reintroduce old ones

\<Longrightarrow> because it's now in the subtree of E (third tree not being relatively swapped*)
end
end