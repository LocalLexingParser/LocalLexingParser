theory Stage3Rewriting
imports Rewriting1

begin 

 
type_synonym ('a, 'c) fresh_new_g_slot = "(((('a, 'c) symbol) \<Rightarrow> nat option) \<times>  ('a \<times> nat, 'c) symbol list 
\<times> ('a \<times> nat, 'c) grammar \<times>  (('a \<times> nat, 'c ) symbol \<Rightarrow> 
(('a, 'c) symbol list \<times> ('a, 'c) symbol list) option))"

(*for each nonterminal where we filter something add a new rule*)

(*changed replace*)
fun change_rule::"('a, 'c) symbol list \<Rightarrow> ('a, 'c) symbol list \<Rightarrow> ('a \<times> nat, 'c) symbol \<Rightarrow> ('a \<times> nat, 'c) rule \<Rightarrow> ('a \<times> nat, 'c) rule" where
"change_rule p p' s (N, \<alpha>) = (if (convert_back N = convert_back s \<and> convert_back_sentence \<alpha> = p@p' )
              then (N, list_update \<alpha> (length p) s)  else (N, \<alpha>))"

fun replace::"nat \<Rightarrow>  ('a, 'c) symbol list \<Rightarrow> ('a, 'c) symbol list \<Rightarrow> ('a \<times> nat, 'c) grammar \<Rightarrow> ('a  \<times> nat, 'c) grammar" where
"replace n p p' (\<NN>, \<TT>, g, s) = (({(convert n (hd p'))}\<union>\<NN>), \<TT>, (change_rule p p' (convert n (hd p'))) ` g, s)" 

(*for each recursive pattern,
  reserve new fresh nonterminal*)
fun step1::"('a, 'c) pattern \<Rightarrow>  ('a, 'c) fresh_new_g_slot \<Rightarrow>  ('a, 'c) fresh_new_g_slot" where
"step1 ((p1), p2 , p3, _) (f, n, g, s) = (if (p1 = hd p3) then (let f1 = fresh f p1 in 
        (f1, (convert  (the (f1 p1)) p1)#n, 
        replace (the (f1 p1)) p2 p3 g, s++[ (convert  (the (f1 p1)) p1) \<mapsto> (p2, p3)])) else (f, n, g, s)) "

(*reserves new fresh names *)
fun stage1_2::"('a, 'c) pattern list \<Rightarrow> ('a \<times> nat, 'c) grammar \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"stage1_2 p G = foldl (\<lambda> a b. step1 b a)  (Map.empty, [], G, Map.empty) p "

fun plain::"('a \<times> nat, 'c) symbol \<Rightarrow> ('a, 'c) symbol" where
"plain s = case_sum (\<lambda> t. Inl (fst t)) Inr s" 
fun plainrule::"('a \<times> nat, 'c) symbol list \<Rightarrow> ('a, 'c) symbol list" where
"plainrule l = map plain l"

fun candidate_rules::"('a \<times> nat, 'c) grammar \<Rightarrow> ('a \<times> nat, 'c) symbol \<Rightarrow> ('a \<times> nat, 'c) rule set"
  where
  "candidate_rules (\<NN>, \<TT>, R, s) head = Set.filter (\<lambda> (h,r) . h = head) R"

fun candidate_rules'::"('a \<times> nat, 'c) grammar \<Rightarrow> ('a \<times> nat, 'c) symbol \<Rightarrow> ('a \<times> nat, 'c) symbol list set" where
"candidate_rules' (\<NN>, \<TT>, R, s) head = ({ r. \<forall> (h, r) \<in> R . head = h})"(*should just be filtering*)

(*maybe changed to rule?*)
fun banned_patterns::"('a, 'c) pattern list \<Rightarrow> ('a, 'c) symbol \<Rightarrow> ('a, 'c) symbol list 
\<Rightarrow> ('a, 'c) symbol list \<Rightarrow> (('a, 'c) symbol list) list" where
"banned_patterns p head prev post = (foldr (\<lambda>(h,prefix, postfix, r2) l. 
(if (head = h \<and> prev = prefix \<and> post = postfix) then l else r2#l)) p [])"

fun add_rules::"('a, 'c) pattern list \<Rightarrow> (('a \<times> nat, 'c ) symbol) \<Rightarrow>(('a, 'c) symbol list \<times> ('a, 'c) symbol list) 
\<Rightarrow>  (('a \<times> nat, 'c) symbol  \<Rightarrow> ('a \<times> nat, 'c ) rule  set) \<Rightarrow> (('a \<times> nat, 'c) rule) set" where
"add_rules p symb (pre, post) rules_f = (let pattern = set (banned_patterns p (hd post) pre post) in 
(Pair symb) ` {r. \<forall> r \<in> snd ` (rules_f ( basic_convert (hd post))) . (plainrule r) \<notin> pattern})"


fun step2::"('a, 'c) pattern list \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a \<times> nat, 'c) grammar" where
"step2 p (f, new, (\<NN>, \<TT>, R, s), slot) = (let candidates = candidate_rules (\<NN>, \<TT>, R, s) in 
  (\<NN>, \<TT>, (R\<union> \<Union>((\<lambda> newsymb. add_rules p newsymb (the (slot newsymb)) candidates) ` set new)), s))"

fun stage3::"('a, 'c) pattern list \<Rightarrow> ('a \<times> nat, 'c) grammar \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"stage3 p G = (let (f, n, g, s) = stage1_2 p G in (f, n, step2 p (f, n, g, s), s))"

section "Rewriting until depth 1 conflicts are resolved"

context Pattern
begin
definition nonterm'::"('a \<times> nat, 'b) symbol set" where
"nonterm' = Inl ` local.new_nonterm"

definition term'::"('a \<times> nat, 'b) symbol set" where
"term' = Inr ` local.new_term"

definition fngs::"('a, 'b) fresh_new_g_slot" where
"fngs = stage3 \<P> (nonterm', term', rules, (Inl start)) "

definition \<GG>'::"('a \<times> nat, 'b) grammar" where
"\<GG>' = (let  (f, n, g, s) = stage3 \<P> (nonterm', term', rules, (Inl start)) in g)"

fun get_nonterm::"('a \<times> nat, 'b) grammar \<Rightarrow>('a \<times> nat, 'b) symbol set" where
"get_nonterm (r, _, _, _) = r"

fun get_term::"('a \<times> nat, 'b) grammar \<Rightarrow>('a \<times> nat, 'b) symbol set" where
"get_term (_ , r, _, _) = r"

fun get_rule::"('a \<times> nat, 'b) grammar \<Rightarrow>('a \<times> nat, 'b) rule set" where
"get_rule (_, _, r, _) = r"

fun get_s::"('a \<times> nat, 'b) grammar \<Rightarrow>('a \<times> nat, 'b) symbol" where
"get_s (_,  _,  _, s) = s"

fun extract_inl::"('a \<times> nat, 'b) symbol \<Rightarrow> 'a \<times> nat" where
"extract_inl (Inl a) = a"|
"extract_inl a = projl a"

fun extract_inr::"('a \<times> nat, 'b) symbol \<Rightarrow> 'b" where
"extract_inr a = projr a"

fun rightconflictfree'::"('a, 'b) rule \<Rightarrow> ('a, 'b) rule \<Rightarrow> bool" where
"rightconflictfree' r  r' = ((r, r') \<notin> Priority \<and> (r, r') \<notin> Right)" 

fun leftconflictfree'::"('a, 'b) rule \<Rightarrow> ('a, 'b) rule \<Rightarrow> bool" where
"leftconflictfree' r  r' = ((r, r') \<notin> Priority \<and> (r, r') \<notin> Left)" 

definition \<NN>''::"('a \<times> nat) set" where
"\<NN>'' = projl ` (get_nonterm \<GG>')"

definition \<TT>''::"'b set" where
"\<TT>'' = projr ` (get_term \<GG>')"

definition \<RR>''::"('a \<times> nat, 'b) rule set" where
"\<RR>'' = get_rule \<GG>'"

definition \<SS>''::"'a \<times> nat" where
"\<SS>'' = projl (get_s \<GG>')"
lemma replace_preserves:"replace r p2 p3 (\<NN>1, \<TT>1, R1, \<SS>1) = (\<NN>2, \<TT>2, R2, \<SS>2) \<Longrightarrow> \<NN>1 \<subseteq> \<NN>2"
  by (auto)
lemma replace_\<SS>:"replace r p2 p3 (\<NN>1, \<TT>1, R1, \<SS>1) = (\<NN>2, \<TT>2, R2, \<SS>2) \<Longrightarrow> \<SS>1 = \<SS>2"
  by (auto)
lemma replace_\<SS>_inv:"\<SS>1 \<in> \<NN>1 \<Longrightarrow>replace r p2 p3 (\<NN>1, \<TT>1, R1, \<SS>1) = (\<NN>2, \<TT>2, R2, \<SS>2) \<Longrightarrow> \<SS>2 \<in> \<NN>2"
  by auto

(*invariants*)

fun start_in_nonterm::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"start_in_nonterm (\<NN>1, \<TT>1, R1, \<SS>1) = (\<SS>1 \<in> \<NN>1)"

fun valid_rules::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"valid_rules (\<NN>1, \<TT>1, R1, \<SS>1) = (\<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1))"

fun finite_R::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"finite_R (\<NN>1, \<TT>1, R1, \<SS>1) = finite R1"

fun rules_convertback::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"rules_convertback (\<NN>1, \<TT>1, R1, \<SS>1) = (\<forall>(N, \<alpha>)\<in>R1 . (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>)"

fun term_unchanged::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"term_unchanged (\<NN>1, \<TT>1, R1, \<SS>1) = (\<TT>1 = term')"

fun nonterm_eq::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"nonterm_eq (\<NN>1, \<TT>1, R1, \<SS>1) =  (convert_back ` \<NN>1 = Inl ` \<A>)"

fun new_in_nonterm::"('a, 'b) fresh_new_g_slot \<Rightarrow> bool" where
"new_in_nonterm (f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s) = ((set n) \<subseteq> \<NN>1)"

definition is_zero_index::"('a \<times> nat, 'b) symbol \<Rightarrow> bool" where
  "is_zero_index s = (s \<in> Inl ` new_nonterm \<or> s \<in> Inr ` new_term)"

fun middle_zero_index::"('a \<times> nat, 'b) rule \<Rightarrow> bool" where
"middle_zero_index (N, \<alpha>) = ((length \<alpha> < 2 \<longrightarrow> list_all is_zero_index \<alpha>) \<and>
  (length \<alpha> \<ge> 2 \<longrightarrow> list_all is_zero_index (butlast (tl \<alpha>))))"

fun rules_middle_zero_index::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"rules_middle_zero_index (\<NN>1, \<TT>1, R1, \<SS>1) = (\<forall> (N, \<alpha>) \<in> R1 . middle_zero_index (N, \<alpha>))"

fun zero_index_all::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"zero_index_all (\<NN>1, \<TT>1, R1, \<SS>1) = (\<forall> (N', \<alpha>') \<in> \<RR> . \<exists> (N, \<alpha>) \<in> R1 . is_zero_index N \<and> convertback_rule (N, \<alpha>) = (N', \<alpha>'))"

fun grammar_invariants::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"grammar_invariants g = (start_in_nonterm g \<and> valid_rules g \<and> finite_R g \<and> rules_convertback g 
  \<and> term_unchanged g \<and> nonterm_eq g \<and> rules_middle_zero_index g \<and> zero_index_all g)"

fun fngs_invariants::"('a, 'b) fresh_new_g_slot \<Rightarrow> bool" where
"fngs_invariants (f, n, g, s) = (new_in_nonterm (f, n, g, s) \<and> grammar_invariants g)"

(*needs evolving lemmas to be proven*)
(*i. e. that slots define the only position where a certain nonterminal is used*)
fun rule_exists_leftconflictfree::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"rule_exists_leftconflictfree (\<NN>1, \<TT>1, R1, \<SS>1) = (\<forall> (N, \<alpha>) \<in> R1 . (\<forall> (N', \<alpha>') \<in> \<RR> . N' = convert_back (hd \<alpha>) 
      \<and> leftconflictfree' (convertback_rule (N, \<alpha>)) (N', \<alpha>')
    \<longrightarrow> (\<exists> (N'', \<alpha>'') \<in> R1 . N'' = hd \<alpha> \<and> convertback_rule (N'', \<alpha>'') = (N', \<alpha>'))))"

fun rule_exists_rightconflictfree::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"rule_exists_rightconflictfree (\<NN>1, \<TT>1, R1, \<SS>1) = (\<forall> (N, \<alpha>) \<in> R1 . (\<forall> (N', \<alpha>') \<in> \<RR> . N' = convert_back (last \<alpha>) 
      \<and> rightconflictfree' (convertback_rule (N, \<alpha>)) (N', \<alpha>')
    \<longrightarrow> (\<exists> (N'', \<alpha>'') \<in> R1 . N'' = last \<alpha> \<and> convertback_rule (N'', \<alpha>'') = (N', \<alpha>'))))"

lemma step1_preserves:
  assumes "\<SS>2 \<in> \<NN>2 ""(f', n', (\<NN>3, \<TT>3, R3, \<SS>3), s') = step1 ((p1), p2 , p3, p4) (f, n, (\<NN>2, \<TT>2, R, \<SS>2), s)"
  shows "\<SS>3 \<in> \<NN>3"
proof (cases " (p1 = hd p3)")
  case True
  with assms(2) have "(f', n', (\<NN>3, \<TT>3, R3, \<SS>3), s') = (let f1 = fresh f p1 in 
        (f1, (convert  (the (f1 p1)) p1)#n, 
        replace (the (f1 p1)) p2 p3 (\<NN>2, \<TT>2, R, \<SS>2), s++[ (convert  (the (f1 p1)) p1) \<mapsto> (p2, p3)]))" by simp
  then have "replace  (the ((fresh f p1) p1)) p2 p3 (\<NN>2, \<TT>2, R, \<SS>2) = (\<NN>3, \<TT>3, R3, \<SS>3)" 
    by (auto simp add: Let_def)
  then show ?thesis using replace_\<SS>_inv assms(1) by blast
next
  case False
  with assms(2) have "(\<NN>2, \<TT>2, R, \<SS>2) = (\<NN>3, \<TT>3, R3, \<SS>3)" by simp 
  then show ?thesis using assms(1) by simp
qed

lemma change_rule_valid_rules:
  assumes "N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)"
          "change_rule p p' s (N, \<alpha>) = (N', \<alpha>')"
  shows  "N' \<in> \<NN>1 \<union> {s} \<and> (\<forall>i\<in>set \<alpha>'. i \<in> \<NN>1 \<union>  \<TT>1 \<union> {s})"
proof (cases "(convert_back N = convert_back s \<and> convert_back_sentence \<alpha> = p@p' )")
  case True
  with assms(2) have eq:"N' = N" by auto
  from True assms(2) have "\<alpha>' = list_update \<alpha> (length p) s" by auto
  then have "set \<alpha>' \<subseteq> set \<alpha> \<union> {s}" by (simp add: set_update_subset_insert)
  with assms(1) have "(\<forall>i\<in>set \<alpha>'. i \<in> \<NN>1 \<union>  \<TT>1 \<union> {s})"  by blast
  then show ?thesis using assms(1) eq by blast
next
  case False
  then show ?thesis using assms by auto
qed
   
lemma replace_valid_rules':
  assumes  "\<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" 
           "replace  r p2 p3 (\<NN>1, \<TT>1, R1, \<SS>1) = (\<NN>2, \<TT>2, R2, \<SS>2)"
         shows "\<forall>(N, \<alpha>)\<in>R2. N \<in> \<NN>2 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>2 \<union>  \<TT>2)"
proof - 
  obtain s where s_def:"s = (convert r (hd p3)) " by blast
  then have new1:"\<NN>2 = {s}\<union>\<NN>1" and new2: 
      "\<NN>2 \<union>  \<TT>2 = {s}\<union>\<NN>1\<union> \<TT>1" using assms(2) by auto
  from assms(2) have "R2 = (change_rule p2 p3 s) ` R1" by (auto simp add:s_def) 
  then have "\<forall>(N, \<alpha>)\<in>R2 . (\<exists> i \<in> R1 . change_rule p2 p3 s i = (N, \<alpha>))" using
    s_def by auto
  then have "\<forall>(N', \<alpha>')\<in>R2 . (\<exists> (N, \<alpha>) \<in> R1 . change_rule p2 p3 s (N, \<alpha>) = (N', \<alpha>') \<and>
  N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1) )" using assms(1) by fast
  then have "\<forall>(N', \<alpha>')\<in>R2 . (\<exists> (N, \<alpha>) \<in> R1 . N' \<in> \<NN>1\<union>{s} \<and> (\<forall>s'\<in>set \<alpha>'. s' \<in> \<NN>1 \<union> \<TT>1 \<union>{s}))"
    using change_rule_valid_rules by fast 
  then have "\<forall>(N, \<alpha>)\<in>R2. N \<in> \<NN>2 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>2 \<union>  \<TT>2)"  using new2 by (auto simp add:new1)
  then show ?thesis by blast 
qed

lemma change_rule_convert_back:
  assumes "(convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>"
          "change_rule p p' s (N, \<alpha>) = (N', \<alpha>')"
          "convert_back s = hd p'"
  shows  "(convert_back N', convert_back_sentence \<alpha>') \<in> \<RR>"
proof (cases "(convert_back N = convert_back s \<and> convert_back_sentence \<alpha> = p@p' )")
  case True
  with assms(2) have eq:"N' = N" by auto
  (*why does this hold*)
  from True assms(3) have 1:"convert_back (\<alpha> ! (length p)) = convert_back s" sorry
  from True assms(2) have "\<alpha>' = list_update \<alpha> (length p) s" by auto
  then have "convert_back_sentence  \<alpha>' = convert_back_sentence \<alpha> " using 1 sorry
  then show ?thesis using assms(1) eq by auto
next
  case False
  then show ?thesis using assms by auto
qed

lemma change_rule_zero_index:
  assumes "(convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>"
          "change_rule p p' s (N, \<alpha>) = (N', \<alpha>')"
          "convert_back s = hd p'"
          "is_zero_index N"
  shows  "(convert_back N', convert_back_sentence \<alpha>') \<in> \<RR> \<and> is_zero_index N'"
proof (cases "(convert_back N = convert_back s \<and> convert_back_sentence \<alpha> = p@p' )")
  case True
  with assms(2) have eq:"N' = N" by auto
  (*why does this hold*)
  from True assms(3) have 1:"convert_back (\<alpha> ! (length p)) = convert_back s"  sorry
  from True assms(2) have "\<alpha>' = list_update \<alpha> (length p) s" by auto
  then have "convert_back_sentence  \<alpha>' = convert_back_sentence \<alpha> " using 1 sorry
  then show ?thesis using assms(1) eq assms by auto
next
  case False
  then show ?thesis using assms by auto
qed

definition valid_pattern::"('a, 'b) symbol list \<Rightarrow> ('a, 'b) symbol list \<Rightarrow> bool" where
"valid_pattern p p' = ((p = [] \<and> length p' > 2) \<or> (length p \<ge> 1 \<and> length p' = 1))"

lemma convert_back_eq:"length ( convert_back_sentence \<alpha>) = length \<alpha>"
  by simp

lemma valid_pattern_implies_length2:"valid_pattern p p' \<Longrightarrow> length (p@p') \<ge> 2" 
  using valid_pattern_def by auto

lemma valid_pattern_cases:"valid_pattern p p' \<Longrightarrow> length p = 0 \<or> length p  = length (p@p') -1" 
  using valid_pattern_def by auto

lemma change_rule_middle_zero:
  assumes "change_rule p p' s (N, \<alpha>) = (N', \<alpha>')"
          "valid_pattern p p'"
          "middle_zero_index (N, \<alpha>)"
  shows  "middle_zero_index (N', \<alpha>')"
proof (cases "(convert_back N = convert_back s \<and> convert_back_sentence \<alpha> = p@p' )")
  case True
  with assms(1) have eq:"N' = N" by auto
  from True assms(2) have l:"length \<alpha> \<ge> 2" by (metis valid_pattern_implies_length2 convert_back_eq )
  (*why does this hold*)
  from True assms(1) have update:"\<alpha>' = list_update \<alpha> (length p) s" by auto
  from True assms(2) have cases:"length p  = 0 \<or> length p = length \<alpha> -1" by (metis valid_pattern_cases convert_back_eq)
  show ?thesis
  proof (cases "length p  = 0 ")
    case True
    then have "tl \<alpha>' = tl \<alpha>" using  l apply(cases \<alpha>)  by(auto simp add: update)
    then have "butlast (tl \<alpha>') = butlast (tl \<alpha>)" by simp
    then show ?thesis using assms(3) l update by auto 
  next
    case False
    with  assms(2) have "length p = length \<alpha> -1" using True cases by(auto simp add: valid_pattern_def) 
    then have "butlast \<alpha>' = butlast \<alpha>" using  l apply(cases \<alpha> rule: rev_cases)  by (auto simp add: update)
    then have "butlast (tl \<alpha>') = butlast (tl \<alpha>)" by (simp add: butlast_tl)
    then show ?thesis using assms(3) l update by auto 
  qed
next
  case False
  then show ?thesis using assms by auto
qed

lemma replace_nonterm_add:"replace r p2 p3 (\<NN>1, \<TT>1, R1, \<SS>1) = (\<NN>2, \<TT>2, R2, \<SS>2) \<Longrightarrow>  
    \<NN>2 = \<NN>1\<union>{convert r (hd p3)}"
  by simp

lemma replace_invariants:                   
  assumes "replace r p2 p3 g = g'" "grammar_invariants g" "valid_pattern p2 p3"
  shows   "grammar_invariants g'" 
proof - 
  obtain \<NN>1 \<TT>1 R1 \<SS>1 where g:"(\<NN>1, \<TT>1, R1, \<SS>1) = g" apply(cases g) by blast
  obtain \<NN>2 \<TT>2 R2 \<SS>2 where g':"(\<NN>2, \<TT>2, R2, \<SS>2) = g'" apply (cases g') by blast
  then have 0:"\<forall> (N', \<alpha>')\<in>R2 . (\<exists> (N, \<alpha>)\<in>R1 . change_rule p2 p3 (convert r (hd p3)) (N, \<alpha>) = (N', \<alpha>') )"
    using assms g append.right_neutral append_prepend_nil1 list.discI sorry(*slow running proof*)
  (*start in nonterm*)
  from assms(1) have " \<SS>1 = \<SS>2" using g g' by auto
  with assms g g' have start:"start_in_nonterm g'" by auto
  (*valid rules*)
  from assms(2) g have 1:"\<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" by fastforce
  from assms(1) g g' have valid:"valid_rules g'" using replace_valid_rules' [OF 1] by auto
  (*term unchanged*)
  from assms g g' have ter:"term_unchanged g'" by force
  (*finite R*)
  from assms g g' have fin:"finite_R g'" by force
  (*rules convert_back*)
  have conv:"rules_convertback g'" using change_rule_convert_back sorry
  (*nonterm eq*)
  
  from assms g g' have prem:"(convert_back ` \<NN>1 = Inl ` \<A>)" by force
  have "(hd p3) \<in> Inl ` \<A> " sorry (*pattern assumption*)
  then have 2:"convert_back (convert r (hd p3)) \<in>  Inl ` \<A>" by auto
  have "\<NN>2 = \<NN>1\<union>{convert r (hd p3)}" using assms g g' by auto
  with 2 prem have nonterm:"nonterm_eq g'" using g' by force
  (*zero index all*)
  from assms(2) g have "\<forall>(N, \<alpha>)\<in>R1 . middle_zero_index (N, \<alpha>)" by fastforce
  then have "\<forall>(N, \<alpha>)\<in>R2 .middle_zero_index (N, \<alpha>)" using change_rule_middle_zero assms(3) g g' 0 by fast
  then have middle:"rules_middle_zero_index g'" using g' by force           
  (*rules zero index all*)
  have zero_index_all:"zero_index_all g'" using g' change_rule_zero_index sorry
  from nonterm conv ter start valid fin middle zero_index_all show ?thesis by auto
qed

lemma step1_invariants:
  assumes "(f', n', g', s') = step1 ((p1), p2 , p3, p4) (f, n, g, s)"
          "fngs_invariants (f, n, g, s)"
  shows  "fngs_invariants (f', n', g', s')"
proof (cases "(p1 = hd p3)")
  case True
  with assms(1) have "(f', n', g', s') = (let f1 = fresh f p1 in 
        (f1, (convert  (the (f1 p1)) p1)#n, 
        replace (the (f1 p1)) p2 p3 g, s++[ (convert  (the (f1 p1)) p1) \<mapsto> (p2, p3)]))" by simp
  then have step:"(f', n', g', s') = ((fresh f p1), (convert  (the ((fresh f p1) p1)) p1)#n, 
        replace (the ((fresh f p1) p1)) p2 p3 g, s++[ (convert  (the ((fresh f p1) p1)) p1) \<mapsto> (p2, p3)])" by metis
  then have 1:"g' = replace (the ((fresh f p1) p1)) p2 p3 g" by simp
  have "valid_pattern p2 p3" sorry (*has to propagate*)
  with 1 assms(2)  have gram:"grammar_invariants g'" using replace_invariants by auto
  obtain \<NN>1 \<TT>1 R1 \<SS>1 where g:"(\<NN>1, \<TT>1, R1, \<SS>1) = g" apply(cases g) by blast
  obtain \<NN>2 \<TT>2 R2 \<SS>2 where g':"(\<NN>2, \<TT>2, R2, \<SS>2) = g'" apply (cases g') by blast
  from 1 g g' have new_nonterm:"\<NN>2 = \<NN>1 \<union> {(convert  (the ((fresh f p1) p1)) (hd p3))}" 
      using replace_nonterm_add by force
  with True have new_new:"n' = (convert  (the ((fresh f p1) p1)) (hd p3))#n" using step by simp
  from assms(2) have "set n \<subseteq> \<NN>1" using g by fastforce  
  then have "new_in_nonterm (f', n', g', s')" using g' new_nonterm new_new by auto 
  then show ?thesis using gram by simp
next
  case False
  then show ?thesis using assms by auto 
qed

lemma stage1_2_help_invariants:
  shows  "(f', n', g', s') = foldl (\<lambda> a b. step1 b a)  (f, n, g, s) p \<Longrightarrow> 
            fngs_invariants (f, n, g, s) \<Longrightarrow> fngs_invariants (f', n', g', s')"
proof (induction p arbitrary:  f n g s)
  case Nil
  then show ?case by auto
next
  case (Cons a p)
  obtain f'' n'' g'' s'' where step:"(f'', n'', g'', s'') =
    step1 a (f, n, g, s)" apply (cases a) by (metis step1.simps)
  with Cons(3) step1_invariants have inv:"fngs_invariants (f'', n'', g'', s'')" apply(cases a) by blast
  have "foldl (\<lambda> a b .step1 b a) (f'', n'', g'', s'') p = (f', n', g', s')"
    using Cons step by simp
  then show ?case using inv Cons(1) by metis
qed

lemma stage1_2_invariants:
  assumes "stage1_2 p g = (f', n', g', s')  " " grammar_invariants g "
  shows " fngs_invariants (f', n', g', s')"
proof - 
  from assms(1) have fold:"foldl (\<lambda> a b. step1 b a)  (Map.empty, [], g, Map.empty) p = (f', n', g', s')" by simp
  obtain \<NN>1 \<TT>1 R1 \<SS>1 where g:"(\<NN>1, \<TT>1, R1, \<SS>1) = g" apply(cases g) by blast
  have "set [] \<subseteq> \<NN>1" by simp
  with assms(2) have "fngs_invariants (Map.empty, [], g, Map.empty)" using g by auto
  with fold show ?thesis using stage1_2_help_invariants by metis
qed


lemma stage1_2_help:"foldl (\<lambda> a b .step1 b a)  (f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s) p= 
    (f', n', (\<NN>2, \<TT>2, R2, \<SS>2), s') \<Longrightarrow> \<SS>1 \<in> \<NN>1 \<Longrightarrow> \<SS>2 \<in> \<NN>2"
proof (induction p arbitrary:  f n \<NN>1 \<TT>1 R1 \<SS>1 s)
  case Nil
  then have "(f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s) =  (f', n', (\<NN>2, \<TT>2, R2, \<SS>2), s')" by simp
  then show ?case using Nil(2) by blast
next
  case (Cons a p)
  obtain f'' n'' \<NN>' \<TT>' R' \<SS>' s'' where step:"(f'', n'', (\<NN>', \<TT>', R', \<SS>'), s'') =
    step1 a (f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s)" apply(cases "step1 a (f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s)") by auto
  with Cons(3) step1_preserves have inv:"\<SS>' \<in> \<NN>'" apply(cases a) by blast
  have "foldl (\<lambda> a b .step1 b a) (f'', n'', (\<NN>', \<TT>', R', \<SS>'), s'') p = (f', n', (\<NN>2, \<TT>2, R2, \<SS>2), s')"
    using Cons step by simp
  then show ?case using inv Cons by blast
qed

lemma stage1_2_preserves: "stage1_2 p (\<NN>1, \<TT>1, R1, \<SS>1) = (f', n', (\<NN>2, \<TT>2, R2, \<SS>2), s')  \<Longrightarrow> \<SS>1 \<in> \<NN>1 \<Longrightarrow> \<SS>2 \<in> \<NN>2"
  using stage1_2_help by fastforce

lemma step1_valid_rules:
  assumes "\<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" and
           "(f', n', (\<NN>2, \<TT>2, R2, \<SS>2), s') = step1 ((p1), p , p', p4) (f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s)"
  shows "\<forall>(N, \<alpha>)\<in>R2. N \<in> \<NN>2 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>2 \<union>  \<TT>2)"
proof (cases "(p1 = hd p')")
  case True
  with assms(2) have "replace  (the ((fresh f p1) p1)) p p' (\<NN>1, \<TT>1, R1, \<SS>1) = 
    (\<NN>2, \<TT>2, R2, \<SS>2) " by (auto simp add: Let_def)
  then show ?thesis using replace_valid_rules' assms(1) by fast 
next
  case False
  with assms(2) have "(\<NN>2, \<TT>2, R2, \<SS>2) = (\<NN>1, \<TT>1, R1, \<SS>1)" by simp 
  then show ?thesis using assms(1) by simp
qed

lemma stage1_2_help':"foldl (\<lambda> a b .step1 b a)  (f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s) p= 
    (f', n', (\<NN>2, \<TT>2, R2, \<SS>2), s') \<Longrightarrow>  \<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1) 
\<Longrightarrow> \<forall>(N, \<alpha>)\<in>R2. N \<in> \<NN>2 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>2 \<union>  \<TT>2)"
proof (induction p arbitrary:  f n \<NN>1 \<TT>1 R1 \<SS>1 s)
  case Nil
  then have "(f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s) =  (f', n', (\<NN>2, \<TT>2, R2, \<SS>2), s')" by simp
  then show ?case using Nil(2) by blast
next
  case (Cons a p)
  obtain f'' n'' \<NN>' \<TT>' R' \<SS>' s'' where step:"(f'', n'', (\<NN>', \<TT>', R', \<SS>'), s'') =
    step1 a (f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s)" apply(cases "step1 a (f, n, (\<NN>1, \<TT>1, R1, \<SS>1), s)") by force
  then  have inv:"\<forall>(N, \<alpha>)\<in>R'. N \<in> \<NN>' \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>' \<union>  \<TT>')" 
   apply(cases a) using step1_valid_rules [OF Cons(3) ] by auto 
  have "foldl (\<lambda> a b .step1 b a) (f'', n'', (\<NN>', \<TT>', R', \<SS>'), s'') p = (f', n', (\<NN>2, \<TT>2, R2, \<SS>2), s')"
    using Cons step by simp
  then show ?case using inv Cons by blast
qed

lemma stage1_2_valid_rules:"\<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1) \<Longrightarrow> 
  stage1_2 p (\<NN>1, \<TT>1, R1, \<SS>1) = (f', n', (\<NN>2, \<TT>2, R2, \<SS>2), s') \<Longrightarrow> 
  \<forall>(N, \<alpha>)\<in>R2. N \<in> \<NN>2 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>2 \<union>  \<TT>2)"
  using stage1_2_help' by fastforce

lemma step2_preserves:
  assumes "\<SS>1 \<in> \<NN>1 " "(\<NN>2, \<TT>2, R2, \<SS>2) = step2 p (f, new, (\<NN>1, \<TT>1, R1, \<SS>1), slot)"
  shows "\<SS>2 \<in> \<NN>2"
proof -
  from assms show ?thesis by auto
qed 

lemma candidate_rules_valid: assumes
    "rul =  candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) s " " \<forall>(N, \<alpha>)\<in>R1 . (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1) "
  shows "\<forall>(N, \<alpha>) \<in> rul . (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" 
proof -
  from assms(1) have "rul \<subseteq>  R1"  apply(simp) by auto  
  then show ?thesis using assms by force
qed

lemma add_rules_valid:
  assumes valid:"\<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" and
          valid_symbol:"symb \<in> \<NN>1" and
          out:"\<RR>2 = add_rules p symb (pre, post) (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1))"
  shows "\<forall>(N, \<alpha>)\<in>\<RR>2. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)"
proof -
  from out valid_symbol have  headvalid:"\<forall>(N, \<alpha>)\<in>\<RR>2. N \<in> \<NN>1" by simp
  from out have 1:"\<forall>(N, \<alpha>) \<in> \<RR>2 . \<alpha> \<in> (snd ` (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) (basic_convert (hd post))))" 
      apply(simp) sorry
  obtain c where 2:"c = (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) (basic_convert (hd post)))" by blast
  with valid have "\<forall>(N, \<alpha>) \<in> c . (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" using candidate_rules_valid by fast
  with 1 2 have "\<forall>(N, \<alpha>) \<in> \<RR>2 . (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" by fastforce
  with headvalid show ?thesis by blast
qed

lemma step2_valid_rules:
  assumes "\<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)"
        "(\<NN>2, \<TT>2, R2, \<SS>2) = step2 p (f, new, (\<NN>1, \<TT>1, R1, \<SS>1), slot)"
        "(N, \<alpha>)\<in>R2"
        "\<forall> s \<in> set new . s \<in> \<NN>1"
  shows " N \<in> \<NN>2 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>2 \<union>  \<TT>2)"
proof (cases "(N, \<alpha>) \<in> R1")
  case True
  from assms(2) have 1:"\<TT>1 \<subseteq>\<TT>2 " by auto
  with assms(2) have 2:"\<NN>1  \<subseteq>\<NN>2" by auto
  with 1 have "\<NN>1 \<union>  \<TT>1 \<subseteq>\<NN>2 \<union> \<TT>2" by auto
  from assms(1) True have "N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union> \<TT>1)" by blast
  with 1 2 show ?thesis by auto 
next
  case False
  then have "(N, \<alpha>) \<in> \<Union>((\<lambda> newsymb. add_rules p newsymb (the (slot newsymb)) (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1))) ` set new)" sorry
  then obtain s \<RR>2 where  val:"s \<in> set new" and add_rules:"(N, \<alpha>) \<in> \<RR>2" and 
    r:" \<RR>2= (add_rules p s (the (slot s)) (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1)))" by auto
  from val assms(4) have "s \<in> \<NN>1" by blast
  with  assms(1) r  have \<RR>2:"\<forall> (N, \<alpha>) \<in> \<RR>2. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union> \<TT>1)" using add_rules_valid  sorry (*should be forceable ...*)
  from assms(2) have 1:"\<TT>1 \<subseteq>\<TT>2 " by auto
  with assms(2) have 2:"\<NN>1  \<subseteq>\<NN>2" by auto
  with 1 have "\<NN>1 \<union>  \<TT>1 \<subseteq>\<NN>2 \<union> \<TT>2" by auto
  from add_rules \<RR>2 have "N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union> \<TT>1)" by blast
  with 1 2 show ?thesis by auto
qed

lemma candidate_rule_finite:"finite R1 \<Longrightarrow> candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) head = R2 \<Longrightarrow> finite R2"
  by force
lemma add_rules_invariant:
  assumes "valid_rules g \<and> finite_R g \<and> rules_convertback g \<and> rules_middle_zero_index g"
          "symb \<in> \<NN>1" 
          "(\<NN>1, \<TT>1, R1, \<SS>1) = g" "\<RR>2 = add_rules p symb (pre, post) (candidate_rules g)"
  shows "\<forall>(N, \<alpha>)\<in>\<RR>2. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1) \<and>
      (\<forall>(N, \<alpha>)\<in>\<RR>2 . (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>) \<and> finite \<RR>2 \<and> (\<forall> (N, \<alpha>) \<in> \<RR>2 . middle_zero_index (N, \<alpha>))"
proof -
  (*could actually rewrite candidate rules to only work on original grammar*)
  from assms have  headvalid:"\<forall>(N, \<alpha>)\<in>\<RR>2. N \<in> \<NN>1" by simp
  from assms have 1:"\<forall>(N, \<alpha>) \<in> \<RR>2 . \<alpha> \<in> (snd ` (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) (basic_convert (hd post))))" 
    apply(simp) sorry
  have "convert_back symb = hd post" sorry (*very important assumption, where to add?*)
  have back_conv:"convert_back (basic_convert (hd post)) = hd post" by (metis backconversion basic_convert.simps)
  with 1 have 2:"\<forall>(N, \<alpha>) \<in> \<RR>2 . convert_back N = hd post" sorry
  from back_conv assms have "\<forall> (N, \<alpha> ) \<in> (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) (basic_convert (hd post))) 
    . (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>" sorry
  with 1 2 have conv:"(\<forall>(N, \<alpha>)\<in>\<RR>2 . (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>)" sorry (*have to  somehow make combination work*)
  have valid :"\<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" using assms by force
  obtain c where 2:"c = (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) (basic_convert (hd post)))" by blast
  with valid have "\<forall>(N, \<alpha>) \<in> c . (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" using candidate_rules_valid by fast
  with 1 2 have "\<forall>(N, \<alpha>) \<in> \<RR>2 . (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" by fastforce
  with headvalid have valid:"\<forall>(N, \<alpha>)\<in>\<RR>2. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)" by fastforce
  from assms have "finite R1" by auto
  then have "finite c" using 2 candidate_rule_finite by blast
  then have fin:"finite \<RR>2" using assms 2 sorry
  (*middle zero*)
  have snd_R1:"\<forall>(N, \<alpha>) \<in> \<RR>2 . (\<exists> N' . (N', \<alpha>) \<in> R1 \<and> convert_back N' = convert_back N)" sorry (*this has to be proven*)
  from assms have "(\<forall> (N, \<alpha>) \<in> R1 . middle_zero_index (N, \<alpha>))" by auto
  with snd_R1 have middle:"\<forall>(N, \<alpha>) \<in> \<RR>2 . middle_zero_index (N, \<alpha>)" by auto
  from conv valid fin middle show ?thesis by simp
qed

(*need to distinguish between left right patterns*)
definition complete_pattern::"('a, 'b) pattern list \<Rightarrow> bool" where
"complete_pattern p  = ((\<lambda> (h, prev, post, p2) . ((h, prev@post), (h, p2))) ` (set p) = (Priority \<union> Left \<union> Right))"

(*big question is where to add the match*)
(*invariant \<longrightarrow> all predecessor are of form p, p', and only match on this one*)

(*really the assumption here is convert_back newsymb = hd p'*)
(*regard this as adding to the slot*)
lemma add_rules_conflictfree':
  assumes "\<RR>2  = (add_rules pattern newsymb (p, p') (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1)))" "valid_pattern p p'""complete_pattern pattern"
        "convert_back newsymb = hd p'" "convertback_rule ` R1 = \<RR>"
      shows "(p = [] \<longrightarrow> convertback_rule ` \<RR>2 = {r | r . r \<in> \<RR> \<and> leftconflictfree' r (hd p', p@p') \<and> fst r = hd p'}) \<and>
    (p \<noteq> [] \<longrightarrow> convertback_rule ` \<RR>2 = {r | r . r \<in> \<RR> \<and> rightconflictfree' r (hd p', p@p') \<and> fst r = hd p'})"  
proof (cases p) (*left head*)
  case Nil
  obtain banned where "banned = set (banned_patterns pattern (hd p') p p')" by blast
  from assms(3) have "banned  = {r | r . (convert_back newsymb, r) \<in> \<RR> \<and> 
    \<not> leftconflictfree' (convert_back newsymb, r) (hd p', p@p')}" sorry
  then obtain banned' where "banned' = {r | r . r \<in> \<RR> \<and> 
    \<not> leftconflictfree' r (hd p', p@p') \<and> fst r = hd p'}" sorry
  (*candidate rules assumption*)
  obtain rules where "rules = (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) ( basic_convert (hd p')))" by blast
  then have "rules  = {r | r. r \<in> R1 \<and> fst r = basic_convert (hd p')}" sorry
  then have "convertback_rule ` {r. \<forall> r \<in> (rules) . (convertback_rule r) \<notin> banned'} 
      = {r | r . r \<in> \<RR> \<and> leftconflictfree' r (hd p', p@p') \<and> fst r = hd p'}" sorry
  with assms(1) have "convertback_rule ` \<RR>2 = 
      {r | r . r \<in> \<RR> \<and> leftconflictfree' r (hd p', p@p') \<and> fst r = hd p'}" sorry 
      (*additional lemma out convertback_newsymp equals the other*)
  then show ?thesis using Nil by auto
next
  case (Cons a list)
   obtain banned where "banned = set (banned_patterns pattern (hd p') p p')" by blast
  from assms(3) have "banned  = {r | r . (convert_back newsymb, r) \<in> \<RR> \<and> 
    \<not> rightconflictfree' (convert_back newsymb, r) (hd p', p@p')}" sorry
  then obtain banned' where "banned' = {r | r . r \<in> \<RR> \<and> 
    \<not> rightconflictfree' r (hd p', p@p') \<and> fst r = hd p'}" sorry
  (*candidate rules assumption*)
  obtain rules where "rules = (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) ( basic_convert (hd p')))" by blast
  then have "rules  = {r | r. r \<in> R1 \<and> fst r = basic_convert (hd p')}" sorry
  then have "convertback_rule ` {r. \<forall> r \<in> (rules) . (convertback_rule r) \<notin> banned'} 
      = {r | r . r \<in> \<RR> \<and> rightconflictfree' r (hd p', p@p') \<and> fst r = hd p'}" sorry
  with assms(1) have "convertback_rule ` \<RR>2 = 
      {r | r . r \<in> \<RR> \<and> rightconflictfree' r (hd p', p@p') \<and> fst r = hd p'}" sorry 
      (*additional lemma out convertback_newsymp equals the other*)
  then show ?thesis using Cons by auto
qed

lemma add_rules_conflictfree'':
  assumes "\<RR>2  = (add_rules pattern newsymb (p, p') (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1)))" "valid_pattern p p'""complete_pattern pattern"
        "convert_back newsymb = hd p'" "convertback_rule ` R1 = \<RR>"
      shows "convertback_rule ` \<RR>2 = {r | r . r \<in> \<RR> \<and>  fst r = hd p' \<and> (hd p', p, p', snd r) \<notin> set pattern}"  
proof - (*left head*)

  show ?thesis sorry
qed

(*one additional invariant needed*)
definition not_in_pattern::"('a \<times> nat, 'b) symbol \<Rightarrow> ('a \<times> nat, 'b) symbol list \<Rightarrow> 
  ('a \<times> nat, 'b) symbol \<Rightarrow> ('a \<times> nat, 'b) symbol list \<Rightarrow> bool" where
"not_in_pattern N \<alpha> N' \<alpha>' = ((N' = hd \<alpha> \<and> 
  convert_back N = convert_back (hd \<alpha>) \<longrightarrow> 
  (convert_back N, [], convert_back_sentence \<alpha>, convert_back_sentence \<alpha>') \<notin> set \<P>)
  \<and> (N' = last \<alpha> \<and> 
  convert_back N = convert_back (last \<alpha>) \<longrightarrow> 
  (convert_back N, convert_back_sentence (butlast \<alpha>), 
  [convert_back (last \<alpha>)], convert_back_sentence \<alpha>') \<notin> set \<P>))"

definition pattern_complete::"('a \<times> nat, 'b) symbol \<Rightarrow> ('a \<times> nat, 'b) symbol list \<Rightarrow> ('a \<times> nat, 'b) rule set \<Rightarrow> bool" where
"pattern_complete N \<alpha> R1  = (\<forall> (N', \<alpha>')\<in> \<RR> . (convert_back (hd \<alpha>) = N' \<and> (convert_back N, [], convert_back_sentence \<alpha>, \<alpha>') \<notin> set \<P> \<longrightarrow> 
(\<exists> (N', \<alpha>'') \<in> R1. (hd \<alpha>) = N' \<and> convert_back_sentence \<alpha>'' = \<alpha>')) \<and> 
(convert_back (last \<alpha>) = N' \<and> (convert_back N, convert_back_sentence (butlast \<alpha>), [convert_back (last \<alpha>)], \<alpha>') \<notin> set \<P> \<longrightarrow> 
(\<exists> (N', \<alpha>'') \<in> R1. (last \<alpha>) = N' \<and> convert_back_sentence \<alpha>'' = \<alpha>')))"

fun pattern_valid::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"pattern_valid (\<NN>1, \<TT>1, R1, \<SS>1) = ((\<forall> (N, \<alpha>) \<in> R1 . \<forall> (N', \<alpha>')\<in> R1 . not_in_pattern N \<alpha> N' \<alpha>') \<and> 
        (\<forall> (N, \<alpha>) \<in> R1 . pattern_complete N \<alpha> R1))"

lemma step2_invariants:
  assumes "step2 p (f, n, g, s) = g'" "fngs_invariants (f, n, g, s)"
  shows "grammar_invariants g'"
proof -
  obtain \<NN>1 \<TT>1 R1 \<SS>1 where g:"(\<NN>1, \<TT>1, R1, \<SS>1) = g" apply(cases g) by blast
  obtain \<NN>2 \<TT>2 R2 \<SS>2 where g':"(\<NN>2, \<TT>2, R2, \<SS>2) = g'" apply (cases g') by blast
  (*start*)
  from assms have start:"start_in_nonterm g'" using g g' by force
  (*term unchanged*)
  from assms have ter:"term_unchanged g'" using g g' by force
  (*nonterm_eq*)
  from assms have nonterm:"nonterm_eq g'" using g g' by force
  (*new rules*)
  from assms(1) g g' have R2:"R2 = (R1 \<union> \<Union>((\<lambda> newsymb. add_rules p newsymb (the (s newsymb)) (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1))) ` set n))"
    by auto
  from assms have 1:"\<forall> n \<in> set n . n \<in> \<NN>1" using g by force
  from assms have "valid_rules g \<and> finite_R g \<and> rules_convertback g" by auto
  with 1 g have 2:"\<forall> n \<in> set n . (\<forall>(N, \<alpha>) \<in> (add_rules p n (the (s n)) (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1))) . (N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)
    \<and> (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>) \<and>  middle_zero_index (N, \<alpha>) \<and>finite (add_rules p n (the (s n)) (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1))))
      "
    using add_rules_invariant sorry 
       (*maybe try other approach later*)
  with R2 have 3:"(\<forall>(N, \<alpha>) \<in> R2  . (N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1)
    \<and> (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>))" sorry
  (*rules valid*)
  from 3 g' g assms(1) have valid:"valid_rules g'" by force
  (*convert_back*)
  from 3 g' have conv:"rules_convertback g'" by auto 
  (*rule zero*)
  from assms(2) have "(\<forall> (N', \<alpha>') \<in> \<RR> . \<exists> (N, \<alpha>) \<in> R1 . is_zero_index N \<and> convertback_rule (N, \<alpha>) = (N', \<alpha>'))" using g by auto
  then have "(\<forall> (N', \<alpha>') \<in> \<RR> . \<exists> (N, \<alpha>) \<in> R2 . is_zero_index N \<and> convertback_rule (N, \<alpha>) = (N', \<alpha>'))" using g R2 by fast
  with g' have zero_index:"zero_index_all g'" by auto
  (*middle zero*)
  from 2 R2 assms(2) have "\<forall> r \<in> R2 . middle_zero_index r" sorry
  with g' have middle:"rules_middle_zero_index g'" sorry
  (*finite r*)
  have "finite (set n)" using assms by blast
  then have "finite R2" using 2 sorry
  then have fin:"finite_R g'" using g' by auto
  (*maybe do things more existence based*)
  (*rule exclusion*)
  (*needs premesis: all rules longer than 2 are covered by newsymb slots*)
  (*prove that that before no rule matched to R1 heads of rules*)
  (*premise*)
  have "\<forall> symbol \<in> set n . Set.filter (\<lambda> (N, \<alpha>) . N = symbol) R1 ={}" sorry
  (*end pointes are use sites*)
  
  have "\<forall> (N, \<alpha>) \<in> R1 . hd \<alpha> \<in> set n \<and> last \<alpha> \<in> set n" sorry
  then have "\<forall> (N, \<alpha>) \<in> R1 . True" sorry
  have "\<forall> (N, \<alpha>) \<in> R2 . \<exists> N' . (N', \<alpha>) \<in> R1 \<and> convert_back N' = convert_back N" sorry 
     (*alternates are the same \<longrightarrow> this can the be used to generalize the previous proof*)
  (*prove via uniqueness \<longrightarrow> each rule of length 2 has unique nonterminal in the end*)
  show ?thesis  by (simp add:fin start ter nonterm valid conv zero_index middle)
qed

lemma step2_valid_rules':"\<forall>(N, \<alpha>)\<in>R1. N \<in> \<NN>1 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>1 \<union>  \<TT>1) \<Longrightarrow> 
(\<NN>2, \<TT>2, R2, \<SS>2) = step2 p (f, new, (\<NN>1, \<TT>1, R1, \<SS>1), slot) \<Longrightarrow> \<forall> s \<in> set new . s \<in> \<NN>1 \<Longrightarrow>\<forall> (N, \<alpha>)\<in>R2 .N \<in> \<NN>2 \<and> (\<forall>s\<in>set \<alpha>. s \<in> \<NN>2 \<union>  \<TT>2)"
  using step2_valid_rules by blast
(*alternative proof approach using valid_start function*)
lemma step3_preserves:"stage3 p (\<NN>1, \<TT>1, \<RR>1, \<SS>1)  = (f, n, (\<NN>2, \<TT>2, \<RR>2, \<SS>2), s) \<Longrightarrow> \<SS>1 \<in> \<NN>1 \<Longrightarrow> \<SS>2 \<in> \<NN>2"
proof -
  assume assms:"stage3 p (\<NN>1, \<TT>1, \<RR>1, \<SS>1)  = (f, n, (\<NN>2, \<TT>2, \<RR>2, \<SS>2), s)" "\<SS>1 \<in> \<NN>1"
  then have step1:"(f, n, (\<NN>2, \<TT>2, \<RR>2, \<SS>2), s) =(let (f, n, g, s) = stage1_2 p  (\<NN>1, \<TT>1, \<RR>1, \<SS>1) in (f, n, step2 p (f, n, g, s), s))" by simp
  then obtain  \<NN>0 \<TT>0 \<RR>0 \<SS>0  
    where 12:" stage1_2 p  (\<NN>1, \<TT>1, \<RR>1, \<SS>1) = (f, n,  (\<NN>0, \<TT>0, \<RR>0, \<SS>0), s)" 
  apply(cases "stage1_2 p  (\<NN>1, \<TT>1, \<RR>1, \<SS>1)") by auto 
  then have step2:"(\<NN>2, \<TT>2, \<RR>2, \<SS>2) = step2 p (f, n,  (\<NN>0, \<TT>0, \<RR>0, \<SS>0), s)" using step1 by simp
  from 12 have "\<SS>0 \<in> \<NN>0" using stage1_2_preserves assms by metis
  with step2 have "\<SS>2 \<in> \<NN>2" using step2_preserves by blast
  then show ?thesis by auto
qed

lemma stage3_invariants:
  assumes "stage3 p G  = (f, n, g, s)" "grammar_invariants G"
  shows "fngs_invariants (f, n, g, s)"
proof -
  obtain f1 n1 g1 s1 where step1:"(f1, n1, g1, s1) = stage1_2 p G"  apply (cases "stage1_2 p G") by auto
  from assms(1) step1 have step2:"(f, n, g, s) = (f1, n1, step2 p (f1, n1, g1, s1), s1)" 
     using step1 apply(simp add: Let_def  del: stage1_2.simps) 
     by (smt (z3) Pair_inject old.prod.case) (*long running*)
  from step1 assms(2) have fngs:"fngs_invariants (f1, n1, g1, s1)" using stage1_2_invariants by metis
  with step2_invariants step2 have grammar_invariants:"grammar_invariants g" by fast
  obtain \<NN>1 \<TT>1 R1 \<SS>1 where g:"(\<NN>1, \<TT>1, R1, \<SS>1) = g" apply(cases g) by blast
  obtain \<NN>2 \<TT>2 R2 \<SS>2 where g1:"(\<NN>2, \<TT>2, R2, \<SS>2) = g1" apply (cases g1) by blast
  from step2 have "\<NN>1 = \<NN>2" using step2 g g1 by force
  with fngs step2 have "new_in_nonterm (f, n, g, s)" using g g1 by force 
  then show ?thesis using grammar_invariants by simp
qed

lemma inl_start:"Inl start \<in> nonterm'"
  by (auto simp add: start_valid nonterm'_def) 

lemma valid_rules_help:"\<forall>(N, \<alpha>) \<in> rules . N \<in> nonterm' \<and> (\<forall> s \<in> set \<alpha> . s \<in> nonterm' \<union> term')"
  apply(simp add: nonterm'_def term'_def new_nonterm_def new_term_def)
  using h1 h2 
  using new_term_def by force
(*prove via the fact that nonterms only increase and start terminal does not change*)

lemma start':"get_s \<GG>' \<in> get_nonterm \<GG>'"
proof - 
  obtain f n \<NN>2 \<TT>2 \<RR>2 \<SS>2 s where 
    assms:"stage3 \<P> (nonterm', term', rules, Inl start) = (f, n, (\<NN>2, \<TT>2, \<RR>2, \<SS>2), s)" 
    apply(cases "stage3 \<P>  (nonterm', term', rules, Inl start)") by auto
  with   inl_start have " \<SS>2 \<in> \<NN>2" using step3_preserves by blast
  with assms \<GG>'_def show ?thesis  by auto
qed

lemma all_zero_index_implies_middle_zero_index:
  assumes "list_all is_zero_index \<alpha> "
  shows "middle_zero_index (N, \<alpha>)"
proof (cases "length \<alpha> < 2")
  case True
  then show ?thesis using assms by simp
next
  case False
  with assms have "\<forall> s \<in> set \<alpha> . is_zero_index s" using list_all_def by metis
  then have "\<forall> s \<in> set (butlast (tl \<alpha>)) . is_zero_index s" 
    by (metis in_set_butlastD list.sel(2) list.set_sel(2))
  then have "list_all is_zero_index (butlast (tl \<alpha>))" using list_all_def by metis
  then show ?thesis using assms by simp
qed

lemma nonterm'_eq:"(convert_back ` nonterm' = Inl ` \<A>)"
  using nonterm'_def new_nonterm_def backconversion by fastforce

lemma zero_rules:"(\<forall> (N', \<alpha>') \<in> \<RR> . \<exists> (N, \<alpha>) \<in> rules . is_zero_index N \<and> convertback_rule (N, \<alpha>) = (N', \<alpha>'))"
  sorry (*proven in grammar 0*)

lemma zero_middle:"(\<forall> (N, \<alpha>) \<in> rules . middle_zero_index (N, \<alpha>))"
proof -
  from valid_rules_help nonterm'_def term'_def have 
    "\<forall>(N, \<alpha>)\<in>rules.  (\<forall>s\<in>set \<alpha>. s \<in>  Inl ` new_nonterm \<union> Inr ` new_term)" by auto
  then have "\<forall>(N, \<alpha>)\<in>rules . list_all is_zero_index \<alpha>"  by (simp add: list_all_def is_zero_index_def)
  then show ?thesis  using 
      all_zero_index_implies_middle_zero_index by auto
qed
lemma orig_inv:"grammar_invariants (nonterm', term', rules, Inl start)"
  using inl_start valid_rules_help finite_rules rule_equality nonterm'_eq zero_middle zero_rules by auto

lemma grammar3_invariants:"fngs_invariants fngs"
  apply(cases fngs) using fngs_def stage3_invariants orig_inv by auto

lemma grammar3_invariants':"grammar_invariants \<GG>'"
proof -
  obtain f n g s where 1:"(f, n, g, s) = fngs" apply(cases fngs) by auto
  then have "g = \<GG>'" using \<GG>'_def fngs_def by (metis split_conv)
  then show ?thesis using grammar3_invariants 1 by (metis fngs_invariants.simps)  
qed

lemma valid_rules:"\<forall>(N, \<alpha>)\<in>\<RR>''. N \<in> Inl ` \<NN>'' \<and> (\<forall>s\<in>set \<alpha>. s \<in> Inl ` \<NN>'' \<union> Inr ` \<TT>'')"
proof -                                  
  from grammar3_invariants' have "valid_rules \<GG>'" by simp
  then have "\<forall>(N, \<alpha>)\<in> get_rule \<GG>'. N \<in> get_nonterm \<GG>' \<and> (\<forall>s\<in>set \<alpha>. s \<in> get_nonterm \<GG>' \<union>  get_term \<GG>')" 
    apply(cases \<GG>') by simp
   then show ?thesis using \<RR>''_def \<NN>''_def \<TT>''_def  apply(auto) sorry
  (*need an inverse operation for inl \inr \<Longrightarrow> extract_inl/inr as helper*)
 qed

lemma start:"\<SS>'' \<in> \<NN>''"
proof - 
  from grammar3_invariants' have "start_in_nonterm \<GG>'" by force
  then show ?thesis  apply(cases \<GG>') using \<SS>''_def \<NN>''_def by simp
qed

lemma valid_rules':" \<forall>x\<in>\<RR>''. case x of (N, \<alpha>) \<Rightarrow> N \<in> Inl ` \<NN>'' \<and> (\<forall>s\<in>set \<alpha>. s \<in> Inl ` \<NN>'' \<or> s \<in> Inr ` \<TT>'')"
  using valid_rules by simp

lemma finite_\<RR>'':"finite  \<RR>''"
  sorry

lemma finite_\<TT>'':"finite \<TT>''"
proof -                   
  have "finite term'"by (simp add: finite_terminals new_term_def term'_def)
  then have "finite (get_term \<GG>')" using grammar3_invariants sorry
  then show ?thesis by (simp add: \<TT>''_def)
qed
interpretation grammar3: CFG \<NN>'' \<TT>'' \<RR>'' \<SS>''
  apply(unfold_locales)
   apply(auto simp add: start finite_\<RR>'' finite_\<TT>'')
   using valid_rules apply blast using valid_rules by auto

lemma rules_convert: "\<forall> (N, \<alpha>) \<in>\<RR>'' . (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>"
  sorry

(*proof via transformation*)
lemma \<GG>'_nonterm:" convert_back ` (get_nonterm \<GG>') = Inl ` \<A>"
  sorry
lemma \<GG>'_term:"get_term \<GG>' = Inr ` new_term"
  apply (simp add: \<GG>'_def new_term_def term'_def)
  sorry
lemma terminal_equality_help:"\<forall> t \<in> \<TT>'' . t \<in> \<B>"
  by (auto simp add: \<TT>''_def \<GG>'_term new_term_def) 

lemma terminal_equality_help':"\<forall>  t \<in> \<B> .t \<in> \<TT>'' "
  apply (auto simp add: \<TT>''_def \<GG>'_term new_term_def )
  by (metis image_eqI sum.sel(2))

lemma \<TT>''_\<B>:"\<TT>'' = \<B>" 
  by (auto simp add: terminal_equality_help terminal_equality_help')

lemma terminal_equality3:"grammar3.is_terminal x \<Longrightarrow> is_terminal (convert_back x)"
  apply(auto simp add: grammar3.is_terminal_def is_terminal_def terminal_equality_help)
  by (simp add: disjE_realizer terminal_equality_help)
lemma nonterminal_equality_help:"\<forall> t \<in> \<NN>'' . (fst t) \<in> \<A>"
  apply (auto simp add: \<NN>''_def \<GG>'_nonterm)
  sorry
lemma nonterminal_equality3:"grammar3.is_nonterminal x \<Longrightarrow> is_nonterminal (convert_back x)"
  apply(auto simp add: grammar3.is_nonterminal_def is_nonterminal_def)
  using nonterminal_equality_help
  by (simp add: disjE_realizer)

(*candidate rules have to be redefined*)
lemma candidate_rules_subset:(*looks like candidate rules is ill defined*)
  "(candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) h) \<subseteq> R1"
  by auto

lemma candidate_rules_eq_set_filter:"((candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) h) = Set.filter (\<lambda> (N, a) . N = h) R1)"
  by simp

(*have to use something along the slots*)

lemma rule_exists_prem_left:
  "\<forall> (N, \<alpha>) \<in> \<RR>'' . (\<forall> (N', \<alpha>') \<in> \<RR> . N' = convert_back (hd \<alpha>) \<and> leftconflictfree' (convertback_rule (N, \<alpha>)) (N', \<alpha>'))
    \<longrightarrow> (\<exists> (N'', \<alpha>'') \<in> \<RR>'' . N'' = hd \<alpha> \<and> convertback_rule (N'', \<alpha>'') = (N', \<alpha>'))"
  sorry
lemma rule_exists_prem_right:
  "\<forall> (N, \<alpha>) \<in> \<RR>'' . (\<forall> (N', \<alpha>') \<in> \<RR> . N' = convert_back (last \<alpha>) \<and> rightconflictfree' (convertback_rule (N, \<alpha>)) (N', \<alpha>'))
    \<longrightarrow> (\<exists> (N'', \<alpha>'') \<in> \<RR>'' . N'' = last \<alpha> \<and> convertback_rule (N'', \<alpha>'') = (N', \<alpha>'))"
  sorry

lemma rules_zero_index:"\<forall> (N, \<alpha>) \<in> \<RR>'' . (length \<alpha> < 2 \<longrightarrow> list_all is_zero_index \<alpha>) \<and>
  (length \<alpha> \<ge> 2 \<longrightarrow> list_all is_zero_index (butlast (tl \<alpha>)))"
  apply(cases \<GG>') using grammar3_invariants' \<RR>''_def by simp

lemma zero_index_all:"\<forall> (N', \<alpha>') \<in> \<RR> . \<exists> (N, \<alpha>) \<in> \<RR>'' . is_zero_index N \<and> convertback_rule (N, \<alpha>) = (N', \<alpha>')"
  apply(cases \<GG>') using grammar3_invariants' \<RR>''_def by simp


lemma candidate_rules_head:"\<forall> (N, \<alpha>) \<in> (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) s) . N =  s"
  by auto

lemma backconversion':"convert_back (convert n h) = h"
  by (metis grammar3.backconversion)
lemma backconversion'':"convert_back (basic_convert h) = h"
  using backconversion' by auto
lemma add_rules_convert:
  assumes valid:"\<forall>(N, \<alpha>)\<in>R1. (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>" and
          equal :"(hd post) = convert_back symb" (**) and
          out:"\<RR>2 = add_rules p symb (pre, post) (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1))"
  shows "\<forall>(N, \<alpha>)\<in>\<RR>2. (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>"
proof -
  from out  have  headvalid:"\<forall>(N, \<alpha>)\<in>\<RR>2. N = symb" by simp (*additional lemma needed*)
  from out have 1:"\<forall>(N, \<alpha>) \<in> \<RR>2 . \<alpha> \<in> (snd ` (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) (basic_convert (hd post))))" 
    apply(simp) sorry
  obtain c where 2:"c = (candidate_rules (\<NN>1, \<TT>1, R1, \<SS>1) (basic_convert (hd post)))" by blast
  then have "\<forall>(N, \<alpha>) \<in> c . N = (basic_convert (hd post))" using candidate_rules_head by fast
  then have "\<forall> (N, \<alpha>) \<in> c. convert_back N = hd post" using backconversion'' by fast
  with 2 valid have "\<forall>(N, \<alpha>) \<in> c . (hd post, convert_back_sentence \<alpha>) \<in> \<RR>" using candidate_rules_subset by fastforce(*through subset relation*)
  with equal have "\<forall>(N, \<alpha>) \<in> c . (convert_back symb, convert_back_sentence \<alpha>) \<in> \<RR>" by simp
  with 1 2 headvalid have "\<forall>(N, \<alpha>) \<in> \<RR>2 . (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>" by fastforce
  then show ?thesis by simp
qed

lemma rule_equality3:"(N, \<alpha>) \<in> \<RR>'' \<Longrightarrow> (convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>"
proof -
  assume "(N, \<alpha>) \<in> \<RR>''"
  then  show ?thesis 
    using rules_convert by fastforce
qed

theorem grammar3_sub_grammar1:"grammar3.Tree_wf T  \<Longrightarrow> 
  \<exists> T'. Tree_wf T' \<and> convertback_rule (DeriveFromTree T) = DeriveFromTree T'"
proof (induction T )
  case (Leaf x)
  then have 1:"grammar3.is_terminal x" by simp
  have s:"DeriveFromTree (Leaf x) = (x, [x])" by simp
  then have a:"convert_back_sentence [x] = [convert_back x]" by simp
  from 1 have terminal:"is_terminal (convert_back x)" using terminal_equality3 by blast
  obtain leaf where def:"leaf = (Leaf (convert_back x))" by blast
  with terminal have wf:"Tree_wf leaf" by simp
  from def a s have  "convertback_rule (DeriveFromTree (Leaf x))= DeriveFromTree leaf" by simp
  with wf show ?case by blast
next
  case (Inner x)
    then have 1:"grammar3.is_nonterminal x" by simp
  have s:"DeriveFromTree( Inner x) = (x, [x])" by simp
  then have a:"convert_back_sentence [x] = [convert_back x]" by simp
  from 1 have terminal:"is_nonterminal (convert_back x)" using nonterminal_equality3 by blast 
  obtain leaf where def:"leaf = (Inner (convert_back x))" by blast    
  with terminal have wf:"Tree_wf leaf" by simp
  from def a s have  "convertback_rule  (DeriveFromTree (Inner x))= DeriveFromTree leaf" by simp
  with wf show ?case by blast
next
  case (DT r b)
  then have validrule:"r \<in> \<RR>''" by auto 
  obtain N \<alpha> where na:"N = fst r \<and> \<alpha> = snd r" by blast
  with validrule have valid_rule:"(convert_back N, convert_back_sentence \<alpha>) \<in> \<RR>" using rule_equality3 by auto
  from DT.prems(1) na have \<alpha>:"\<alpha> = map (\<lambda> t. fst (DeriveFromTree t)) b " 
    using grammar3.TreeSym_equal_DeriveFrom_root'' by force
  from na have N_root:"N = fst (DeriveFromTree (DT r b))" by auto
      (*downright impossible to convert unless ? define specific conversion function*)
  (*how to apply IH on all subtrees in list?*)
  from DT(2) have "list_all grammar3.Tree_wf b" by simp
  then have "list_all (\<lambda> t. \<exists> T' . Tree_wf T' \<and> DeriveFromTree T' = convertback_rule (DeriveFromTree t)) b" using DT(1) sorry
  then obtain b'' where ih:" list_all2 (\<lambda>T' t. Tree_wf T' \<and> DeriveFromTree T' = 
    convertback_rule (DeriveFromTree t)) b'' b" using implied_existence' by fast
  then have b''_wf:"list_all Tree_wf b''" and b''_deriv:"list_all2 (\<lambda>T' t. DeriveFromTree T' = 
    convertback_rule (DeriveFromTree t)) b'' b" using list_all2_implies_list_all list_all2_implies 
     apply (metis (no_types, lifting)) using ih list_all2_implies by fast
  then have b''_conv:"map (\<lambda> t . convertback_rule (DeriveFromTree t)) b = map DeriveFromTree b''" by (metis list_all2_map2)
  then have "map (\<lambda> t . fst (convertback_rule (DeriveFromTree t))) b = (map (\<lambda> t. fst (DeriveFromTree t))b'')" 
    using map_map sorry
  then have "map (\<lambda> t . convert_back (fst (DeriveFromTree t))) b = (map (\<lambda> t. fst (DeriveFromTree t))b'')"
    by (simp add: convertback_rule_split)
  then have "map convert_back (map (\<lambda> t . fst (DeriveFromTree t)) b) = (map (\<lambda> t. fst (DeriveFromTree t))b'')"
    using map_map [where ?f="convert_back"] sorry
  then have valid_subtrees:"convert_back_sentence \<alpha> =  
    (map (\<lambda> t . (fst (DeriveFromTree t))) b'')" using \<alpha> by simp (*explicit function needed*)
  then have valid_subtrees':"convert_back_sentence \<alpha> = concat (map TreeSym b'')" using TreeSym_equal_DeriveFrom_root'' 
    by presburger  
  (*derivation eq*)
  from b''_conv have "map (\<lambda> t . snd (convertback_rule (DeriveFromTree t))) b = (map (\<lambda> t. snd(DeriveFromTree t))b'')" sorry
  then have conv:"map (\<lambda> t . convert_back_sentence (snd (DeriveFromTree t))) b = (map (\<lambda> t. snd (DeriveFromTree t))b'')"
    by (simp add: convertback_rule_split)
  then have "map convert_back_sentence (map (\<lambda> t . snd (DeriveFromTree t)) b) = map (\<lambda> t. snd (DeriveFromTree t)) b''" 
      using map_map [where ?f="convert_back" and ?g="\<lambda> t. fst (DeriveFromTree t)"] sorry 
  (*using concat_map or something*)
  have a:"snd (DeriveFromTree (DT r b)) = (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b))" by simp
  from map_concat [where ?f="convert_back" and ?xs="(map (\<lambda> t . snd (DeriveFromTree t)) b)"]
  have "convert_back_sentence (snd (DeriveFromTree (DT r b))) = (concat( map (convert_back_sentence )
     (map (\<lambda>subtree .  (snd (DeriveFromTree subtree))) b)))" 
     by (metis convert_back_sentence.simps map_eq_conv a)
  then have deriv:"convert_back_sentence (snd (DeriveFromTree (DT r b))) = 
      (concat( map (\<lambda>t . (convert_back_sentence (snd (DeriveFromTree t)))) b))" using map_map sorry (*using map_map*)
  
  with ih have derive':"convert_back_sentence (snd (DeriveFromTree (DT r b))) = 
    (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b''))" using conv by auto
  obtain T' where tree:"T' = (DT (convert_back N, convert_back_sentence \<alpha>) b'')" by blast
  then have wf:"Tree_wf T'" using valid_rule valid_subtrees' ih    b''_wf by simp
  from tree have derive'':"snd (DeriveFromTree T') = convert_back_sentence (snd (DeriveFromTree (DT r b)))" 
    using derive' by force
  from N_root have "convert_back (fst (DeriveFromTree (DT r b))) = fst (DeriveFromTree T')" using tree by simp
  with tree derive'' have "DeriveFromTree T' = convertback_rule (DeriveFromTree(DT r b))" by simp
  with wf show ?case by auto
qed
lemma terminal_equality4:"is_terminal t \<Longrightarrow> grammar3.is_terminal (convert n t)" 
  apply(auto simp add: grammar3.is_terminal_def  is_terminal_def terminal_equality_help')
  by (simp add: disjE_realizer terminal_equality_help')


lemma nonterminal_equality_help':"\<forall> t \<in> \<NN>'' . (fst t) \<in> \<A>"
  apply (auto simp add: \<NN>''_def \<GG>'_nonterm)
  sorry
lemma nonterminal_equality4:"is_nonterminal x \<Longrightarrow> grammar3.is_nonterminal (convert 0 i)"
  apply(auto simp add: grammar3.is_nonterminal_def is_nonterminal_def)
  sorry

fun same_shape::"('a, 'b) derivtree \<Rightarrow> ('a \<times> nat, 'b) derivtree \<Rightarrow> bool" where
"same_shape (DT r b) (DT r' b') = ((r = convertback_rule r') \<and> (list_all2 same_shape b b'))"|
"same_shape (Leaf l) (Leaf l') = (l = convert_back l')"|
"same_shape (Inner i) (Inner i') = (i = convert_back i')"|
"same_shape _ _ = False"
(*or is something of same shape \<Longrightarrow>*)
(*conflict free trees have a tree in the other grammar of the same shape*)


(*need a certain formulation of rules being available under certain circumstances*)
lemma pattern_filtering:"\<forall>(N, \<alpha>) \<in> \<RR>'' . (\<forall> (N', \<alpha>) \<in> \<RR>'' . (N' = hd \<alpha> \<longrightarrow> rightconflictfree' (
    convertback_rule (N, \<alpha>)) (convertback_rule (N', \<alpha>')))\<and> (N' = last \<alpha> \<longrightarrow> leftconflictfree' (
    convertback_rule (N, \<alpha>)) (convertback_rule (N', \<alpha>'))))  "
  sorry

fun match::"('a, 'b) rule \<Rightarrow> ('a \<times> nat, 'b)  symbol \<Rightarrow>('a \<times> nat, 'b) rule" where
"match r s =  undefined"

lemma "r \<in> \<RR> \<Longrightarrow> convert_back s  = fst r \<Longrightarrow>  (match r s) \<in> \<RR>''" sorry


lemma convertback_rule_snd:"snd (convertback_rule r) = convert_back_sentence (snd r)" 
  by (metis convertback_rule.simps snd_conv surjective_pairing)

fun conflictfree_root'::"('a, 'b) derivtree \<Rightarrow> bool" where
"conflictfree_root' (DT r b) = (rightconflictfree r (last b) \<and> leftconflictfree r (hd b))" |
"conflictfree_root' _ = True"

(*has to be proven from the invariants*)
theorem grammar3_conflict_free':"grammar3.Tree_wf T \<Longrightarrow> conflictfree_root' (convert_tree T)"
proof -
  have "(\<forall> p \<in> set \<P> . valid_root_pattern p (convert_tree T))" sorry (*holds because of our root problem*)
  then show ?thesis sorry
qed

(*conflict free helpers*)
type_synonym ('c , 'd) parents = "('c \<times> nat, 'd) rule option\<times> ('c \<times> nat, 'd) rule option"

lemma [case_names NoneNone SomeNone NoneSome SomeSome, cases type: parents]:
  "(y = (None, None) \<Longrightarrow> P) \<Longrightarrow> (\<And>a. y = (Some a, None) \<Longrightarrow> P) 
    \<Longrightarrow> (\<And>a. y = (None, Some a) \<Longrightarrow> P) \<Longrightarrow> (\<And>a  b. y = (Some b, Some a) \<Longrightarrow> P ) \<Longrightarrow> P"
  by (metis not_None_eq surj_pair)

fun depth1_conflict_free::"('a, 'b) parents \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"depth1_conflict_free (None, None) _ = True" |
"depth1_conflict_free (Some l, None) t = ((fst (DeriveFromTree t) = convert_back (last (snd l))) \<and> 
    rightconflictfree (convertback_rule l) t)" | (*parent on left side*)
"depth1_conflict_free (None, Some r) t = ((fst (DeriveFromTree t) = convert_back (hd (snd r))) \<and> 
    leftconflictfree (convertback_rule r) t)"|
"depth1_conflict_free _  t = False"

fun matching_root::"('a \<times> nat, 'b) symbol \<Rightarrow> ('a, 'b) parents \<Rightarrow> bool" where
"matching_root s (None, None)   = (s \<in> Inl ` new_nonterm \<or> s \<in> Inr ` new_term)" | (*only if zero indexed or terminal*)
"matching_root  s (Some l, None)  = (last (snd l) = s) "|
"matching_root s (None, Some r) = (hd (snd r) = s)"|
"matching_root _ _ = False"

fun valid_parent::"('a, 'b) parents  \<Rightarrow> bool" where
"valid_parent (None, None)  = True"|
"valid_parent (Some l, None)  = (l \<in> \<RR>'')"|
"valid_parent (None, Some l)  = (l \<in> \<RR>'')"|
"valid_parent (Some l, Some r) = False"

(*have to prove that there do not exist trees with a conflict of depth 1 in new grammar*)
lemma pattern_valid:"pattern_valid \<GG>'"
  sorry

lemma rule_exists_prem_left':"(N, \<alpha>) \<in> \<RR>'' \<Longrightarrow> (N', \<alpha>') \<in> \<RR> \<Longrightarrow> N' = convert_back (hd \<alpha>) 
  \<and> leftconflictfree' (convertback_rule (N, \<alpha>)) (N', \<alpha>')
    \<Longrightarrow> (\<exists> (N'', \<alpha>'') \<in> \<RR>'' . N'' = hd \<alpha> \<and> convertback_rule (N'', \<alpha>'') = (N', \<alpha>'))"
  using rule_exists_prem_left sorry

lemma rule_exists_prem_right':"(N, \<alpha>) \<in> \<RR>'' \<Longrightarrow> (N', \<alpha>') \<in> \<RR> \<Longrightarrow> N' = convert_back (last \<alpha>) 
  \<and> rightconflictfree' (convertback_rule (N, \<alpha>)) (N', \<alpha>')
    \<Longrightarrow> (\<exists> (N'', \<alpha>'') \<in> \<RR>'' . N'' = last \<alpha> \<and> convertback_rule (N'', \<alpha>'') = (N', \<alpha>'))"
  using rule_exists_prem_right sorry

(*proven from lemma proven over rewriting*)
lemma rule_exists:
  assumes "valid_parent pred "  "depth1_conflict_free pred  (DT r b)" "Tree_wf (DT r b)"
  shows "\<exists> (N, \<alpha>) \<in> \<RR>'' . convertback_rule (N, \<alpha>) = r \<and> matching_root N pred"
proof -
  obtain N' \<alpha>' where r_def:"(N', \<alpha>') =  r" apply(cases r) by simp
  with assms have valid:"(N', \<alpha>') \<in> \<RR>" by simp
  show ?thesis 
  proof (cases pred)
    case NoneNone
    then show ?thesis using zero_index_all valid r_def 
      by (smt (z3) case_prodE case_prodI is_zero_index_def matching_root.simps(1))
  next
    case (SomeNone a)
    with assms have a_valid:"a \<in> \<RR>''" by fastforce
    obtain N \<alpha> where a_def:"(N, \<alpha>) = a" apply(cases a ) by simp
    with SomeNone assms have match:"(N' = convert_back (last \<alpha>) \<and> 
    rightconflictfree (convertback_rule a) (DT r b))" using r_def by auto
    then have conflictfree:"rightconflictfree' (convertback_rule (N, \<alpha>)) (N', \<alpha>')" using r_def a_def by auto
    then have "(\<exists> (N'', \<alpha>'') \<in> \<RR>'' . N'' = last \<alpha> \<and> convertback_rule (N'', \<alpha>'') = (N', \<alpha>'))" 
       using rule_exists_prem_right' valid a_valid match conflictfree a_def by blast 
    then show ?thesis using SomeNone a_def r_def by auto
  next
    case (NoneSome a)
     with assms have a_valid:"a \<in> \<RR>''" by fastforce
    obtain N \<alpha> where a_def:"(N, \<alpha>) = a" apply(cases a ) by simp
    with NoneSome assms have match:"(N' = convert_back (hd \<alpha>) \<and> 
    leftconflictfree (convertback_rule a) (DT r b))" using r_def by auto
    then have conflictfree:"leftconflictfree' (convertback_rule (N, \<alpha>)) (N', \<alpha>')" using r_def a_def by auto
    then have "(\<exists> (N'', \<alpha>'') \<in> \<RR>'' . N'' = hd \<alpha> \<and> convertback_rule (N'', \<alpha>'') = (N', \<alpha>'))" 
       using rule_exists_prem_left' valid a_valid match conflictfree a_def by blast 
    then show ?thesis using NoneSome a_def r_def by auto
  next
    case (SomeSome a b)
    then show ?thesis using assms by simp
  qed
qed

lemma conversion_id:"is_terminal (convert_back s) \<Longrightarrow>(convert n (convert_back s)) = s"
  by (metis CFG.backconversion CFG.is_terminal_nonterminal CFG_axioms 
is_nonterminal_startsymbol nonterminal_equality3 nonterminal_equality4)


lemma terminal_equality4':"is_terminal x \<Longrightarrow> convert_back s = x \<Longrightarrow> grammar3.is_terminal s"
  using terminal_equality4 [where ?t="convert_back s"] conversion_id by auto
(*additional conditions needed to make sure that s is actually a nonterminal*)
lemma nonterminal_equality4':
  assumes "is_nonterminal x " " s \<in> (Inl ` \<NN>'' \<union> Inr ` \<TT>'') "" convert_back s = x "
  shows " grammar3.is_nonterminal s"
proof (cases "s \<in> Inr ` \<TT>''")
  case True
  then have "s \<in> Inr ` \<B>" using \<TT>''_\<B>  by simp
  then have 1:"x \<in> Inr ` \<B>"  using assms(3) by auto
  from assms have 2:"x \<in> Inl ` \<A>" using is_nonterminal_def by auto
  from 1 2 show ?thesis by force
next
  case False
  with assms have "s \<in> (Inl ` \<NN>'')" by blast
  then show ?thesis using grammar3.is_nonterminal_def by auto
qed

lemma convert_back_sentence_comm:"convert_back_sentence (concat (map (\<lambda> t . snd(DeriveFromTree t)) b)) = 
  (concat (map (\<lambda> t . convert_back_sentence (snd(DeriveFromTree t))) b))"
proof -
  have 1:"(concat (map (\<lambda> t . convert_back_sentence (snd(DeriveFromTree t))) b)) = 
        ((concat (map convert_back_sentence (map (\<lambda> t . (snd(DeriveFromTree t))) b))) )" 
      using map_map [where ?f="convert_back_sentence"] 
      by (smt (z3) containsRuleRight.simps(1) containsRuleRight.simps(2) insert_left.simps(2) insert_left.simps(3)) 
  have "convert_back_sentence (concat (map (\<lambda> t . snd(DeriveFromTree t)) b)) = 
    concat (map (map convert_back) (map (\<lambda> t . snd(DeriveFromTree t)) b))" 
    using map_concat[where ?f ="convert_back" and ?xs="(map (\<lambda> t . snd(DeriveFromTree t)) b)"] by auto
  then have  "convert_back_sentence (concat (map (\<lambda> t . snd(DeriveFromTree t)) b)) = 
    concat (map (convert_back_sentence) (map (\<lambda> t . snd(DeriveFromTree t)) b))" 
    by (metis (no_types, lifting) convert_back_sentence.simps map_eq_conv)
  with 1 show ?thesis by auto
qed

lemma convertback_rule_snd_map:"map (\<lambda> t . snd (convertback_rule (DeriveFromTree t))) b = 
  map (\<lambda> t .convert_back_sentence (snd (DeriveFromTree t))) b"
proof -
  have "(\<lambda> t . (convertback_rule (DeriveFromTree t))) = (\<lambda> t . (convert_back (fst (DeriveFromTree t)),
      convert_back_sentence (snd (DeriveFromTree t ))))" 
    by (metis convertback_rule.simps surjective_pairing)
  then  show ?thesis 
    using convertback_rule_snd by presburger 
qed

lemma convert_tree_implies_deriv_conversion:
  "convert_tree T' = T \<Longrightarrow> convertback_rule (DeriveFromTree T') = DeriveFromTree T"
proof (induction T')
  case (Leaf x)
  then show ?case by auto
next
  case (Inner x)
  then show ?case by auto
next
  case (DT r b)
  obtain b' where b':"b' = map convert_tree b" by blast
  obtain r' where r':"r' = convertback_rule r" by blast
  with DT(2) have T:"T = (DT r' b')" by (simp add: r' b')
  from b' DT have 1:"map DeriveFromTree b' = map (\<lambda> t .DeriveFromTree (convert_tree t)) b" by simp
  then have b'_b:"map ( \<lambda> t. snd ( DeriveFromTree t)) b' = map (\<lambda> t . snd (DeriveFromTree (convert_tree t))) b" 
    sorry
  from DT(1) have 2:"map (\<lambda> t .convertback_rule (DeriveFromTree t)) b  = map (\<lambda> t .DeriveFromTree (convert_tree t)) b" 
    by (meson conflict_case rotate_left.simps)
  then have "map (\<lambda> t .convert_back_sentence (snd (DeriveFromTree t))) b = 
    map (\<lambda> t . snd (DeriveFromTree (convert_tree t))) b" using convertback_rule_snd_map by fastforce
  then have "convert_back_sentence (concat (map (\<lambda> t . snd(DeriveFromTree t)) b)) = 
      concat (map (\<lambda> t . snd (DeriveFromTree (convert_tree t))) b)" using convert_back_sentence_comm by metis
  (*need commutativity of convertback and concats, + snd in there*)
  then have "convert_back_sentence (concat (map (\<lambda> t . snd(DeriveFromTree t)) b)) 
    = concat (map (\<lambda> t . snd (DeriveFromTree t)) b')" by (simp add: b'_b)
  then have 3:"convert_back_sentence (snd (DeriveFromTree (DT r b))) = (snd (DeriveFromTree (DT r' b')))"
    by simp
  from r' have "convert_back (fst (DeriveFromTree (DT r b))) = (fst (DeriveFromTree (DT r' b')))"
      apply(cases r) by simp 
  with 3 T show ?case by auto
qed

theorem grammar3_super_conflict_free':"Tree_wf T \<Longrightarrow> depth1_conflict_free pred  T \<Longrightarrow> conflict_free' T \<Longrightarrow> valid_parent pred
  \<Longrightarrow> \<exists> T'. grammar3.Tree_wf T' \<and>  convert_tree T' = T \<and> matching_root (fst (DeriveFromTree T')) pred"
proof (induct T arbitrary: pred)
  case (Leaf x)
  then have 1:"is_terminal x" by simp
  obtain s a where  "(s, a) = DeriveFromTree (Leaf x)" by auto
  then have s:"s = x \<and> a = [x]" by simp 
  then show ?case 
  proof (cases pred)
    case NoneNone
    from 1 have terminal:"grammar3.is_terminal (convert 0 x)" 
      using terminal_equality4 by force
      obtain leaf where def:"leaf = (Leaf (convert 0 x))" by blast
      with terminal have wf:"grammar3.Tree_wf leaf" by simp
      obtain s' a' where  deriv:"DeriveFromTree leaf = (s', a')" by force
      with def have s'_def:"s' = (convert 0 x) \<and> a' = [convert 0 x]" by auto
      with  s have  s':"convert_back s' = s \<and> convert_back_sentence a' = a" using backconversion' by auto 
      then have conv:"convert_tree (leaf) = Leaf x" using def s'_def s by simp
      from 1 s'_def have "s' \<in> Inr ` \<B>" 
        by (meson grammar3.is_terminal_nonterminal is_nonterminal_startsymbol nonterminal_equality4 terminal) 
      then have "s' \<in> Inr ` new_term" by (simp add: new_term_def)
      then have "matching_root (fst (DeriveFromTree leaf)) pred" using deriv NoneNone by auto
      then show ?thesis using conv wf by blast 
   next
    case (SomeNone a)
     then have conv:"fst (DeriveFromTree (Leaf x)) = convert_back (last (snd a))" using Leaf.prems(2)
         using depth1_conflict_free.simps(2) by blast
    then obtain s' where s'_def:"s' = (last (snd a))" by blast
    have "a \<in> \<RR>''" using Leaf.prems(4) SomeNone valid_parent.simps(2) by blast
    then have s'_symbol:"s' \<in> (Inl ` \<NN>'' \<union> Inr ` \<TT>'')" using validRules s'_def sorry
    (*is this even needed?*)
    have conv':"x = convert_back s'" using conv s'_def by simp
    then have "grammar3.is_terminal s'" using terminal_equality4' 1 by blast
    then have wf:"grammar3.Tree_wf (Leaf s') \<and> convert_tree (Leaf s') = Leaf x" using conv' by simp
    have "matching_root (fst (DeriveFromTree (Leaf s'))) pred" using SomeNone s'_def by auto
    then show ?thesis using wf by blast
  next
    case (NoneSome a)
    then have conv:"fst (DeriveFromTree (Leaf x)) = convert_back (hd (snd a))" using Leaf.prems(2)
      using depth1_conflict_free.elims(2) by blast
    then obtain s' where s'_def:"s' = (hd (snd a))" by blast
    have "a \<in> \<RR>''" using Leaf.prems(4) NoneSome using valid_parent.elims(2) by blast
    then have s'_symbol:"s' \<in> (Inl ` \<NN>'' \<union> Inr ` \<TT>'')" using validRules s'_def sorry
    have conv':"x = convert_back s'" using conv s'_def by simp
    then have "grammar3.is_terminal s'" using terminal_equality4' 1 by presburger
    then have wf:"grammar3.Tree_wf (Leaf s') \<and> convert_tree (Leaf s') = Leaf x" using conv' by simp
    have "matching_root (fst (DeriveFromTree (Leaf s'))) pred" using NoneSome s'_def by auto
    then show ?thesis using wf by blast
  next
    case (SomeSome a b)
    then have "\<not> depth1_conflict_free pred (Leaf x)" by simp
    then show ?thesis  using Leaf.prems(2) by auto
  qed
next
  case (Inner x)
  (*base*)
  then have 1:"is_nonterminal x" by simp
  obtain s a where "(s, a) = DeriveFromTree (Leaf x)" by auto
  then  have s:"s = x \<and> a = [x]" by simp
  then show ?case 
  proof (cases pred)
    case NoneNone
    from 1 have terminal:"grammar3.is_nonterminal (convert 0 x)" using nonterminal_equality4 by blast
    obtain leaf where def:"leaf = (Inner (convert 0 x))" by blast
    with terminal have wf:"grammar3.Tree_wf leaf" by simp
    obtain s' a' where  deriv:"DeriveFromTree leaf = (s', a')" by force
    with def have s'_def:"s' = (convert 0 x) \<and> a' = [convert 0 x]" by auto
    with  s have  s':"convert_back s' = s \<and> convert_back_sentence a' = a" using backconversion' by auto 
    then have conv:"convert_tree (leaf) = Inner x" using def s'_def s by simp
    from  1 is_nonterminal_def have "x \<in> Inl ` \<A>" 
      by (metis CFG.backconversion CFG_axioms nonterminal_equality3 nonterminal_equality4 old.sum.simps(6))
    then have "s' \<in> Inl ` new_nonterm" using s'_def new_nonterm_def by force 
    then have "matching_root (fst (DeriveFromTree leaf)) pred" using deriv NoneNone by auto
    then show ?thesis using conv wf by auto
  next
    case (SomeNone a)
    then have conv:"fst (DeriveFromTree (Inner x)) = convert_back (last (snd a))" using Inner.prems(2)
      using depth1_conflict_free.elims(2) by blast
    then obtain s' where s'_def:"s' = (last (snd a))" by blast
    have "a \<in> \<RR>''" using Inner.prems(4) SomeNone using valid_parent.elims(2) by blast
    then have s'_symbol:"s' \<in> (Inl ` \<NN>'' \<union> Inr ` \<TT>'')" using validRules s'_def 
      sorry
    have conv':"convert_back s' =x " using conv s'_def by simp
    then have "grammar3.is_nonterminal s'" using nonterminal_equality4' [OF 1 s'_symbol] by presburger
    then have wf:"grammar3.Tree_wf (Inner s') \<and> convert_tree (Inner s') = Inner x" using conv' by simp
    have "matching_root (fst (DeriveFromTree (Inner s'))) pred" using SomeNone s'_def by auto
    then show ?thesis using wf by blast
next
case (NoneSome a)
    then have conv:"fst (DeriveFromTree (Inner x)) = convert_back (hd (snd a))" using Inner.prems(2)
      using depth1_conflict_free.elims(2) by blast
    then obtain s' where s'_def:"s' = (hd (snd a))" by blast
    have "a \<in> \<RR>''" using Inner.prems(4) NoneSome using valid_parent.elims(2) by blast
    then have s'_symbol:"s' \<in> (Inl ` \<NN>'' \<union> Inr ` \<TT>'')" using validRules s'_def 
      sorry
    have conv':"x = convert_back s'" using conv s'_def by simp
    then have "grammar3.is_nonterminal s'" using nonterminal_equality4' [OF 1 s'_symbol] by presburger
    then have wf:"grammar3.Tree_wf (Inner s') \<and> convert_tree (Inner s') = Inner x" using conv' by simp
    have "matching_root (fst (DeriveFromTree (Inner s'))) pred" using NoneSome s'_def by auto
    then show ?thesis using wf by blast
next
  case (SomeSome a b)
  then have "\<not> depth1_conflict_free pred (Inner x)" by simp
  then have "False" using Inner.prems(2) by auto
  then show ?thesis by blast
qed
next
  case (DT r b) (*actually needs a case distinction between lengths \<longrightarrow> head rules with length < 2, should not have filtering there*)
  obtain N \<alpha> where rule:"(N, \<alpha>) \<in> \<RR>'' \<and> convertback_rule (N, \<alpha>) = r \<and> matching_root N pred" 
    using DT.prems DT.prems rule_exists  by (smt (z3) case_prodE)
   (*middle trees*)
  from DT.prems have subtrees:"\<forall> t \<in> set b . Tree_wf t  \<and> conflict_free' t" apply(simp) using list_all_def by metis
  then have mid:"\<forall> t \<in> set (butlast (tl b)) . Tree_wf t  \<and> conflict_free' t" 
    by (metis in_set_butlastD list.sel(2) list.set_sel(2))

  then show ?case
  proof (cases "length (snd r) \<ge>2")
    case True
    then have b_nonempty:"length b \<ge>2" using DT.prems(1) sorry (*additional lemma needed*)
    have "\<forall> t \<in> set (butlast (tl b)) . depth1_conflict_free (None, None) t \<and> valid_parent (None, None)" by fastforce
    with mid have "\<forall> t \<in> set (butlast (tl b)) . depth1_conflict_free (None, None) t \<and> 
          valid_parent (None, None) \<and> Tree_wf t  \<and> conflict_free' t" by simp
    with DT(1) have mid':" \<forall> t \<in> set (butlast (tl b)) . (\<exists>T'. grammar3.Tree_wf T' \<and> 
      convert_tree T' = t \<and> matching_root (fst (DeriveFromTree T')) (None, None))" 
      by (metis in_set_butlastD list.sel(2) list.set_sel(2))
  (*effectively by default, now have to add matching root for these*)
    obtain midb where "midb = (butlast (tl b))" by blast
    with mid' have "list_all (\<lambda> t . (\<exists>T'. grammar3.Tree_wf T' \<and> 
      convert_tree T' = t \<and> matching_root (fst (DeriveFromTree T')) (None, None))) midb" by (simp add: list_all_def)
    then obtain midbconv where midconv:"list_all2 (\<lambda> T' T. grammar3.Tree_wf T' \<and> 
      convert_tree T' = T \<and> matching_root (fst (DeriveFromTree T')) (None, None)) midbconv midb" 
      using implied_existence' by fast
    then have "list_all (\<lambda> T'. grammar3.Tree_wf T' \<and> matching_root (fst (DeriveFromTree T')) (None, None)) midbconv" sorry (*how to remove ?*)
    then have T'_wf:"list_all (\<lambda> T'. grammar3.Tree_wf T') midbconv" and "\<forall> i \<in> set midbconv . ((fst (DeriveFromTree i)) \<in> 
    (Inl ` new_nonterm \<union>  Inr ` new_term))" sorry
    from midconv have "list_all2 (\<lambda> T' T. convert_tree T' = T) midbconv midb" sorry (*and based,  list_all_imply?*)
    then have "map convert_tree midbconv = midb" using list_all2_map by blast
    then have  midcorr:"list_all grammar3.Tree_wf midbconv \<and>  map convert_tree midbconv = midb" 
        by (simp add: T'_wf)
    
    (*if convert_back is the same and both have the same index \<longrightarrow> same value*)
    have mid_roots:"map (fst \<circ> DeriveFromTree) midbconv = (butlast (tl \<alpha>))" sorry (*needs a statement about
      middle being zero indexed \<longrightarrow> part of the invariants*)
    
     (*hd *)
      have prem:"hd b \<in> set b" by (meson conflict_case rotate_left.simps)
      from subtrees have valid_hd:"Tree_wf (hd b)" and conflictfree_hd:" conflict_free' (hd b)" 
        using prem apply blast using prem subtrees by fastforce
      from rule DT.prems(1) have match:"(fst (DeriveFromTree (hd b)) = convert_back (hd (\<alpha>)))" sorry (*matching on the character*)
      from DT.prems(3) have "leftconflictfree r (hd b)" by simp
      then have conflict_free:"depth1_conflict_free (None, Some (N, \<alpha>)) (hd b)" using match sorry (*look at formulation again*)
      have valid_parent:"valid_parent (None, Some (N, \<alpha>))" using rule by auto
      then have  hd_exists:
        "\<exists> T'. grammar3.Tree_wf T' \<and>  convert_tree T' = hd b \<and> matching_root (fst (DeriveFromTree T')) (None, Some (N, \<alpha>))"  
        using  DT(1) [OF prem valid_hd conflict_free conflictfree_hd valid_parent] by blast
      then have "\<exists> T'. grammar3.Tree_wf T' \<and>  convert_tree T' = hd b \<and> ((fst (DeriveFromTree T')) = hd \<alpha>)"
        by fastforce
      then obtain T' where hd_corr:"grammar3.Tree_wf T' \<and>  convert_tree T' = hd b " and hd_roots:"((fst (DeriveFromTree T')) = hd \<alpha>)"
        by blast
      (*tl*)
      have prem:"last b \<in> set b" sorry
      from subtrees have valid_last:"Tree_wf (last b)" and conflictfree_last:" conflict_free' (last b)" 
        using prem subtrees apply simp using prem subtrees by simp
      from rule DT.prems(1) have match':"(fst (DeriveFromTree (last b)) = convert_back (last (\<alpha>)))" sorry (*matching on the character*)
      from DT.prems(3) have "rightconflictfree r (last b)" by simp
      then have conflict_free':"depth1_conflict_free (Some (N, \<alpha>), None) (last b)" using match' sorry (*look at formulation again*)
      have valid_parent':"valid_parent (Some (N, \<alpha>), None)" using rule by auto
      then have  tl_exists:
        "\<exists> T'. grammar3.Tree_wf T' \<and>  convert_tree T' = last b \<and> matching_root (fst (DeriveFromTree T')) (Some (N, \<alpha>), None)"  
        using  DT(1) [OF prem valid_last conflict_free' conflictfree_last valid_parent'] by blast
      then have "\<exists> T'. grammar3.Tree_wf T' \<and>  convert_tree T' = last b \<and> ((fst (DeriveFromTree T')) = last \<alpha>)"
        by fastforce
      then obtain T'' where tl_corr:"grammar3.Tree_wf T'' \<and>  convert_tree T'' = last b" and 
            tl_roots:"((fst (DeriveFromTree T'')) = last \<alpha>)"
        by blast
  
      (*need to change the nonempty statement to work*)
      have "\<alpha> = map (fst \<circ> DeriveFromTree ) (T'#midbconv@[T''])" using tl_roots hd_roots mid_roots sorry 
      then have concat:"\<alpha> = concat (map grammar3.TreeSym (T'#midbconv@[T'']))" sorry
      have  convert_tree:"convert_tree T' # map convert_tree midbconv @ [convert_tree T''] = b" 
        using tl_corr hd_corr midcorr (* drop_last*) sorry 
      obtain T where T_def:"T = (DT (N, \<alpha>) (T'#midbconv@[T'']))" by blast
      then have T_wf:"grammar3.Tree_wf T" using concat tl_corr rule hd_corr midcorr by fastforce
      have root:"matching_root N  pred" using rule by blast
      have "convertback_rule (N, \<alpha>) = r" using rule by blast
      then have "convert_tree T = (DT r b)" using T_def convert_tree by simp
      with T_wf have "\<exists>T'. grammar3.Tree_wf T' \<and> convert_tree T' = (DT r b) \<and> 
            matching_root (fst (DeriveFromTree T')) pred" using root T_def by fastforce 
    then show ?thesis sorry
  next
    case False
    then have b_nonempty:"length b = 1" using DT.prems(1) sorry (*additional lemma needed*) (*should rules be nonempty*)
    have "\<alpha> = [hd \<alpha>]" sorry (*singleton implication*)
    (*hd *)
    have prem:"hd b \<in> set b" sorry
    from subtrees have valid_hd:"Tree_wf (hd b)" and conflictfree_hd:" conflict_free' (hd b)" using prem subtrees
          apply fast using subtrees prem by fast
    from rule DT.prems(1) have match:"(fst (DeriveFromTree (hd b)) = convert_back (hd (\<alpha>)))" sorry (*matching on the character*)
      from DT.prems(3) have "leftconflictfree r (hd b)" by simp
      then have conflict_free:"depth1_conflict_free (None, None) (hd b)" using match by auto
      have valid_parent:"valid_parent (None, None)" using rule by auto
      then have  hd_exists:
        "\<exists> T'. grammar3.Tree_wf T' \<and>  convert_tree T' = hd b \<and> matching_root (fst (DeriveFromTree T')) (None, None)"  
        using  DT(1) [OF prem valid_hd conflict_free conflictfree_hd valid_parent] by blast
      then have "\<exists> T'. grammar3.Tree_wf T' \<and>  convert_tree T' = hd b \<and> ((fst (DeriveFromTree T') \<in> Inl ` new_nonterm  \<union> Inr ` new_term))"
        by fastforce
      then obtain T' where hd_corr:"grammar3.Tree_wf T' \<and>  convert_tree T' = hd b " and 
         hd_roots:"((fst (DeriveFromTree T') \<in> Inl ` new_nonterm  \<union> Inr ` new_term))"
        by blast
      (*need additional term relating nonzero to this*)
      (*combining*)
      from rule False have "length \<alpha> = length (snd r)" by auto
      with False have "length \<alpha> < 2" by force
      with rule  rules_zero_index have zero_index:"list_all is_zero_index \<alpha>" apply(cases r) by blast
      (*match on basis symbol*)
      from hd_corr have "convert_back (fst (DeriveFromTree T')) = fst (DeriveFromTree (hd b))"
        sorry
      (*with zero index matching *)
      with hd_roots zero_index have "hd \<alpha> = (fst (DeriveFromTree T'))" sorry
      then have match:"\<alpha> = concat (map grammar3.TreeSym [T'])" sorry (*may need more lemmas*)
      obtain T where T_def:"T = DT (N, \<alpha>) [T']" by blast
      then have wf:"grammar3.Tree_wf T" using match rule hd_corr by simp 
      (*convert tree*)
      from b_nonempty have "[hd b] = b" sorry
      then have "map convert_tree [T'] = b" using hd_corr by simp
      then have "convert_tree T = DT r b" using T_def rule by simp
      then show ?thesis using wf rule T_def by fastforce
  qed
qed
  
(*in this case here, we know that the immediate child node as a (DT r' b') exists*)

theorem grammar3_sub_grammar2:"Tree_wf T \<Longrightarrow> (s, a) = DeriveFromTree T \<Longrightarrow> 
 conflict_free' T \<Longrightarrow> \<exists> T'. convert_tree T' = T \<and> grammar3.Tree_wf T'"
  using grammar3_super_conflict_free' [where ?T= "T" and ?pred = "(None, None)"] by auto

(*additional formulation needed to relate *)
theorem grammar3_sub_grammar2':"Tree_wf T \<Longrightarrow> (s, a) = DeriveFromTree T \<Longrightarrow> 
 conflict_free' T \<Longrightarrow> \<exists> T'. convert_tree T' = T \<and> grammar3.Tree_wf T' 
    \<and> ((fst (DeriveFromTree T'))  \<in> Inl ` new_nonterm \<union>  Inr ` new_term)"
  using grammar3_super_conflict_free' [where ?T= "T" and ?pred = "(None, None)"] by auto

lemma is_word'':"is_word xa \<Longrightarrow> map projr xa = map projr (map (convert 0) xa)"
  apply(auto simp add: is_word_def is_terminal_def)
  by (metis old.sum.simps(5) old.sum.simps(6) projr_def sum.exhaust_sel)

lemma is_word''_help:"is_word xa \<and> convert_back_sentence xs = xa \<Longrightarrow> map (convert 0) xa = xs"
  apply(auto simp add: is_word_def is_terminal_def) 
  sorry

lemma word_derivations:
  assumes "is_word xa"  "DeriveFromTree tree = (\<SS>, xa) " "Tree_wf tree" 
   (*would use completeness lemma*) 
  shows "grammar3.is_word (map (convert 0) xa) \<and> grammar3.is_derivation  (map (convert 0) xa)" 
proof -
  have "conflict_free' tree" sorry (*using completeness lemma*)
  with assms obtain T' where 
    T':"grammar3.Tree_wf T' \<and>  convert_tree T' = tree \<and> matching_root (fst (DeriveFromTree T')) (None, None)"
    using grammar3_super_conflict_free' [where ?T= "tree" and ?pred = "(None, None)"] by auto
  then have "fst (DeriveFromTree T') = Inl \<SS>''" (*using Projections*) sorry
  then have 1:"fst (DeriveFromTree T') = grammar3.\<SS>" using grammar3.\<SS>_def by simp
  (*snd*)
  from T' have "convert_back_sentence ( snd (DeriveFromTree T')) = xa" sorry
  with assms have 2:"( snd (DeriveFromTree T')) = map (convert 0) xa 
    \<and> grammar3.is_word (map (convert 0) xa)" sorry
        (*should have working lemma*)
  from T' obtain D' where  "grammar3.Derivation [grammar3.\<SS>] D' (map (convert 0)xa)"  
     by (metis  grammar3.DerivationTree_implies_Derivation 1 2) 
  then show ?thesis using 2 grammar3.is_derivation_def grammar3.Derivation_implies_derives by blast
qed


theorem grammar3_all_conflict_free:"grammar3.Tree_wf T  \<Longrightarrow>  
   conflict_free' (convert_tree T) \<and> Tree_wf (convert_tree T) \<and> 
  convertback_rule (DeriveFromTree T) = DeriveFromTree (convert_tree T)"
proof (induct T )
  case (Leaf x)
  then have 1:"grammar3.is_terminal x" by simp
  obtain s a where "(s, a) = DeriveFromTree (Leaf x)" by auto
  then have s:"s = x \<and> a = [x]" by simp
  then have a:"convert_back_sentence a = [convert_back x]" by simp
  from 1 have terminal:"is_terminal (convert_back x)" using terminal_equality3 by auto  
  obtain leaf where def:"leaf = (Leaf (convert_back x))" by blast
  with terminal have wf:"Tree_wf leaf" by simp
  from def a s have  deriv:"(convert_back s, convert_back_sentence a )= DeriveFromTree leaf" by simp
  from def have "conflict_free leaf" by force
  with wf deriv def show ?case by simp
next
  case (Inner x)
   then have 1:"grammar3.is_nonterminal x" by simp
  obtain s a where "(s, a) = DeriveFromTree (Inner x)" by auto
  then have s:"s = x \<and> a = [x]" by simp
  then have a:"convert_back_sentence a = [convert_back x]" by simp
  from 1 have terminal:"is_nonterminal (convert_back x)" 
    using nonterminal_equality3 by blast
  obtain leaf where def:"leaf = (Inner (convert_back x))" by blast
  with terminal have wf:"Tree_wf leaf" by simp
  from def a s have  deriv:"(convert_back s, convert_back_sentence a )= DeriveFromTree leaf" by simp
  from def have "conflict_free leaf" by force
  with wf deriv def show ?case by auto
next
  case (DT r b)
  from DT.prems(1) have validrule:"r \<in> \<RR>''" by auto (*need implication that *)
  obtain N \<alpha> where na:"N = fst r \<and> \<alpha> = snd r" by blast 
  with validrule have valid_rule:"convertback_rule r \<in> \<RR>" 
    by (metis CFG.convertback_rule.simps CFG_axioms prod.collapse rule_equality3)
  from DT.prems(1) have "snd r = concat (map grammar3.TreeSym b)" by simp 
  then have "snd r = concat (map (\<lambda> t . [fst (DeriveFromTree t)]) b)" 
      using grammar3.TreeSym_implies_DeriveFrom_root by presburger
  with na have "convert_back_sentence \<alpha> = concat (map (\<lambda> t . [convert_back (fst (DeriveFromTree t))]) b)" by auto
  from DT.prems have wf_subtrees:"list_all grammar3.Tree_wf b" by auto
  from DT.prems have deriv_subtrees:"snd (DeriveFromTree (DT r b)) = 
    (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b))" by auto 
  then obtain b'' where ih:"b'' = map convert_tree b" by blast
  (*induction hypothesis*)
  with wf_subtrees DT(1) have wf_converted:"list_all Tree_wf b''" 
    sorry
  from DT(1) wf_subtrees have conflictfree_converted:"list_all conflict_free' b''" 
    sorry(*why does this hold \<longrightarrow> there seems to be some inconsistency*)
  (*both of these derive from the third case*)

  from DT(1) wf_subtrees have r':"\<forall> x \<in> set b . convertback_rule (DeriveFromTree x) = 
    DeriveFromTree (convert_tree x)" using list_all_def by metis
  then  have fst:"\<forall> x \<in> set b . convert_back (fst (DeriveFromTree x)) = 
    fst (DeriveFromTree (convert_tree x))"  and  
    snd:"\<forall> x \<in> set b . convert_back_sentence (snd (DeriveFromTree x)) = 
    snd (DeriveFromTree (convert_tree x))"  apply(metis convertback_rule_split) by(metis convertback_rule_split r') 

  from fst ih have match:"convert_back_sentence \<alpha>= map (\<lambda> t . fst (DeriveFromTree t)) b''" 
    sorry
  then have valid_subtrees':"convert_back_sentence \<alpha> = concat (map TreeSym b'')" using TreeSym_equal_DeriveFrom_root'' 
    by fastforce
  from snd deriv_subtrees ih have "(concat( map (\<lambda>subtree . convert_back_sentence (snd (DeriveFromTree subtree))) b)) = 
    (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b''))"
    by (metis DeriveFromTree.simps(1) convert_back_sentence_comm convert_tree.simps(3) 
        convert_tree_implies_deriv_conversion convertback_rule_snd snd_conv) 
  then have deriv_converted:"convert_back_sentence (snd (DeriveFromTree (DT r b))) = 
    (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b''))"     
    by (metis DeriveFromTree.simps(1) convert_back_sentence_comm 
        convert_tree_implies_deriv_conversion convertback_rule_snd snd_conv)
  (*construct tree*)
   obtain T' where tree:"T' = convert_tree (DT r b)" by blast
  then have T'_def:"T' = DT (convertback_rule r) b''" using ih by auto
  (*well_formedness of converted tree*)
  then have wf:"Tree_wf T'" using valid_rule  wf_converted valid_subtrees'  na  match convertback_rule_snd by auto
  (*derivation equality*)
  from T'_def have "convert_back (fst (DeriveFromTree (DT r b ))) = fst (DeriveFromTree T')"
    by (metis convertback_rule.simps fst_conv prod.collapse root_symbol)
  with deriv_converted T'_def have deriv:"convertback_rule (DeriveFromTree (DT r b )) = DeriveFromTree T'" by simp
  (*conflict free*)

  from DT.prems(1) tree have "conflictfree_root' T'" using grammar3_conflict_free' by blast
  then have "rightconflictfree (convertback_rule r) (last b'') \<and> leftconflictfree (convertback_rule r) (hd b'')" 
      using T'_def by simp
  with conflictfree_converted have "conflict_free' T'" using T'_def by simp 
  then show ?case using wf deriv tree by fast

qed

lemma terminal_equality3_help:"grammar3.is_terminal x \<Longrightarrow> (is_terminal \<circ> convert_back) x"
  using terminal_equality3 by simp




lemma grammar3_is_word_implies_is_word:"grammar3.is_word xa \<Longrightarrow> is_word (convert_back_sentence xa)"
  apply(simp add: grammar3.is_word_def is_word_def)
  using terminal_equality3_help list_all_map [where ?f="is_terminal" and ?g="convert_back" and ?b="xa"]
    list_all_implies list.pred_map by blast
  
lemma word_derivations':
  assumes "grammar3.is_word xa "" DeriveFromTree tree = (grammar3.\<SS>, xa) "" grammar3.Tree_wf tree "
  shows "is_word (convert_back_sentence xa) \<and> is_derivation  (convert_back_sentence xa)"
proof -
  obtain T where "T = convert_tree tree" by blast
  with assms(3) have 1:"conflict_free' T \<and> Tree_wf T \<and> convertback_rule (DeriveFromTree tree) = DeriveFromTree T" 
    using grammar3_all_conflict_free by simp
  then have "DeriveFromTree T = (convert_back grammar3.\<SS>, convert_back_sentence xa)" using assms by auto
  then have "DeriveFromTree T = (\<SS>, convert_back_sentence xa)" sorry (*needs the additional lemma*)
  then have 2:"is_derivation (convert_back_sentence xa)" using DerivationTree_implies_Derivation is_derivation_def
  Derivation_implies_derives 1 by fastforce
  show ?thesis using 2 assms grammar3_is_word_implies_is_word by blast 
qed

lemma is_word''':"grammar3.is_word xa \<Longrightarrow> map projr xa = map projr (convert_back_sentence xa)"
  apply(auto simp add: grammar3.is_word_def grammar3.is_terminal_def)
   by (metis old.sum.simps(5) old.sum.simps(6) projr_def sum.exhaust_sel)

theorem grammar3:" \<L>_t = grammar3.\<L>_t "
  apply(auto simp add: \<L>_t_def grammar3.\<L>_t_def  \<L>_def  grammar3.\<L>_def is_derivation_def 
      dest!: derives_implies_Derivation DerivationSymbol_implies_DerivTree [OF _ \<SS>_symbol])
  using word_derivations is_word'' apply fastforce
  apply(auto simp add: grammar3.is_derivation_def 
        dest!: grammar3.derives_implies_Derivation grammar3.DerivationSymbol_implies_DerivTree  )
  using grammar3.\<SS>_symbol apply blast
  using word_derivations' is_word''' is_derivation_def by blast
end



end