theory Stage4Rewriting

imports Rewriting1 Stage3Rewriting

begin 


section "Stage 4 of rewriting"

fun y_alt::"('a  \<times> nat , 'c) grammar \<Rightarrow> ('a  \<times> nat, 'c) symbol \<Rightarrow> ('a, 'c) symbol list \<Rightarrow> ('a \<times> nat, 'c) symbol list set" where
"y_alt G head delta = {\<alpha> . \<forall> (N, \<alpha>) \<in> candidate_rules G head . plainrule \<alpha> \<noteq> delta}"

(*! the (f s) possible -1*)
fun set_alternates::" ('a, 'c) symbol \<Rightarrow>  ((('a, 'c) symbol) \<Rightarrow> nat option) \<Rightarrow> ('a \<times> nat, 'c) symbol list" where
"set_alternates s f = (map (\<lambda> n. convert n s)[0..<(the (f s))])"

(*
lemma needed for termination proof
"all set alternates rule alternatives form a subset of the original one"
*)

fun replace_rule::"('a \<times> nat, 'c ) symbol \<Rightarrow> ('a \<times> nat, 'c) symbol \<Rightarrow> ('a \<times> nat, 'c) grammar \<Rightarrow> 
   ( ('a \<times> nat, 'c) symbol \<times> ('a \<times> nat, 'c) symbol list \<times>  ('a \<times> nat, 'c ) symbol list) 
  \<Rightarrow> ('a \<times> nat, 'c ) grammar" where
"replace_rule y y1 (\<NN>, \<TT>, R, s) (s1, mu, theta) = (\<NN>\<union>{y1}, \<TT>, 
    ({(s1, mu@[y1]@theta)}\<union>{r. \<forall> r \<in> R . r \<noteq> (s1, mu@[y]@theta)}) ,s)"

fun extend_grammar::"('a \<times> nat, 'c) grammar \<Rightarrow>  ('a\<times> nat, 'c) symbol \<Rightarrow> ('a\<times> nat, 'c) symbol list set 
\<Rightarrow> ('a\<times> nat, 'c) grammar" where
"extend_grammar (\<NN>, \<TT>, R, s) symbol rule = (\<NN>\<union>{symbol}, \<TT>, (R\<union>((\<lambda>r. (symbol, r)) ` rule)), s)"


(*for termination formalize reduction of alternates*)
(*maybe define order on grammars which is defined by these functions*)
fun apply_pattern::" ((('a, 'c) symbol) \<Rightarrow> nat option) \<Rightarrow>('a\<times> nat, 'c) grammar \<Rightarrow> ('a\<times> nat, 'c) symbol 
   \<Rightarrow> ('a, 'c) symbol list \<Rightarrow> 
( ('a\<times> nat, 'c) symbol \<times> ('a\<times> nat, 'c) symbol list \<times>  ('a\<times> nat, 'c) symbol list) \<Rightarrow> (('a\<times> nat, 'c) grammar \<times> ('a\<times> nat, 'c) symbol \<times>  ((('a, 'c) symbol) \<Rightarrow> nat option))" where
"apply_pattern f grammar w delta (s, mu, theta) = (let alt = y_alt grammar w delta in 
(let set = filter (\<lambda>sym. candidate_rules' grammar sym = alt) (set_alternates (plain w) f) in
if ([] =  set) then (let f = (fresh f (plain w)) in 
                      (let y' =  (convert (the (f (plain w)))  (plain w)) in 
                  (replace_rule  w y' (extend_grammar grammar y' alt)  (s, mu, theta), w, f)))  
               else (replace_rule  w (hd set) grammar  (s, mu, theta), hd set , f) ))"


(*lemmas*)
(*
lemma apply_pattern_soundness: "derive grammar w \<Rightarrow> legal pattern w \<Rightarrow> derive (apply_pattern grammar) w"
*)
(*given a patttern a right_recursive rule y_i = \<mu>W, apply pattern foldwise*)
fun right_step4::"(('a \<times> nat, 'c) symbol \<times>  ('a \<times> nat, 'c)symbol list \<times>  ('a \<times> nat, 'c) symbol list) 
        \<Rightarrow> ('a \<times> nat, 'c) symbol \<Rightarrow>  ('a, 'c) pattern 
    \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"right_step4 (s, mu, theta) W (s', p, p', p1) (f, n, g, slot) = (let (g', new_symbol', f') = 
      apply_pattern f g W p1 (s, mu, theta)
    in (f', new_symbol'#n, g', slot(new_symbol' \<mapsto> (the (slot (W))))))" (*maybe new should be a set*)

fun right_step3::"(('a \<times> nat, 'c) symbol \<times>  ('a \<times> nat, 'c)symbol list \<times>  ('a \<times> nat, 'c) symbol list)
      \<Rightarrow> ('a \<times> nat, 'c) symbol \<Rightarrow>
       ('a, 'c) pattern list \<Rightarrow>
      ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"right_step3 rule W  p (f, n, g, s) = foldr (right_step4 rule W)  p (f, n, g, s)"
fun same_nonterm::"('a \<times> nat, 'c) symbol \<Rightarrow> ('a \<times> nat, 'c) symbol \<Rightarrow> bool" where
"same_nonterm s s' = (convert_back s = convert_back s')"

fun rightrecursive::"('a \<times> nat, 'c) symbol \<Rightarrow> bool" where
"rightrecursive s = undefined" (*\<exists> z . s \<in> rightrecursive z*)

fun candidate_rules_right::"('a \<times> nat, 'c) symbol \<Rightarrow> ('a \<times> nat, 'c) rule set \<Rightarrow> ('a \<times> nat, 'c) rule set" where
"candidate_rules_right Y_i \<R> = {(N, \<alpha>) . \<forall> (N, \<alpha>) \<in> \<R> . same_nonterm (last \<alpha>) Y_i \<and> rightrecursive (last \<alpha>)}"

(*iterates over all rules in \<GG>'*)
(*need to recheck whether (N, butlast \<alpha>, []) is correct*)
fun right_step2::"('a::ccompare \<times> nat, 'c::ccompare) symbol \<Rightarrow> ('a, 'c) pattern list \<Rightarrow> ('a \<times> nat, 'c) grammar 
  \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"right_step2 symbol P (\<NN>''' , \<TT>''', R, \<SS>''') (f, n, g, slot) = 
  foldl (\<lambda> fngs (N, \<alpha>).  right_step3 (N, [], tl \<alpha>) (hd \<alpha>) P fngs)  
  (f, n, g, slot) (csorted_list_of_set (candidate_rules_right symbol R))"

(*lemma after this step, for all previous rules in input grammar, an alternative is removed if and only if it lead to conflicts*)
(*this lemma can then be used to prove that conflict free trees have an equivalent tree*)
lemma convertback_rule_snd:"snd (convertback_rule r) = convert_back_sentence (snd r)" 
  sorry

fun filterPattern::"('a, 'c) pattern list \<Rightarrow> (('a, 'c) symbol list \<times> ('a, 'c) symbol list) 
  \<Rightarrow> ('a,'c) pattern list" where
"filterPattern p rule = filter (\<lambda>(s, p1, p1', p2). (p1, p1') = rule) p"

(*iterates overall slots with leftrecursive head*)
fun apply_right_step1::"('a::ccompare \<times> nat, 'c::ccompare) symbol \<Rightarrow> ('a, 'c) pattern list \<Rightarrow> ('a \<times> nat, 'c) grammar \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"apply_right_step1 symbol P G' (f, n, g, slot) = (if [] =  fst(the (slot symbol)) 
    then right_step2 symbol (filterPattern P (the (slot symbol)))G' (f, n, g, slot) 
    else (f, n, g, slot))"

(*careful with new*)

fun left_step4::"(('a \<times> nat, 'c) symbol \<times>  ('a \<times> nat, 'c)symbol list \<times>  ('a \<times> nat, 'c) symbol list) 
        \<Rightarrow> ('a \<times> nat, 'c) symbol \<Rightarrow>  ('a, 'c) pattern 
    \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"left_step4 (s, mu, theta) W (s', p, p', p1) (f, n, g, slot) = (let (g', new_symbol', f') = 
      apply_pattern f g W p1 (s, mu, theta)
    in (f', new_symbol'#n, g', slot(new_symbol' \<mapsto> (the (slot (W))))))" (*maybe new should be a set*)

fun left_step3::"(('a \<times> nat, 'c) symbol \<times>  ('a \<times> nat, 'c)symbol list \<times>  ('a \<times> nat, 'c) symbol list)
      \<Rightarrow> ('a \<times> nat, 'c) symbol \<Rightarrow>
       ('a, 'c) pattern list \<Rightarrow>
      ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"left_step3 rule W  p (f, n, g, s) = foldr (left_step4 rule W)  p (f, n, g, s)"

fun leftrecursive::"('a \<times> nat, 'c) symbol \<Rightarrow> bool" where
"leftrecursive s = undefined" (*\<exists> z . s \<in> rightrecursive z*)

fun candidate_rules_left::"('a \<times> nat, 'c) symbol \<Rightarrow> ('a \<times> nat, 'c) rule set \<Rightarrow> ('a \<times> nat, 'c) rule set" where
"candidate_rules_left Y_i \<R> = {(N, \<alpha>) . \<forall> (N, \<alpha>) \<in> \<R> . same_nonterm (hd \<alpha>) Y_i \<and> leftrecursive (hd \<alpha>)}"


(*iterates over all rules in \<GG>'*)
fun left_step2::"('a::ccompare \<times> nat, 'c::ccompare) symbol \<Rightarrow> ('a, 'c) pattern list \<Rightarrow> ('a \<times> nat, 'c) grammar 
  \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"left_step2 symbol P (\<NN>''' , \<TT>''', R, \<SS>''') (f, n, g, slot) = 
  foldl (\<lambda> fngs (N, \<alpha>).  left_step3 (N, butlast \<alpha>, []) (last \<alpha>) P fngs)  
  (f, n, g, slot) (csorted_list_of_set (candidate_rules_left symbol R))"

(*lemma after this step, for all previous rules in input grammar, an alternative is removed if and only if it lead to conflicts*)
(*this lemma can then be used to prove that conflict free trees have an equivalent tree*)

fun filterPattern'::"('a, 'c) pattern list \<Rightarrow> (('a, 'c) symbol list \<times> ('a, 'c) symbol list) 
  \<Rightarrow> ('a,'c) pattern list" where
"filterPattern' p rule = filter (\<lambda>(s, p1, p1', p2). (p1, p1') = rule) p"

(*iterates overall slots with leftrecursive head*)
fun apply_left_step1::"('a::ccompare \<times> nat, 'c::ccompare) symbol \<Rightarrow> ('a, 'c) pattern list \<Rightarrow> ('a \<times> nat, 'c) grammar \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"apply_left_step1 symbol P G' (f, n, g, slot) = (if [] =  fst(the (slot symbol)) 
    then left_step2 symbol (filterPattern P (the (slot symbol)))G' (f, n, g, slot) 
    else (f, n, g, slot))"

fun apply_step0::"('a::ccompare \<times> nat, 'c::ccompare) symbol \<Rightarrow> ('a, 'c) pattern list \<Rightarrow> ('a \<times> nat, 'c) grammar \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"apply_step0 symbol P G' fngs = apply_right_step1 symbol P G' (apply_left_step1 symbol P G' fngs)"


fun step0::"('a::ccompare, 'c::ccompare) pattern list \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a, 'c) fresh_new_g_slot" where
"step0 P (f, n, g, slot) = foldl (\<lambda> fngs symbol . apply_step0 symbol P g fngs)  (f, n, g, slot) n"

function stage4::"('a::ccompare, 'c::ccompare) pattern list \<Rightarrow> ('a \<times> nat, 'c ) grammar \<Rightarrow>  ('a \<times>nat, 'c) recursrel \<Rightarrow> ('a \<times>nat, 'c) recursrel \<Rightarrow> ('a, 'c) fresh_new_g_slot \<Rightarrow> ('a \<times> nat, 'c) grammar" where
"stage4 p g' l r (f, n, g'', s) = (if (g' = g'') then g'' else stage4 p g'' l r (step0 p  (f, n, g'', s)) ) "
  by pat_completeness auto termination sorry 

context Pattern
begin

(*function that denotes right right recursive functions in a grammar*)
definition rightrecurs::"('a \<times> nat, 'b) recursrel" where
"rightrecurs = undefined" (*has to be defined*)

definition leftrecurs::"('a \<times> nat, 'b) recursrel" where
"leftrecurs = undefined" (*has to be defined*)

definition \<P>'::"('a::ccompare, 'b::ccompare) pattern list" where
"\<P>' = undefined"

definition \<GG>''::"('a \<times> nat, 'b) grammar" where
"\<GG>'' = stage4 \<P> \<GG>' leftrecurs rightrecurs fngs"
definition \<NN>'''::"('a \<times> nat) set" where
"\<NN>''' = projl ` (get_nonterm \<GG>'')"

definition \<TT>'''::"'b set" where
"\<TT>''' = projr ` (get_term \<GG>'')"

definition \<RR>'''::"('a \<times> nat, 'b) rule set" where
"\<RR>''' = get_rule \<GG>''"

definition \<SS>'''::"'a \<times> nat" where
"\<SS>''' = projl (get_s \<GG>'')"

section "Helpers"
(*Should be able to use the step invariants for everything including valid grammar*)


fun term_start_unchanged::"('a \<times> nat, 'b) grammar \<Rightarrow> ('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"term_start_unchanged (\<NN>1, \<TT>1, \<RR>1, \<SS>1) (\<NN>0, \<TT>0, \<RR>0, \<SS>0) =  (\<SS>1 = \<SS>0 \<and> \<TT>1 = \<TT>0)"

(*first argument new grammar*)
fun nonterm_sub::"('a \<times> nat, 'b) grammar \<Rightarrow> ('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"nonterm_sub (\<NN>1, \<TT>1, \<RR>1, \<SS>1) (\<NN>0, \<TT>0, \<RR>0, \<SS>0) =  (\<NN>0 \<subseteq> \<NN>1)"

fun valid_grammar::"('a \<times> nat, 'b) grammar \<Rightarrow> bool" where
"valid_grammar (\<NN>1, \<TT>1, \<RR>1, \<SS>1) = (\<forall> (N, \<alpha>) \<in> \<RR>1 . N \<in> \<NN>1 \<and> (\<forall> s \<in> set \<alpha> . s \<in> (\<NN>1 \<union> \<TT>1)))"

lemma invariants_refl:"nonterm_sub \<GG>0  \<GG>0 \<and> term_start_unchanged  \<GG>0  \<GG>0"
  by (smt (z3) nonterm_sub.simps old.prod.exhaust order_refl prod.inject term_start_unchanged.elims(3))

lemma nonterm_sub':
  assumes "(\<NN>0', \<TT>0', \<RR>0', \<SS>0') = G''  \<and> (\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0 \<and> nonterm_sub G'' \<GG>0 "
  shows" \<RR>0 \<subseteq> \<RR>0'"
proof -
  have "nonterm_sub (\<NN>0', \<TT>0', \<RR>0', \<SS>0') (\<NN>0, \<TT>0, \<RR>0, \<SS>0)" using assms by auto
  then show ?thesis sorry

qed


lemma nonterm_transitive:
  assumes "nonterm_sub G' \<GG>0 \<and> nonterm_sub G'' G'"
  shows" nonterm_sub G'' \<GG>0" 
proof -
  obtain   \<NN>0 \<TT>0 \<RR>0 \<SS>0 where 1:"(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0" using assms  by (metis nonterm_sub.elims(2))
  obtain   \<NN>' \<TT>' \<RR>' \<SS>' where 2:"(\<NN>', \<TT>', \<RR>', \<SS>') = G'" using assms  by (metis nonterm_sub.elims(2))
  obtain   \<NN>'' \<TT>'' \<RR>'' \<SS>'' where 3:"(\<NN>'', \<TT>'', \<RR>'', \<SS>'') = G''" using assms  by (metis nonterm_sub.elims(2))
  then have "\<RR>0 \<subseteq> \<RR>'" using nonterm_sub' assms  1 2  by fast
  then have "\<RR>0 \<subseteq> \<RR>''" using nonterm_sub' assms 2 3 by fast
  then have "nonterm_sub (\<NN>'', \<TT>'', \<RR>'', \<SS>'') (\<NN>0, \<TT>0, \<RR>0, \<SS>0)" 
    using "1" "2" "3" assms by force
  then show ?thesis using 1 3 by fast
qed


lemma term_start_transitive:
  assumes "term_start_unchanged G' \<GG>0 \<and> term_start_unchanged G'' G'"
  shows" term_start_unchanged G'' \<GG>0" 
proof -
  obtain   \<NN>0 \<TT>0 \<RR>0 \<SS>0 where 1:"(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0" using assms by (metis valid_grammar.cases)
  obtain   \<NN>' \<TT>' \<RR>' \<SS>' where 2:"(\<NN>', \<TT>', \<RR>', \<SS>') = G'" using assms  by (metis valid_grammar.cases)
  obtain   \<NN>'' \<TT>'' \<RR>'' \<SS>'' where 3:"(\<NN>'', \<TT>'', \<RR>'', \<SS>'') = G''" using assms  by (metis valid_grammar.cases)
  then have "\<SS>0 = \<SS>' \<and> \<TT>0 = \<TT>'" using  assms  1 2  by auto
  then have "\<SS>0 = \<SS>'' \<and> \<TT>0 = \<TT>''" using  assms 2 3 by auto
  then have "term_start_unchanged (\<NN>'', \<TT>'', \<RR>'', \<SS>'') (\<NN>0, \<TT>0, \<RR>0, \<SS>0)" 
    using "1" "2" "3" assms by force
  then show ?thesis using 1 3 by fast
qed

(*probably with added pattern*)

lemma replace_rule_invariants:
  assumes "replace_rule y y1 (\<NN>0, \<TT>0, \<RR>0, \<SS>0) (s1, mu, theta) = \<GG>1"
          "valid_grammar  (\<NN>0, \<TT>0, \<RR>0, \<SS>0)"
          "(s1, mu@[y]@theta) \<in> \<RR>0"
        shows "valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 (\<NN>0, \<TT>0, \<RR>0, \<SS>0) \<and> term_start_unchanged  \<GG>1 (\<NN>0, \<TT>0, \<RR>0, \<SS>0)"
proof - 
  from assms(1) have inv1:"nonterm_sub \<GG>1 (\<NN>0, \<TT>0, \<RR>0, \<SS>0) \<and> term_start_unchanged  \<GG>1 (\<NN>0, \<TT>0, \<RR>0, \<SS>0)" by auto
  obtain \<NN>1 \<TT>1 \<RR>1 \<SS>1 where def:"(\<NN>1, \<TT>1, \<RR>1, \<SS>1) = \<GG>1" using assms(1) by simp
  with assms(1) have y1:"y1 \<in> \<NN>1" by auto
  from assms have "s1 \<in> \<NN>0 \<and> (\<forall> s \<in> set (mu@[y]@theta) . s \<in> (\<NN>0 \<union> \<TT>0)) " by fastforce
  with y1 have new_rule:"s1 \<in> \<NN>1 \<and> (\<forall> s \<in> set (mu@[y1]@theta) . s \<in> (\<NN>1 \<union> \<TT>1))" using assms(2) assms(3) inv1 def by fastforce
  have subset:"{r. \<forall> r \<in> \<RR>0 . r \<noteq> (s1, mu@[y]@theta)} \<subseteq> \<RR>0"  using assms(3) by blast
  have "\<RR>1 = {r. \<forall> r \<in> \<RR>0 . r \<noteq> (s1, mu@[y]@theta)}\<union>{(s1, mu@[y1]@theta)}" using assms(1) def by force
  with assms(1) def new_rule subset have "(\<forall> (N, \<alpha>) \<in> \<RR>1 . N \<in> \<NN>1 \<and> (\<forall> s \<in> set \<alpha> . s \<in> (\<NN>1 \<union> \<TT>1)))" by blast
  then have "valid_grammar \<GG>1" using def by force
  with inv1 show ?thesis by blast
qed

lemma extend_grammar_invariants:
  assumes "extend_grammar (\<NN>0, \<TT>0, \<RR>0, \<SS>0) y1 rule  = \<GG>1"
          "valid_grammar  (\<NN>0, \<TT>0, \<RR>0, \<SS>0)"
          "rule \<subseteq> snd ` \<RR>0"
        shows "valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 (\<NN>0, \<TT>0, \<RR>0, \<SS>0) \<and> term_start_unchanged  \<GG>1 (\<NN>0, \<TT>0, \<RR>0, \<SS>0)"
proof - 
  from assms(1) have inv1:"nonterm_sub \<GG>1 (\<NN>0, \<TT>0, \<RR>0, \<SS>0) \<and> term_start_unchanged  \<GG>1 (\<NN>0, \<TT>0, \<RR>0, \<SS>0)" by auto
  obtain \<NN>1 \<TT>1 \<RR>1 \<SS>1 where def:"(\<NN>1, \<TT>1, \<RR>1, \<SS>1) = \<GG>1" using assms(1) by simp
  with assms(1) have y1:"y1 \<in> \<NN>1" by auto
  from assms(2) have "\<forall> r \<in> (snd ` \<RR>0) . (\<forall> s \<in> set r . s \<in> (\<NN>0 \<union> \<TT>0))" by fastforce
  with assms(3)  have "\<forall> r \<in> rule . (\<forall> s \<in> set r . s \<in> (\<NN>1 \<union> \<TT>1))" using def inv1 by fastforce
  with y1 have "\<forall> (N, \<alpha>) \<in> ((\<lambda>r. (y1, r)) ` rule) . N \<in> \<NN>1 \<and> (\<forall> s \<in> set \<alpha> . s \<in> (\<NN>1 \<union> \<TT>1))" by simp
  then have "valid_grammar \<GG>1" using def  assms(1) assms(2) by fastforce
  with inv1 show ?thesis by fast
qed


lemma alt:
  assumes "alt = y_alt (\<NN>0, \<TT>0, \<RR>0, \<SS>0) w delta"
  shows "alt \<subseteq> snd ` \<RR>0"
proof -
  from assms have "alt = {\<alpha> . \<forall> (N, \<alpha>) \<in> candidate_rules  (\<NN>0, \<TT>0, \<RR>0, \<SS>0) w . plainrule \<alpha> \<noteq> delta}" by simp
  then have "alt \<subseteq> snd ` {(N, \<alpha>). \<forall> (N, \<alpha>) \<in> candidate_rules  (\<NN>0, \<TT>0, \<RR>0, \<SS>0) w . True}" by auto
  then have "alt \<subseteq> snd ` (Set.filter (\<lambda> t. True) (candidate_rules (\<NN>0, \<TT>0, \<RR>0, \<SS>0) w))" sorry
  then  have "alt \<subseteq> snd ` (candidate_rules (\<NN>0, \<TT>0, \<RR>0, \<SS>0) w)" by fastforce
  then show ?thesis using candidate_rules_subset by blast
qed

(*still have to add filtering etc.*)
lemma apply_pattern_invariants:
  assumes "(grammar', s', s'') = apply_pattern f grammar w delta (s, mu, theta)"
          "valid_grammar grammar"
          "(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = grammar"
          "(s, mu@[w]@theta) \<in> \<RR>0"
        shows "term_start_unchanged grammar' grammar \<and> 
        nonterm_sub grammar' grammar \<and> valid_grammar grammar'"
proof -
  obtain alt where alt_def:"alt = y_alt grammar w delta" by blast
  then have alt_sub:"alt \<subseteq> snd ` \<RR>0" using alt  assms(3) by blast
  obtain set' where set':"set' = filter (\<lambda>sym. candidate_rules' grammar sym = alt) (set_alternates (plain w) f)" by blast
  then show ?thesis
  proof (cases "set' = []")
    case True
    obtain G'' where g''_Def:"G'' = extend_grammar grammar y' alt" by blast
    then have G'':"valid_grammar G'' \<and> nonterm_sub G'' (\<NN>0, \<TT>0, \<RR>0, \<SS>0) \<and> term_start_unchanged  G'' (\<NN>0, \<TT>0, \<RR>0, \<SS>0)" 
    using extend_grammar_invariants assms alt_sub by blast
    obtain \<NN>1 \<TT>1 \<RR>1 \<SS>1 where g''_sub:"(\<NN>1, \<TT>1, \<RR>1, \<SS>1) = G''" using g''_Def assms(3) by auto 
    from assms(4) have r1:"(s, mu@[w]@theta) \<in> \<RR>1" sorry (*why does this hold?*)
    obtain G''' where "G''' = replace_rule  w y' G''  (s, mu, theta)" by blast
    then have invs:"valid_grammar G''' \<and> nonterm_sub G''' G'' \<and> term_start_unchanged  G''' G''" using replace_rule_invariants G'' r1 g''_sub by blast
    then have "grammar' = G'''" sorry
    then show ?thesis using G'' invs sorry (*additional transitivity term*)
  next
    case False
    obtain G' where   G':"G' = replace_rule  w (hd set') grammar  (s, mu, theta)" by blast
    then have invs:"valid_grammar G' \<and> nonterm_sub G' (\<NN>0, \<TT>0, \<RR>0, \<SS>0) \<and> term_start_unchanged  G' (\<NN>0, \<TT>0, \<RR>0, \<SS>0)" 
      using replace_rule_invariants assms(2) assms(3) assms(4) by blast
    then have "grammar' = G'" using G' assms(1) set' alt sorry  
    then show ?thesis using invs assms(3) by simp 
  qed
qed


lemma left_step4_invariants:
  assumes "(f', n', \<GG>1, slot') = 
  left_step4 (s, mu, theta) W (s', p, p', p1) (f, n, grammar, slot)"
  "valid_grammar grammar"
   "(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = grammar"
   "(s, mu@[W]@theta) \<in> \<RR>0"
  shows " valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 grammar \<and> term_start_unchanged  \<GG>1 grammar"
proof -
  from assms(1) have "(let (g', new_symbol', f') = 
      apply_pattern f grammar W p1 (s, mu, theta)
    in (f', new_symbol'#n, g', slot(new_symbol' \<mapsto> (the (slot (W)))))) = (f', n', \<GG>1, slot')" by simp
  then have " \<exists> s'' s'''. (\<GG>1, s'', s''' )= apply_pattern f grammar W p1 (s, mu, theta)" sorry
  then show ?thesis using assms apply_pattern_invariants  by blast
 (*based on apply pattern invariant*)
qed

lemma right_step4_invariants:
  assumes "(f', n', \<GG>1, slot') = 
  right_step4 (s, mu, theta) W (s', p, p', p1) (f, n, grammar, slot)"
  "valid_grammar grammar"
   "(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = grammar"
   "(s, mu@[W]@theta) \<in> \<RR>0"
  shows " valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 grammar \<and> term_start_unchanged  \<GG>1 grammar"
proof -
  from assms(1) have "(\<GG>1, s'', s''' )= apply_pattern f grammar W p1 (s, mu, theta)" sorry
  then show ?thesis using assms apply_pattern_invariants  by blast
 (*based on apply pattern invariant*)
qed

(*! ! ! check needed  (s, mu@[W]@theta) \<in> \<RR>0, might have to be changed as condition*)
lemma left_step3_invariants:
  shows  "(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0 \<Longrightarrow>
          valid_grammar \<GG>0 \<Longrightarrow>
          rule = (s, mu, theta) \<Longrightarrow>
          (s, mu@[W]@theta) \<in> \<RR>0 \<Longrightarrow>
          (f', n', \<GG>1, s') = left_step3 rule W  p (f, n,  \<GG>0, slot) \<Longrightarrow> 
          valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 \<GG>0 \<and> term_start_unchanged  \<GG>1 \<GG>0" (*again based on folding*)
proof (induction p arbitrary: f' n' \<GG>1 s')
  case Nil
  then have "\<GG>1 = \<GG>0" by simp
  then show ?case using Nil.prems by auto
next
  case (Cons a p)
  then have " (f', n', \<GG>1, s') = foldr (left_step4 rule W)  (a#p) (f, n, \<GG>0, slot)" by auto
  then have 1:"(f', n', \<GG>1, s') = ((left_step4 rule W a) \<circ> foldr (left_step4 rule W)  (p)) (f, n, \<GG>0, slot)"by auto
  then obtain f'' n'' \<GG>3 s'' where 2:"(f'', n'', \<GG>3, s'') =foldr (left_step4 rule W)  (p) (f, n, \<GG>0, slot)" 
    by (metis prod_cases4)
  then have "(f'', n'', \<GG>3, s'') = left_step3 rule W  p (f, n, \<GG>0, slot)" by simp
  then have \<GG>3_inv:"valid_grammar \<GG>3 \<and> nonterm_sub \<GG>3 \<GG>0 \<and> term_start_unchanged  \<GG>1 \<GG>0" using Cons sorry
  (*technically a rule is only changed once (!) so assumption  
    (s, mu@[W]@theta) \<in> \<RR>0 has to be rewritten as a conditional for certain changes*)
  then  obtain \<NN>3 \<TT>3 \<RR>3 \<SS>3 where  \<GG>3:"\<GG>3 = (\<NN>3, \<TT>3, \<RR>3, \<SS>3)" using valid_grammar.cases by blast
  then have placeholder:"(s, mu@[W]@theta) \<in> \<RR>3" sorry (*placeholder \<longrightarrow> might not hold 
      later, still taking a look*)
  then  obtain s0 p0 p0' p1 where a:"(s0, p0, p0', p1) = a" sorry
  have "(f', n', \<GG>1, s') = (left_step4 rule W a) (f'', n'', \<GG>3, s'')" using 1 2 by simp

  then have "valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 \<GG>3 \<and> term_start_unchanged  \<GG>1 \<GG>3"  
    using left_step4_invariants placeholder \<GG>3 Cons(4) a \<GG>3_inv by blast
  then show ?case using \<GG>3_inv nonterm_transitive term_start_transitive by blast
qed

lemma right_step3_invariants:
  shows "(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0 \<Longrightarrow>
          valid_grammar \<GG>0 \<Longrightarrow>
          rule = (s, mu, theta) \<Longrightarrow>
          (s, mu@[W]@theta) \<in> \<RR>0 \<Longrightarrow>
    (f', n', \<GG>1, s') = right_step3 rule W  p (f, n, \<GG>0, slot)
  \<Longrightarrow>  valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 \<GG>0  \<and> term_start_unchanged  \<GG>1 \<GG>0" (*again based on folding*)
proof (induction p  arbitrary: f' n' \<GG>1 s')
case Nil
then show ?case sorry
next
  case (Cons a p)
  then show ?case sorry
qed


lemma left_step2_invariants:
  assumes "(f', n',\<GG>1, s') = 
  left_step2 symbol \<ff>  (\<NN>0' , \<TT>0', R, \<SS>0') (f, n,  \<GG>0, slot)"
  "valid_grammar \<GG>0"
  "(\<NN>0 , \<TT>0, \<RR>0, \<SS>0) = \<GG>0 "
  "R \<subseteq> \<RR>0" (*needed to relate*)
shows  "valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1  \<GG>0 \<and> term_start_unchanged  \<GG>1  \<GG>0" 
proof -
  have l:"(f', n',\<GG>1, s') = foldl (\<lambda> fngs (N, \<alpha>).  left_step3 (N, butlast \<alpha>, []) (last \<alpha>) \<ff> fngs)  
  (f, n, \<GG>0, slot) (csorted_list_of_set (candidate_rules_left symbol R))" using assms by simp
  obtain rset where rset_def:"rset = (candidate_rules_left symbol R)" by blast
  have setchar:"rset \<subseteq> R \<and> (\<forall>(N, \<alpha>) \<in>  rset . last \<alpha> = symbol)" sorry (*candidate rules proof*)
  then have sub:"\<forall>(N, \<alpha>) \<in>  rset . (N, \<alpha>) \<in> \<RR>0" using assms(4) by auto
  have "\<forall>(N, \<alpha>) \<in>  rset . (butlast \<alpha>@[symbol]) = \<alpha>" using setchar  sorry
  then have sub':"\<forall>(N, \<alpha>) \<in> rset . (N, butlast \<alpha>@[symbol])\<in>\<RR>0" using sub by auto (*placeholder rule*)
  obtain list where list_def:"list = csorted_list_of_set (candidate_rules_left symbol R)" by blast
  then have eq:"set list = rset" using rset_def by (meson conflict_case rotate_left.simps)
  then have "\<forall>(N, \<alpha>) \<in> set list . (N, butlast \<alpha>@[symbol])\<in>\<RR>0" using sub' by simp 
  have "\<forall>(N, \<alpha>) \<in> set list . (N, \<alpha>)\<in>\<RR>0" using sub eq by simp 
  then have ind:"(\<NN>0 , \<TT>0, \<RR>0, \<SS>0) = \<GG>0 \<Longrightarrow> valid_grammar \<GG>0 \<Longrightarrow> (f', n',\<GG>1, s') = foldl (\<lambda> fngs (N, \<alpha>).  left_step3 (N, butlast \<alpha>, []) (last \<alpha>) \<ff> fngs)  
  (f, n, \<GG>0, slot) list \<Longrightarrow> ?thesis"
  proof (induction list arbitrary: f n \<GG>0 slot \<NN>0  \<TT>0 \<RR>0 \<SS>0)
    case Nil
    then have "\<GG>1 = \<GG>0" by force
    then show ?case using Nil invariants_refl by fast
  next
    case (Cons a list)
    obtain N \<alpha> where Na:"(N, \<alpha>) = a" 
      by (metis convertback_rule.cases)
    have cond1:"(N, (butlast \<alpha>)@[last \<alpha>]@[]) \<in> \<RR>0" using Cons(5) Na 
     sorry
    obtain rule where rule_Def:"rule = (N, (butlast \<alpha>), []:: ('a \<times> nat + 'b) list)" by simp
    from  Cons(3) obtain f'' n'' G'' s'' where first_app:"(f'', n'', G'', s'') = 
    (\<lambda>fngs a. case a of (N, \<alpha>) \<Rightarrow> left_step3 (N, butlast \<alpha>, []) (last \<alpha>) \<ff> fngs) (f, n, \<GG>0, slot) a"
 sorry
    then have  app:"(f'', n'', G'', s'') = left_step3 rule (last \<alpha>) \<ff> (f, n,  \<GG>0, slot)" 
      using rule_Def Na by fast
    then have G''_valid:"valid_grammar G''" and G''_trans:"nonterm_sub G''  \<GG>0 \<and> term_start_unchanged  G''  \<GG>0" 
      using left_step3_invariants [OF Cons(2) Cons(3) rule_Def cond1 app] apply(simp)
      using left_step3_invariants [OF Cons(2) Cons(3) rule_Def cond1 app] by simp
    have step:"(f', n',\<GG>1, s') = foldl (\<lambda> fngs (N, \<alpha>).  left_step3 (N, butlast \<alpha>, []) (last \<alpha>) \<ff> fngs)  
  (f'', n'', G'', s'') list" using Cons first_app by simp
    
    obtain \<NN>0' \<TT>0' \<RR>0' \<SS>0' where G''_sub:"(\<NN>0' , \<TT>0', \<RR>0', \<SS>0') = G''" by (metis valid_grammar.cases)
    then have " \<RR>0 \<subseteq> \<RR>0'" using G''_trans Cons(2) nonterm_sub' by blast
    then have list_val:"\<forall>a\<in>set (list). case a of (N, \<alpha>) \<Rightarrow> (N, \<alpha>) \<in> \<RR>0'" using Cons  by auto
    then have " valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 G'' \<and> term_start_unchanged \<GG>1 G''" using Cons(1) [OF G''_sub G''_valid step ] list_val  by auto
    with G''_trans nonterm_transitive term_start_transitive show ?case by blast
  qed
  show ?thesis using ind [OF assms(3) assms(2)] l list_def by blast
qed

lemma right_step2_invariants:
  assumes "(f', n',\<GG>1, s') = right_step2 symbol \<ff> (\<NN>0' , \<TT>0', R, \<SS>0') (f, n,  \<GG>0, slot)"
    "valid_grammar \<GG>0"
    "(\<NN>0 , \<TT>0, \<RR>0, \<SS>0) = \<GG>0 "
    "R \<subseteq> \<RR>0" (*needed to relate*)
  shows "valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 \<GG>0 \<and> term_start_unchanged  \<GG>1  \<GG>0"
proof -
  have l:"(f', n',\<GG>1, s') = foldl (\<lambda> fngs (N, \<alpha>).  right_step3 (N, [], tl \<alpha>) (hd \<alpha>) \<ff> fngs)  
  (f, n, \<GG>0, slot) (csorted_list_of_set (candidate_rules_right symbol R))" using assms by simp
  obtain rset where rset_def:"rset = (candidate_rules_right symbol R)" by blast
  have setchar:"rset \<subseteq> R \<and> (\<forall>(N, \<alpha>) \<in>  rset . hd \<alpha> = symbol)" sorry (*candidate rules proof*)
  then have sub:"\<forall>(N, \<alpha>) \<in>  rset . (N, \<alpha>) \<in> \<RR>0" using assms(4) by auto
  have "\<forall>(N, \<alpha>) \<in>  rset . (symbol#tl \<alpha>) = \<alpha>" using setchar 
   sorry
  then have sub':"\<forall>(N, \<alpha>) \<in> rset . (N, symbol#tl \<alpha>)\<in>\<RR>0" using sub by auto (*placeholder rule*)
  obtain list where list_def:"list = csorted_list_of_set (candidate_rules_right symbol R)" by blast
  then have eq:"set list = rset" using rset_def by (meson conflict_case rotate_left.simps)
  then have "\<forall>(N, \<alpha>) \<in> set list . (N, symbol#tl \<alpha>)\<in>\<RR>0" using sub' by simp 
  have "\<forall>(N, \<alpha>) \<in> set list . (N, \<alpha>)\<in>\<RR>0" using sub eq by simp 
  then have ind:"(\<NN>0 , \<TT>0, \<RR>0, \<SS>0) = \<GG>0 \<Longrightarrow> valid_grammar \<GG>0 \<Longrightarrow> (f', n',\<GG>1, s') = foldl (\<lambda> fngs (N, \<alpha>).  right_step3 (N, [], tl \<alpha>) (hd \<alpha>) \<ff> fngs)  
  (f, n, \<GG>0, slot) list \<Longrightarrow> ?thesis"
  proof (induction list arbitrary: f n \<GG>0 slot \<NN>0  \<TT>0 \<RR>0 \<SS>0)
    case Nil
    then have "\<GG>1 = \<GG>0" by force
    then show ?case using Nil invariants_refl by fast
  next
    case (Cons a list)
    obtain N \<alpha> where Na:"(N, \<alpha>) = a" 
      by (metis convertback_rule.cases)
    have cond1:"(N, []@[(hd \<alpha>)]@tl \<alpha>) \<in> \<RR>0" using Cons(5) Na 
      sorry
    obtain rule where rule_Def:"rule = (N,  []:: ('a \<times> nat + 'b) list, tl \<alpha>)" by simp
    from  Cons(3) obtain f'' n'' G'' s'' where first_app:"(f'', n'', G'', s'') = 
    (\<lambda>fngs a. case a of (N, \<alpha>) \<Rightarrow> right_step3 (N, [], tl \<alpha>) (hd \<alpha>) \<ff> fngs) (f, n, \<GG>0, slot) a"
     sorry
    then have  app:"(f'', n'', G'', s'') = right_step3 rule (hd \<alpha>) \<ff> (f, n,  \<GG>0, slot)" 
      using rule_Def Na by fast
    then have G''_valid:"valid_grammar G''" and G''_trans:"nonterm_sub G''  \<GG>0 \<and> term_start_unchanged  G''  \<GG>0" 
      using right_step3_invariants [OF Cons(2) Cons(3) rule_Def cond1 app] apply simp
      using right_step3_invariants [OF Cons(2) Cons(3) rule_Def cond1 app] by simp
    have step:"(f', n',\<GG>1, s') = foldl (\<lambda> fngs (N, \<alpha>).  right_step3 (N, [], tl \<alpha>) (hd \<alpha>) \<ff> fngs)  
  (f'', n'', G'', s'') list" using Cons first_app by simp
    
    obtain \<NN>0' \<TT>0' \<RR>0' \<SS>0' where G''_sub:"(\<NN>0' , \<TT>0', \<RR>0', \<SS>0') = G''" by (metis valid_grammar.cases)
    then have " \<RR>0 \<subseteq> \<RR>0'" using G''_trans Cons(2) nonterm_sub' by blast
    then have list_val:"\<forall>a\<in>set (list). case a of (N, \<alpha>) \<Rightarrow> (N, \<alpha>) \<in> \<RR>0'" using Cons  by auto
    then have " valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 G'' \<and> term_start_unchanged \<GG>1 G''" using Cons(1) [OF G''_sub G''_valid step ] list_val  by auto
    with G''_trans nonterm_transitive term_start_transitive show ?case by blast
  qed
  show ?thesis using ind [OF assms(3) assms(2)] l list_def by blast
qed



lemma apply_step0_right_invariants: 
assumes
  "(f', n',\<GG>1, s')= apply_right_step1 symbol p G'  (f, n, \<GG>0, s) "
  "valid_grammar \<GG>0"
  "G' = (\<NN>', \<TT>', R', \<SS>')"
  "(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0 "
  "R' \<subseteq> \<RR>0"
shows"valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 \<GG>0 \<and> term_start_unchanged  \<GG>1 \<GG>0"
proof (cases "[] =  fst(the (s symbol))")
  case True
   then have 1:"(f', n', \<GG>1, s') =
    right_step2 symbol (filterPattern p (the (s symbol))) (\<NN>', \<TT>', R', \<SS>') (f, n, \<GG>0 , s)"
     using assms by simp
   then show ?thesis using right_step2_invariants [OF 1 assms(2) assms(4) assms(5)] by blast
next
  case False
  then have "(f', n', \<GG>1, s') = (f, n, \<GG>0, s)" using assms by simp
  then show ?thesis using assms by (auto) 
qed


lemma apply_step0_left_invariants: 
  assumes "(f', n', \<GG>1, s')=
  apply_left_step1 symbol p G'  (f, n, \<GG>0, s) "
  "valid_grammar \<GG>0"
  "G' = (\<NN>', \<TT>', R', \<SS>')"
  "(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0 "
  "R' \<subseteq> \<RR>0"
  shows"valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 \<GG>0 \<and> term_start_unchanged  \<GG>1 \<GG>0"
proof (cases "[] =  fst(the (s symbol))")
  case True
   then have 1:"(f', n', \<GG>1, s') =
    left_step2 symbol (filterPattern p (the (s symbol)))  (\<NN>', \<TT>', R', \<SS>') (f, n, \<GG>0 , s)"
     using assms by simp
   
   then show ?thesis using left_step2_invariants [OF 1 assms(2) assms(4) assms(5)] by blast
  (*
     by (metis (mono_tags, hide_lams) old.prod.exhaust term_start_unchanged.simps term_start_transitive)*)
next
  case False
  then have "(f', n', \<GG>1, s') = (f, n, \<GG>0, s)" using assms by simp
  then show ?thesis using assms by auto
qed

lemma apply_step0_invariants:
  assumes "(f', n', \<GG>1, s')=
  apply_step0 symbol p \<GG>_'  (f, n, \<GG>0, s) "
  "valid_grammar \<GG>0"
  "\<GG>_' = (\<NN>', \<TT>', R', \<SS>') " 
  "(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0 "
  "R' \<subseteq> \<RR>0"
  
  shows"valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 \<GG>0 \<and> term_start_unchanged  \<GG>1 \<GG>0"
proof -
  obtain f'' n'' \<GG>'' s'' where intermed:
    "(f'', n'', \<GG>'', s'') = 
  apply_left_step1 symbol p  \<GG>_'  (f, n, \<GG>0, s)" 
    by (metis prod_cases4) 
  then have med:"valid_grammar \<GG>'' \<and> nonterm_sub \<GG>'' \<GG>0 \<and> term_start_unchanged  \<GG>'' \<GG>0"  
    using assms(2) apply_step0_left_invariants [OF intermed assms(2) assms(3) assms(4) assms(5)] by blast
  from this have valid_med:"valid_grammar \<GG>''" by simp
  obtain \<NN>'' \<TT>'' R'' \<SS>'' where intermed':"\<GG>'' = (\<NN>'', \<TT>'', R'', \<SS>'') " by (meson \<open>valid_grammar \<GG>''\<close> valid_grammar.elims(2))
  then have intermed'':"R' \<subseteq> R''" using med assms(5) assms(4) 
    using nonterm_sub' by blast  
  from assms intermed have second:"(f', n', \<GG>1, s') = 
  apply_right_step1 symbol p  \<GG>_' (f'', n'', \<GG>'', s'')" by simp
  then have val:"valid_grammar \<GG>1" using med apply_step0_right_invariants [OF second valid_med assms(3) ] intermed' intermed'' by blast
  have med':"nonterm_sub \<GG>1 \<GG>'' \<and> term_start_unchanged  \<GG>1 \<GG>''" using med second 
      apply_step0_right_invariants [OF second valid_med assms(3) ] intermed' intermed'' by blast
  with med have "nonterm_sub \<GG>1 \<GG>0" 
   using nonterm_transitive by blast
  from med' med val nonterm_transitive term_start_transitive show ?thesis by blast   
qed

(*any possible invariants on new are used for pattern recognition*)
lemma step0_invariants:
  assumes  "(f', n', \<GG>1 ,s') = (step0 P  (f, n, \<GG>0 , s))"  
           "valid_grammar \<GG>0"
           "(\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0 "
  shows"valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 \<GG>0 \<and> term_start_unchanged  \<GG>1 \<GG>0"
proof -
  have fold:"(f', n', \<GG>1 ,s') = foldl (\<lambda> fngs symbol . apply_step0 symbol P  \<GG>0  fngs)  (f, n,  \<GG>0 , s) n" using assms by simp
  obtain \<GG>0' \<NN>0' \<TT>0' \<RR>0' \<SS>0' where placeholder:"\<GG>0' = \<GG>0"  and placeholder':"(\<NN>0', \<TT>0', \<RR>0', \<SS>0') = \<GG>0'" apply(cases \<GG>0) by blast 
  then have ph_valid:"valid_grammar \<GG>0'" and ph_r:"\<RR>0 \<subseteq> \<RR>0'" using assms(2) apply blast using placeholder' placeholder assms(3) by blast
  obtain n0 where "n0 = n" by blast
  then have fold':"(f', n', \<GG>1 ,s') = foldl (\<lambda> fngs symbol . apply_step0 symbol P  \<GG>0  fngs)  (f, n0,  \<GG>0' , s) n" using fold placeholder by simp
  have lemma1:"valid_grammar \<GG>0' \<Longrightarrow> (\<NN>0', \<TT>0', \<RR>0', \<SS>0') = \<GG>0' \<Longrightarrow> (\<NN>0, \<TT>0, \<RR>0, \<SS>0) = \<GG>0 \<Longrightarrow> \<RR>0 \<subseteq> \<RR>0' \<Longrightarrow>  
          (f', n', \<GG>1 ,s') = foldl (\<lambda> fngs symbol . apply_step0 symbol P  \<GG>0  fngs)  (f, n0 ,  \<GG>0' , s) n
            \<Longrightarrow> ?thesis" (*n'' needed \<Longrightarrow> influence on pattern proofs?*)
  proof (induction n arbitrary: f   s \<NN>0' \<TT>0' \<RR>0' \<SS>0' n0 \<GG>0')
    case Nil
    then have "(f', n', \<GG>1, s') = (f, n0, \<GG>0', s)" by simp
    then show ?case  sorry (*reevaluate foldl*)
next
  case (Cons a n)
  then obtain f'' n'' G'' s'' where app:"(f'', n'', G'', s'') = (\<lambda> fngs symbol . apply_step0 symbol P  \<GG>0  fngs)  (f, n0,  \<GG>0' , s) a" sorry(*why not?*)
  then have 1:"(f'', n'', G'', s'') = apply_step0 a P  \<GG>0  (f, n0,  \<GG>0' , s)" using Cons by simp  
  from Cons(4) have 3:"\<GG>0 = (\<NN>0, \<TT>0, \<RR>0, \<SS>0) " by simp
  have intermed:"valid_grammar G'' \<and> nonterm_sub G'' \<GG>0' \<and> term_start_unchanged G'' \<GG>0'" using apply_step0_invariants [OF 1 Cons(2) 3 Cons(3) Cons(5)] by simp
  then have med_valid:"valid_grammar G''" by simp
  obtain \<NN>'' \<TT>'' R'' \<SS>'' where intermed':"G'' = (\<NN>'', \<TT>'', R'', \<SS>'') " by (meson \<open>valid_grammar G''\<close> valid_grammar.elims(2))
  then have "\<RR>0' \<subseteq> R''" using intermed Cons(3) 
    using nonterm_sub' by blast
  then have intermed'':"\<RR>0 \<subseteq> R''" using Cons(5) by simp
  from intermed' have intermed''':" (\<NN>'', \<TT>'', R'', \<SS>'' ) = G''" by simp
  have l:"(f', n', \<GG>1, s') = foldl (\<lambda>fngs symbol. apply_step0 symbol P \<GG>0 fngs) (f'', n'', G'', s'') n" using app Cons(6) by auto
  then show ?case using Cons(1) [OF med_valid intermed''' Cons(4) intermed'' l] by auto
qed
  show ?thesis using lemma1 [OF ph_valid placeholder' assms(3) ph_r fold'] by blast
qed 


lemma stage4_invariants:
  assumes "\<GG>1 = 
  stage4 \<P> \<GG>0 leftrecurs rightrecurs (f, n,  \<GG>0, s)" "valid_grammar \<GG>0"
  shows"valid_grammar \<GG>1 \<and> nonterm_sub \<GG>1 \<GG>0 \<and> term_start_unchanged  \<GG>1 \<GG>0"
proof - 
  show ?thesis sorry 
qed

lemma G'_valid:"valid_grammar \<GG>'"
  sorry
lemma \<GG>''_valid:"valid_grammar \<GG>'' \<and> nonterm_sub \<GG>'' \<GG>' \<and> term_start_unchanged \<GG>'' \<GG>'"
  using stage4_invariants G'_valid 
  sorry

lemma terminal_equality_help4:" \<TT>''' = \<B>"
proof -
  obtain N T R s N' T' R' s' where def:"\<GG>'' = (N, T, R, s) \<and> \<GG>' = (N', T', R', s')" 
    by (meson \<GG>''_valid nonterm_sub.elims(2))
  then have "T' = T" using \<GG>''_valid by simp
  then have "get_term \<GG>'' = get_term \<GG>'" using def by auto
  then have "\<TT>''' = \<TT>''" using \<TT>'''_def \<TT>''_def by argo
  then show ?thesis using \<TT>''_\<B> by auto
qed

(*lemma needed to prove that lack of equivalent tree implies conflict*)
lemma "\<forall> r \<in> \<RR>' . \<exists> r' \<in> \<RR>''' . convertback_rule r' = r"
  sorry
lemma validStart:"\<SS>''' \<in> \<NN>'''"
proof -
  from \<GG>''_valid have 1:"get_s \<GG>'' = get_s \<GG>'"  sorry
  from \<GG>''_valid have 2:"get_nonterm \<GG>' \<subseteq> get_nonterm \<GG>'' " sorry
  with 1 start' have "get_s \<GG>'' \<in> get_nonterm \<GG>''" by auto
  then have "\<SS>'''\<in> \<NN>'''" using  \<SS>'''_def \<NN>'''_def by blast
  then show ?thesis by simp
qed (*proof based on start element staying the same and  \<NN>''\<subseteq>\<NN>''' *)



(*probably need additional lemma that all in term are of type Inl*)
lemma nonterm_type_a:"\<forall> s \<in> get_nonterm \<GG>'' . case_sum (\<lambda> s. True) (\<lambda> s. False) s"
  sorry


lemma inl_grammar4:"Inl ` \<NN>''' = get_nonterm \<GG>''"
proof -
  have 1:"Inl ` \<NN>''' \<subseteq> get_nonterm \<GG>''" using \<NN>'''_def sorry
  from nonterm_type_a have " get_nonterm \<GG>'' \<subseteq> Inl ` \<NN>''' " using \<NN>'''_def sorry
  with 1 show ?thesis by auto
qed

lemma inr_grammar4:"Inr ` \<TT>''' = get_term \<GG>'' "
 sorry (*? ? ? proper proof?*)
lemma validRules:"\<forall> (N, \<alpha>) \<in> \<RR>''' . N \<in> Inl ` \<NN>''' \<and> (\<forall>s\<in>set \<alpha>. s \<in> Inl ` \<NN>''' \<union> Inr ` \<TT>''')"
proof -
  from \<GG>''_valid have val:"valid_grammar \<GG>''" by simp
  obtain \<NN>1 \<TT>1  \<RR>1 \<SS>1 where subexp:"(\<NN>1, \<TT>1,  \<RR>1, \<SS>1) = \<GG>''" 
    by (metis valid_grammar.cases)
  with val have rules:"(\<forall> (N, \<alpha>) \<in> \<RR>1 . N \<in> \<NN>1 \<and> (\<forall> s \<in> set \<alpha> . s \<in> (\<NN>1 \<union> \<TT>1)))" sorry
  from subexp have "\<RR>1 = get_rule \<GG>'' \<and> \<NN>1 = get_nonterm \<GG>''  \<and> \<TT>1 =get_term \<GG>''"
    by (metis get_rule.simps get_nonterm.simps get_term.simps)
  with rules val subexp  have "\<forall>(N, \<alpha>)\<in> get_rule \<GG>''. N \<in> get_nonterm \<GG>'' \<and> (\<forall>s\<in>set \<alpha>. s \<in> get_nonterm \<GG>'' \<union>  get_term \<GG>'')" by simp
  then show ?thesis using inl_grammar4 inr_grammar4 \<RR>'''_def by simp 
  (*get from apply pattern adding only valid rules*)
qed

lemma finite_\<RR>''':"finite \<RR>'''"
  sorry

lemma finite_\<TT>''':"finite \<TT>'''"
  sorry


interpretation grammar4: CFG \<NN>''' \<TT>''' \<RR>''' \<SS>'''
  apply(unfold_locales)
   apply(auto simp add: validStart finite_\<RR>''' finite_\<TT>''')
  using validRules  apply blast using validRules  by blast


lemma \<RR>'''_equiv_\<RR>:"\<forall> r \<in> \<RR>''' . ( convertback_rule r \<in> \<RR>) "
  sorry (*provable again via inheritance from grammar3*)


lemma terminal_equality_gram4:"grammar4.is_terminal x \<Longrightarrow> is_terminal (convert_back x)"
  apply(auto simp add: grammar4.is_terminal_def is_terminal_def)
  sorry

lemma terminal_equality_gram4':"is_terminal x \<Longrightarrow> grammar4.is_terminal (convert i x)"
  apply(auto simp add: grammar4.is_terminal_def is_terminal_def)
  by (simp add: disjE_realizer terminal_equality_help4)

lemma nonterminal_equality_help4:"\<forall> t \<in> \<NN>''' . (fst t) \<in> \<A>"
  apply (auto simp add: \<NN>'''_def)
  sorry

lemma nonterminal_equality_gram4:"grammar4.is_nonterminal x \<Longrightarrow> is_nonterminal (convert_back x)"
  apply(auto simp add: grammar4.is_nonterminal_def is_nonterminal_def)
  by (simp add: disjE_realizer nonterminal_equality_help4)


theorem grammar4_conflict_free:"\<forall> r \<in> \<RR>''' . (reachable_left r) \<notin> (Priority \<union> Left) \<and> (reachable_right r) \<notin> (Priority \<union> Right)"
  sorry

theorem grammar4_conflict_free':"grammar4.Tree_wf T \<Longrightarrow> conflictfree_root (convert_tree T)"
proof -
  have "(\<forall> p \<in> set \<P> . valid_root_pattern p (convert_tree T))" sorry (*holds because of our root problem*)
  then show ?thesis sorry
qed
 (*probably a proof by contradiction or something similar*)

theorem grammar4_conflict_free2:"\<forall> r \<in> \<RR>''' . (\<forall> r' \<in> \<RR>'''. ((convertback_rule r, convertback_rule r') \<notin> (Priority \<union> Left))
  \<longrightarrow>  (r' \<in> (reachable r)))"
  sorry

lemma grammar4_sub_0:"grammar4.Tree_wf T \<Longrightarrow> 
        Tree_wf (convert_tree T) \<and> convertback_rule (DeriveFromTree T) = DeriveFromTree (convert_tree T) \<and> conflict_free (convert_tree T)"
proof(induct T )
  case (Leaf x)
  then have 1:"grammar4.is_terminal x" by simp
  obtain s a where "(s, a) = DeriveFromTree (Leaf x)" by auto
  then have s:"s = x \<and> a = [x]" by simp
  then have a:"convert_back_sentence a = [convert_back x]" by simp
  from 1 have terminal:"is_terminal (convert_back x)" using terminal_equality_gram4 by blast
  obtain leaf where def:"leaf = (Leaf (convert_back x))" by blast
  with terminal have wf:"Tree_wf leaf" by simp
  from def a s have  deriv:"(convert_back s, convert_back_sentence a )= DeriveFromTree leaf" by simp
  from def have "conflict_free leaf" by force
  with wf deriv def show ?case by auto
next
  case (Inner x)
  then have 1:"grammar4.is_nonterminal x" by simp
  obtain s a where "(s, a) = DeriveFromTree (Inner x)" by auto
  then have s:"s = x \<and> a = [x]" by simp
  then have a:"convert_back_sentence a = [convert_back x]" by simp
  from 1 have terminal:"is_nonterminal (convert_back x)" using nonterminal_equality_gram4 by blast
  obtain leaf where def:"leaf = (Inner (convert_back x))" by blast
  with terminal have wf:"Tree_wf leaf" by simp
  from def a s have  deriv:"(convert_back s, convert_back_sentence a )= DeriveFromTree leaf" by simp
  from def have "conflict_free leaf" by force
  with wf deriv def show ?case by auto
next
  case (DT r b)
  from DT.prems(1) have validrule:"r \<in> \<RR>'''" by auto (*need implication that *)
  obtain N \<alpha> where na:"N = fst r \<and> \<alpha> = snd r" by blast 
  with validrule have valid_rule:"convertback_rule r \<in> \<RR>" using \<RR>'''_equiv_\<RR> by auto
  from DT.prems(1) have "snd r = concat (map grammar4.TreeSym b)" by simp 
  then have "snd r = concat (map (\<lambda> t . [fst (DeriveFromTree t)]) b)" using grammar4.TreeSym_implies_DeriveFrom_root by presburger
  with na have "convert_back_sentence \<alpha> = concat (map (\<lambda> t . [convert_back (fst (DeriveFromTree t))]) b)" by auto
  from DT.prems have wf_subtrees:"list_all grammar4.Tree_wf b" by auto
  from DT.prems have deriv_subtrees:"snd (DeriveFromTree (DT r b)) = (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b))" by auto
  then obtain b'' where ih:"b'' = map convert_tree b" by blast
  (*induction hypothesis*)
  with wf_subtrees have wf_converted:"list_all Tree_wf b''" using DT(1) list_all_def sorry
  from ih deriv_subtrees have deriv_converted:"convert_back_sentence (snd (DeriveFromTree (DT r b))) = 
    (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b''))" sorry
  from DT(1) have conflictfree_converted:"list_all conflict_free b''" sorry


  then have valid_subtrees:"convert_back_sentence \<alpha> = 
    concat (map (\<lambda> t . [(fst (DeriveFromTree t))]) b'')" using DT(1) sorry (*explicit function needed*)
  then have valid_subtrees':"convert_back_sentence \<alpha> = concat (map TreeSym b'')" using TreeSym_equal_DeriveFrom_root' 
    by presburger  
  from DT.prems have "snd (DeriveFromTree (DT r b)) = (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b))" by simp
  then have deriv:"convert_back_sentence (snd (DeriveFromTree (DT r b))) = 
    (concat( map (\<lambda>subtree . (convert_back_sentence (snd (DeriveFromTree subtree)))) b))" sorry (*no singletons, separate proof needed*)
  with ih have derive':"convert_back_sentence (snd (DeriveFromTree (DT r b))) = (concat( map (\<lambda>subtree . (snd (DeriveFromTree subtree))) b''))" 
    using DT(1) sorry
  obtain T' where tree:"T' = convert_tree (DT r b)" by blast
  then have T'_def:"T' = DT (convertback_rule r) b''" using ih by auto
  (*well_formedness of converted tree*)
  then have wf:"Tree_wf T'" using valid_rule valid_subtrees' wf_converted na  convertback_rule_snd by auto
  (*derivation equality*)
  from deriv_converted T'_def have deriv:"convertback_rule (DeriveFromTree (DT r b )) = DeriveFromTree T'" apply simp 
    by (metis convert_back.simps convertback_rule.simps fst_conv prod.collapse)
  (*conflict free*)
  from DT.prems(1) have "conflictfree_root T'" using grammar4_conflict_free' tree by blast
  with conflictfree_converted have "conflict_free T'" using T'_def by simp 
  then show ?case using wf deriv tree by fast
qed

lemma terminal_set_eq:"\<TT>''' = \<B>"
  using terminal_equality_help4 by blast



section "Two possible strengthenings
        1. define possible rule parent of tree and if inductively no conflict with parent,
           than tree rooted and symbol in parent exists (*might not properly capture higher ambiguities

        2. keep sets of parent rules that might cause conflict \<Longrightarrow> inductively proof that whole list won't have 
            conflicts, so tree rooted at this point exists*)"


lemma [case_names NoneNone SomeNone NoneSome SomeSome, cases type: parents]:
  "(y = (None, None) \<Longrightarrow> P) \<Longrightarrow> (\<And>a. y = (Some a, None) \<Longrightarrow> P) 
    \<Longrightarrow> (\<And>a. y = (None, Some a) \<Longrightarrow> P) \<Longrightarrow> (\<And>a  b. y = (Some b, Some a) \<Longrightarrow> P ) \<Longrightarrow> P"
  by (metis not_None_eq surj_pair)


(*the proper cases of conflict freedom must be used*)
fun conflict_free''::"('a, 'b) parents \<Rightarrow>('a, 'b) parents \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"conflict_free'' (None, None) (None, None) t = True" |
"conflict_free'' (Some l, None) (None, None)  t = ((fst (DeriveFromTree t) = convert_back (last (snd l)))  \<and>(\<forall> s \<in> set (leftspine1 t) 
.(leftconflictfree (convertback_rule l) s)))"| (*parent to the left, so leftspine comp*)
"conflict_free'' (Some l, None) (Some l', None)  t = ((fst (DeriveFromTree t) = convert_back (last (snd l))) \<and> (\<forall> s \<in> set (leftspine1 t) 
.(leftconflictfree (convertback_rule l) s)))"| (*plus the deeper ambiguity*)
"conflict_free'' (None, Some r) (None, Some r') t = ((fst (DeriveFromTree t) = convert_back(hd (snd r))) \<and> (\<forall> s \<in> set (rightspine1 t) 
  .  (rightconflictfree (convertback_rule r) s)))"|
"conflict_free'' _  _  t = False"


(*
fun matching_root::"('a \<times> nat, 'b) symbol \<Rightarrow> ('a, 'b) parents \<Rightarrow> bool" where
"matching_root s (None, None)   = (s \<in> Inl ` new_nonterm)" | (*only if zero indexed*)
"matching_root  s (Some l, None)  = (last (snd l) = s) "|
"matching_root s (None, Some r) = (hd (snd r) = s)"|
"matching_root _ _ = False"*)

fun right_reachable::"('a \<times> nat, 'b) rule \<Rightarrow> ('a \<times> nat, 'b) rule \<Rightarrow> bool" where
"right_reachable r l = undefined"


fun left_reachable::"('a \<times> nat, 'b) rule \<Rightarrow> ('a \<times> nat, 'b) rule \<Rightarrow> bool" where
"left_reachable r l = undefined"

fun valid_parents::"('a, 'b) parents \<Rightarrow> ('a, 'b) parents \<Rightarrow> bool" where
"valid_parents (None, None) (None, None) = True" |
"valid_parents (Some l, None) (None, None) = (l \<in> \<RR>''')" |
"valid_parents (Some l, None) (None, Some r) = ((l \<in> \<RR>''') \<and> (r \<in> \<RR>''') \<and> (right_reachable r l))" |
"valid_parents (None, Some l) (None, None) =  (l \<in> \<RR>''')"|
"valid_parents (None, Some l) (Some r, None) = ((l \<in> \<RR>''') \<and> (r \<in> \<RR>''') \<and> left_reachable r l)"|
"valid_parents _ _ = False"

(*additional valid parents needed*)
lemma ruleexists:"valid_parents pred pred' \<Longrightarrow> conflict_free'' pred pred' (DT r b) \<Longrightarrow> 
  \<exists> (N, \<alpha>) \<in> \<RR>''' . convertback_rule (N, \<alpha>) = r \<and> matching_root N pred"
  sorry (*one of the removal things*)

(*additional lemma connecting spins to right and left reachable*)
(*lemma: for each symbol rule reachable from the spines of another rule \<Longrightarrow> if no conflicts with either, rule alternative exists*)

lemma conversion_lemma:"is_terminal x \<Longrightarrow>  s \<in> (Inl ` \<NN>''' \<union> Inr ` \<TT>''') \<Longrightarrow> convert_back s = x \<Longrightarrow> grammar4.is_terminal s"
  sorry


lemma conversion_lemma':"is_nonterminal x \<Longrightarrow>  s \<in> (Inl ` \<NN>''' \<union> Inr ` \<TT>''') \<Longrightarrow> convert_back s = x \<Longrightarrow> grammar4.is_nonterminal s"
  sorry
theorem grammar4_super_conflict_free':"Tree_wf T \<Longrightarrow> conflict_free'' pred pred' T \<Longrightarrow> conflict_free T \<Longrightarrow> valid_parents pred pred'
  \<Longrightarrow> \<exists> T'. grammar4.Tree_wf T' \<and>  convert_tree T' = T \<and> matching_root (fst (DeriveFromTree T')) pred"
proof (induct T)
  case (Leaf x)
  then have 1:"is_terminal x" by simp
  obtain s a where "(s, a) = DeriveFromTree (Leaf x)" by auto
  then  have s:"s = x \<and> a = [x]" by simp
  show ?case
  proof (cases pred)
    case NoneNone
      from 1 have terminal:"grammar4.is_terminal (convert 0 x)" using terminal_equality_gram4'  by blast
      obtain leaf where def:"leaf = (Leaf (convert 0 x))" by blast
      with terminal have wf:"grammar4.Tree_wf leaf" by simp
      obtain s' a' where  deriv:"DeriveFromTree leaf = (s', a')" by force
      with def have s'_def:"s' = (convert 0 x) \<and> a' = [convert 0 x]" by auto
      with  s have  s':"convert_back s' = s \<and> convert_back_sentence a' = a" using backconversion' by auto 
      then have conv:"convert_tree (leaf) = Leaf x" using def s'_def s by simp
      have "s' \<in> Inl ` new_nonterm" sorry (*holds because of convert 0*) 
      then have "matching_root (fst (DeriveFromTree leaf)) pred" using deriv NoneNone by auto
      then show ?thesis using conv wf by blast 
  next
    case (SomeNone a)
    then have conv:"fst (DeriveFromTree (Leaf x)) = convert_back (last (snd a))" using Leaf.prems(2)
      using conflict_free''.elims(2) by blast
    then obtain s' where s'_def:"s' = (last (snd a))" by blast
    have "a \<in> \<RR>'''" using Leaf.prems(4) SomeNone using valid_parents.elims(2) by blast
    then have s'_symbol:"s' \<in> (Inl ` \<NN>''' \<union> Inr ` \<TT>''')" using validRules s'_def sorry
    have conv':"x = convert_back s'" using conv s'_def by simp
    then have "grammar4.is_terminal s'" using conversion_lemma [OF 1] s'_symbol by presburger
    then have wf:"grammar4.Tree_wf (Leaf s') \<and> convert_tree (Leaf s') = Leaf x" using conv' by simp
    have "matching_root (fst (DeriveFromTree (Leaf s'))) pred" using SomeNone s'_def by auto
    then show ?thesis using wf by blast
  next
    case (NoneSome a)
        then have conv:"fst (DeriveFromTree (Leaf x)) = convert_back (hd (snd a))" using Leaf.prems(2)
      using conflict_free''.elims(2) by blast
    then obtain s' where s'_def:"s' = (hd (snd a))" by blast
    have "a \<in> \<RR>'''" using Leaf.prems(4) NoneSome using valid_parents.elims(2) by blast
    then have s'_symbol:"s' \<in> (Inl ` \<NN>''' \<union> Inr ` \<TT>''')" using validRules s'_def sorry
    have conv':"x = convert_back s'" using conv s'_def by simp
    then have "grammar4.is_terminal s'" using conversion_lemma [OF 1] s'_symbol by presburger
    then have wf:"grammar4.Tree_wf (Leaf s') \<and> convert_tree (Leaf s') = Leaf x" using conv' by simp
    have "matching_root (fst (DeriveFromTree (Leaf s'))) pred" using NoneSome s'_def by auto
    then show ?thesis using wf by blast
  next
    case (SomeSome a b) 
    then have "\<not> conflict_free'' pred pred' (Leaf x)" by simp
     then have "False" using Leaf.prems(2) by auto
     then show ?thesis by blast
  qed
next
  case (Inner x)
  then have 1:"is_nonterminal x" by simp
  obtain s a where "(s, a) = DeriveFromTree (Leaf x)" by auto
  then  have s:"s = x \<and> a = [x]" by simp
  show ?case
  proof (cases pred)
    case NoneNone
      from 1 have terminal:"grammar4.is_nonterminal (convert 0 x)" using terminal_equality_gram4'  sorry
      obtain leaf where def:"leaf = (Inner (convert 0 x))" by blast
      with terminal have wf:"grammar4.Tree_wf leaf" by simp
      obtain s' a' where  deriv:"DeriveFromTree leaf = (s', a')" by force
      with def have s'_def:"s' = (convert 0 x) \<and> a' = [convert 0 x]" by auto
      with  s have  s':"convert_back s' = s \<and> convert_back_sentence a' = a" using backconversion' by auto 
      then have conv:"convert_tree (leaf) = Inner x" using def s'_def s by simp
      have "s' \<in> Inl ` new_nonterm" sorry (*holds because of convert 0*) 
      then have "matching_root (fst (DeriveFromTree leaf)) pred" using deriv NoneNone by auto
      then show ?thesis using conv wf by auto
  next
    case (SomeNone a)
    then have conv:"fst (DeriveFromTree (Inner x)) = convert_back (last (snd a))" using Inner.prems(2)
      using conflict_free''.elims(2) by blast
    then obtain s' where s'_def:"s' = (last (snd a))" by blast
    have "a \<in> \<RR>'''" using Inner.prems(4) SomeNone using valid_parents.elims(2) by blast
    then have s'_symbol:"s' \<in> (Inl ` \<NN>''' \<union> Inr ` \<TT>''')" using validRules s'_def sorry
    have conv':"x = convert_back s'" using conv s'_def by simp
    then have "grammar4.is_nonterminal s'" using conversion_lemma' [OF 1] s'_symbol by presburger
    then have wf:"grammar4.Tree_wf (Inner s') \<and> convert_tree (Inner s') = Inner x" using conv' by simp
    have "matching_root (fst (DeriveFromTree (Inner s'))) pred" using SomeNone s'_def by auto
    then show ?thesis using wf by blast
  next
    case (NoneSome a)
        then have conv:"fst (DeriveFromTree (Inner x)) = convert_back (hd (snd a))" using Inner.prems(2)
      using conflict_free''.elims(2) by blast
    then obtain s' where s'_def:"s' = (hd (snd a))" by blast
    have "a \<in> \<RR>'''" using Inner.prems(4) NoneSome using valid_parents.elims(2) by blast
    then have s'_symbol:"s' \<in> (Inl ` \<NN>''' \<union> Inr ` \<TT>''')" using validRules s'_def sorry
    have conv':"x = convert_back s'" using conv s'_def by simp
    then have "grammar4.is_nonterminal s'" using conversion_lemma' [OF 1] s'_symbol by presburger
    then have wf:"grammar4.Tree_wf (Inner s') \<and> convert_tree (Inner s') = Inner x" using conv' by simp
    have "matching_root (fst (DeriveFromTree (Inner s'))) pred" using NoneSome s'_def by auto
    then show ?thesis using wf by blast
  next
    case (SomeSome a b) 
    then have "\<not> conflict_free'' pred pred' (Inner x)" by simp
     then have "False" using Inner.prems(2) by auto
     then show ?thesis by blast
  qed
next
  case (DT r b)
  (*case distinction ? on whether parents or not*)

   obtain N \<alpha> where rule:"(N, \<alpha>) \<in> \<RR>''' \<and> convertback_rule (N, \<alpha>) = r \<and> matching_root N pred" using DT.prems(2) DT.prems(4)ruleexists 
     by (smt (z3) case_prodE)
   (*middle trees*)
     have "\<forall> t \<in> set (butlast (tl b)) . Tree_wf t \<Longrightarrow> conflict_free'' (None, None) (None, None) T \<Longrightarrow> conflict_free T"
    (*effectively by default, now have to add matching root for these*) sorry
    obtain midb where "midb = (butlast (tl b))" by blast
    obtain midbconv where midcorr:"list_all grammar4.Tree_wf midbconv \<and>  map convert_tree midbconv = midb" sorry
    have mid_roots:"map (fst \<circ> DeriveFromTree) midbconv = (butlast (tl \<alpha>))" sorry

   (*hd *)
   have hd_exists:"\<exists> T'. grammar4.Tree_wf T' \<and>  convert_tree T' = hd b \<and> (fst (DeriveFromTree T')) = (hd \<alpha>)"
   proof (cases pred)
     case NoneNone
      obtain b' where b'def:"b' = hd b" by blast
    then have wf:"Tree_wf b' \<and> conflict_free b'" using DT.prems(3) DT.prems(1) 
     sorry(*wf, DT might have to be declared non_empty*)
    then have "conflict_free'' (None, Some (N, \<alpha>)) (None, None) b'" sorry (*based on conflictfreedom and no higher ones*)
    with wf have "\<exists> T'. grammar4.Tree_wf T' \<and>  convert_tree T' = b' 
        \<and> matching_root (fst (DeriveFromTree T')) (None, Some (N, \<alpha>))" using DT.prems sorry (*IH hidden, also uses valid_parents*)
    then obtain b'_conv where hd_corr:"grammar4.Tree_wf  b'_conv \<and>  convert_tree  b'_conv = b' 
        \<and> matching_root (fst (DeriveFromTree  b'_conv)) (None, Some (N, \<alpha>))" by blast
    then have hd_roots:"hd \<alpha> = (fst (DeriveFromTree b'_conv))" by simp
     then show ?thesis using hd_corr b'def by auto
   next
     case (SomeNone a)
        obtain b' where b'def:"b' = hd b" by blast
    then have wf:"Tree_wf b' \<and> conflict_free b'" using DT.prems(3) DT.prems(1) 
      sorry (*wf, DT might have to be declared non_empty*)
    then have "conflict_free'' (None, Some (N, \<alpha>)) pred  b'" sorry (*based on conflictfreedom and no higher ones*)
    with wf have "\<exists> T'. grammar4.Tree_wf T' \<and>  convert_tree T' = b' 
        \<and> matching_root (fst (DeriveFromTree T')) (None, Some (N, \<alpha>))" using DT.prems sorry (*IH hidden*)
    then obtain b'_conv where hd_corr:"grammar4.Tree_wf  b'_conv \<and>  convert_tree  b'_conv = b' 
        \<and> matching_root (fst (DeriveFromTree  b'_conv)) (None, Some (N, \<alpha>))" by blast
    then have hd_roots:"hd \<alpha> = (fst (DeriveFromTree b'_conv))" by simp
     then show ?thesis using hd_corr b'def by auto
   next
     case (NoneSome a)
        obtain b' where b'def:"b' = hd b" by blast
    then have wf:"Tree_wf b' \<and> conflict_free b'" using DT.prems(3) DT.prems(1) 
      sorry (*wf, DT might have to be declared non_empty*)
    then have "conflict_free'' (None, Some (N, \<alpha>)) (None, None) b'" sorry (*based on conflictfreedom and no higher ones*)
    with wf have "\<exists> T'. grammar4.Tree_wf T' \<and>  convert_tree T' = b' 
        \<and> matching_root (fst (DeriveFromTree T')) (None, Some (N, \<alpha>))" using DT.prems sorry (*IH hidden*)
    then obtain b'_conv where hd_corr:"grammar4.Tree_wf  b'_conv \<and>  convert_tree  b'_conv = b' 
        \<and> matching_root (fst (DeriveFromTree  b'_conv)) (None, Some (N, \<alpha>))" by blast
    then have hd_roots:"hd \<alpha> = (fst (DeriveFromTree b'_conv))" by simp
     then show ?thesis using hd_corr b'def by auto
   next
     case (SomeSome a a')
     then have "\<not> conflict_free'' pred pred' (DT r b)" by simp
     then have "False" using DT.prems(2) by auto
     then show ?thesis by blast
   qed

    (*tl *)
   have tl_exists:"\<exists> T'. grammar4.Tree_wf T' \<and>  convert_tree T' = last b \<and> (fst (DeriveFromTree T')) = (last \<alpha>)"
   proof (cases pred)
     case NoneNone
    obtain b'' where  b'def:"b'' = last b" by blast
    then have wf:"Tree_wf b'' \<and> conflict_free b''" using DT.prems(3) DT.prems(1) 
      sorry (*wf, DT might have to be declared non_empty*)
    then have "conflict_free'' (Some (N, \<alpha>), None) (None, None) b''" sorry
    with wf have "\<exists> T'. grammar4.Tree_wf T' \<and>  convert_tree T' = b'' 
        \<and> matching_root (fst (DeriveFromTree T')) (Some (N, \<alpha>), None)" using DT.prems sorry (*IH hidden*)
    then obtain b''_conv where tl_corr:"grammar4.Tree_wf  b''_conv \<and>  convert_tree  b''_conv = b'' 
        \<and> matching_root (fst (DeriveFromTree  b''_conv)) (Some (N, \<alpha>), None )" by blast
    then have tl_roots:"last \<alpha> = (fst (DeriveFromTree b''_conv))" by simp  
    then show ?thesis using tl_corr b'def by auto
   next
     case (SomeNone a)(*possible inherited higherup conflict \<Longrightarrow> case distinction?*)
         obtain b'' where  b'def:"b'' = last b" by blast
    then have wf:"Tree_wf b'' \<and> conflict_free b''" using DT.prems(3) DT.prems(1) 
     sorry(*wf, DT might have to be declared non_empty*)
    then have "conflict_free'' (Some (N, \<alpha>), None) pred' b''" sorry
    with wf have "\<exists> T'. grammar4.Tree_wf T' \<and>  convert_tree T' = b'' 
        \<and> matching_root (fst (DeriveFromTree T')) (Some (N, \<alpha>), None)" using DT.prems sorry (*IH hidden*)
    then obtain b''_conv where tl_corr:"grammar4.Tree_wf  b''_conv \<and>  convert_tree  b''_conv = b'' 
        \<and> matching_root (fst (DeriveFromTree  b''_conv)) (Some (N, \<alpha>), None )" by blast
    then have tl_roots:"last \<alpha> = (fst (DeriveFromTree b''_conv))" by simp  
    then show ?thesis using tl_corr b'def by auto
   next
     case (NoneSome a)(*additional higherup conflict through parent *)
        obtain b'' where  b'def:"b'' = last b" by blast
    then have wf:"Tree_wf b'' \<and> conflict_free b''" using DT.prems(3) DT.prems(1) 
      sorry (*wf, DT might have to be declared non_empty*)
    then have "conflict_free'' (Some (N, \<alpha>), None) pred b''" sorry
    with wf have "\<exists> T'. grammar4.Tree_wf T' \<and>  convert_tree T' = b'' 
        \<and> matching_root (fst (DeriveFromTree T')) (Some (N, \<alpha>), None)" using DT.prems sorry (*IH hidden*)
    then obtain b''_conv where tl_corr:"grammar4.Tree_wf  b''_conv \<and>  convert_tree  b''_conv = b'' 
        \<and> matching_root (fst (DeriveFromTree  b''_conv)) (Some (N, \<alpha>), None )" by blast
    then have tl_roots:"last \<alpha> = (fst (DeriveFromTree b''_conv))" by simp  
    then show ?thesis using tl_corr b'def by auto
   next
     case (SomeSome a a')
     then have "\<not> conflict_free'' pred pred' (DT r b)" by simp
     then have "False" using DT.prems(2) by auto
     then show ?thesis by blast
   qed
   (*how many case distinctions even needed?*)
   from hd_exists obtain b'_conv where  hd_corr:"grammar4.Tree_wf b'_conv \<and> convert_tree b'_conv = hd b" and hd_roots:"fst (DeriveFromTree b'_conv) = hd \<alpha> " by blast
   from tl_exists obtain b''_conv where tl_corr:"grammar4.Tree_wf b''_conv \<and> convert_tree b''_conv = last b" and tl_roots:"fst (DeriveFromTree b''_conv) = last \<alpha> " by blast

    have "\<alpha> = map (fst \<circ> DeriveFromTree ) (b'_conv#midbconv@[b''_conv])" using tl_roots hd_roots mid_roots 
     sorry
    then have concat:"\<alpha> = concat (map grammar4.TreeSym (b'_conv#midbconv@[b''_conv]))" sorry 
    have  convert_tree:"convert_tree b'_conv # map convert_tree midbconv @ [convert_tree b''_conv] = b" 
      using tl_corr hd_corr midcorr sorry
    obtain T where T_def:"T = (DT (N, \<alpha>) (b'_conv#midbconv@[b''_conv]))" by blast
    then have T_wf:"grammar4.Tree_wf T" using concat tl_corr rule hd_corr midcorr by fastforce
    have root:"matching_root N  pred" sorry (*derives from 0-index and pred being None None*)
    have "convertback_rule (N, \<alpha>) = r" using rule by blast
    then have "convert_tree T = (DT r b)" using T_def convert_tree by simp
    with T_wf have "\<exists>T'. grammar4.Tree_wf T' \<and> convert_tree T' = (DT r b) \<and> 
          matching_root (fst (DeriveFromTree T')) pred" using root T_def by fastforce 
   then show ?case by blast

qed

lemma conversion:"\<exists> tree . grammar4.Tree_wf tree \<and> convert_tree tree = T  \<Longrightarrow>  \<exists> tree . grammar4.Tree_wf tree 
  \<and> fst (DeriveFromTree tree) =  convert 0 (fst (DeriveFromTree T)) \<and> convert_tree tree = T"
  sorry
lemma convert_tree_implies_derives_conversion:"convert_tree (T) = T' \<Longrightarrow> convertback_rule (DeriveFromTree T) = DeriveFromTree T'"
proof (induction T)
  case (Leaf x)
  then show ?case sorry
next
  case (Inner x)
  then show ?case sorry
next
  case (DT r  b)
  then show ?case sorry
qed



(*should work differently in theory*)
lemma word_implies_grammar4_word:"is_word xa \<Longrightarrow> grammar4.is_word (map (convert i) xa)"
  apply(auto simp add: is_word_def grammar4.is_word_def grammar4.is_terminal_def is_terminal_def)
  using terminal_set_eq apply(simp)
  sorry

lemma word_derivations4:
  assumes "DeriveFromTree tree = (\<SS>, xa) " "Tree_wf tree "
  shows " grammar4.is_derivation  (map (convert i) xa)"
        (*" \<exists> x' . grammar4.is_derivation  x' \<and> convert_back_sentence x' = xa"*)
proof -
  (*completeness*)
  from assms obtain cf where "DeriveFromTree cf = (\<SS>, xa) \<and>Tree_wf cf \<and> conflict_free cf " sorry
  then  obtain T' where " grammar4.Tree_wf T' \<and>
         (\<SS>, xa) = convertback_rule (DeriveFromTree T') \<and> convert_tree T' = cf" 
    using  (*grammar4_super_conflict_free*) convert_tree_implies_derives_conversion sorry (*need to use strengthened lemma now*)
  then have "DeriveFromTree T' = (grammar4.\<SS>, (map (convert i) xa))" sorry 
      (*probably need something implicit*)
  then have "\<exists> D . grammar4.Derivation [grammar4.\<SS>] D (map (convert i) xa)" sorry
  then show ?thesis 
    using \<open>DeriveFromTree T' = (grammar4.\<SS>, map (convert i) xa)\<close> \<open>grammar4.Tree_wf T' \<and> (\<SS>, xa) = convertback_rule (DeriveFromTree T') \<and> convert_tree T' = cf\<close> 
      grammar4.DeriveFromTree_implies_is_derivation by presburger
qed


lemma is_word4:"is_word xa \<Longrightarrow> map projr xa = map projr (map (convert i) xa)"
  apply(auto simp add: is_word_def is_terminal_def)
  by (metis old.sum.simps(5) old.sum.simps(6) projr_def sum.exhaust_sel)



lemma grammar4_word_implies_word:"grammar4.is_word xa \<Longrightarrow> is_word (convert_back_sentence xa)"
  apply(auto simp add: is_word_def grammar4.is_word_def 
        grammar4.is_terminal_def is_terminal_def)
  using terminal_set_eq apply(simp) 
sorry

lemma \<SS>_equal:"convert_back grammar4.\<SS> = \<SS>"
proof -
  have 1:"grammar4.\<SS> =  Inl \<SS>'''" using grammar4.\<SS>_def by blast  
  have  "\<SS>''' = projl (get_s \<GG>'')" using \<SS>'''_def by simp 
  with 1 have 2:"grammar4.\<SS> = get_s \<GG>''" sorry
  obtain N T R s N' T' R' s' where def:"\<GG>'' = (N, T, R, s) \<and> \<GG>' = (N', T', R', s')" 
    by (meson \<GG>''_valid nonterm_sub.elims(2))
  then have "s' = s" using \<GG>''_valid by simp
  then have "get_s \<GG>'' = get_s \<GG>'" using def by auto
  then have "grammar4.\<SS> = get_s \<GG>'" using 2 by auto
  then show ?thesis sorry (*inherited from other grammar*)
qed 
lemma word_derivations4':
  assumes "DeriveFromTree tree = (grammar4.\<SS>, xa) " "grammar4.Tree_wf tree " 
  shows " is_derivation  (convert_back_sentence xa)"
proof -
  obtain T' where "T' = convert_tree tree" by blast
  with assms have wf:"Tree_wf T' \<and>  
  convertback_rule (DeriveFromTree tree) = DeriveFromTree T'" using grammar4_sub_0 \<SS>_equal by blast
  with assms have "DeriveFromTree T' = (\<SS>, convert_back_sentence xa)" using \<SS>_equal by simp
  then have "\<exists> D. Derivation [\<SS>] D (convert_back_sentence xa)" 
    using wf DeriveFromTree_implies_is_derivation  derives_implies_Derivation is_derivation_def by blast
  then have "is_derivation  (convert_back_sentence xa)" using Derivation_implies_derives is_derivation_def by blast
  then show ?thesis by blast 
qed

lemma is_word4':"grammar4.is_word xa \<Longrightarrow> map projr xa = map projr (convert_back_sentence xa)"
  apply(auto simp add: grammar4.is_word_def grammar4.is_terminal_def)
   by (metis old.sum.simps(5) old.sum.simps(6) projr_def sum.exhaust_sel)


theorem \<L>_t_equal:"grammar4.\<L>_t = \<L>_t"
  apply(auto simp add:  \<L>_t_def grammar4.\<L>_t_def  \<L>_def  grammar4.\<L>_def grammar4.is_derivation_def 
      dest!: grammar4.derives_implies_Derivation grammar4.DerivationSymbol_implies_DerivTree)
  using grammar4.\<SS>_symbol apply blast
  using word_derivations4' grammar4_word_implies_word is_word4' is_derivation_def apply blast
  apply(auto simp add: is_derivation_def  \<L>_t_def grammar4.\<L>_t_def  \<L>_def  grammar4.\<L>_def
        dest!: derives_implies_Derivation DerivationSymbol_implies_DerivTree [ OF _ \<SS>_symbol]  )
  using word_derivations4 word_implies_grammar4_word is_word4 grammar4.is_derivation_def by blast 
end
end