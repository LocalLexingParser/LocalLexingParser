theory SPPF
  imports "LocalLexing2.LLEarleyParsing" DerivationTrees1
begin
text "Defines SFFP output of Earley Parser" 


type_synonym ('a, 'b) pointers = "('a, 'b) item \<Rightarrow> (('a, 'b) item \<times> nat) option"
(*or just reuse this nat notion*)
                    
type_synonym ('a, 'b) sppf_pointers = "('a, 'b) pointers \<times> ('a, 'b) pointers" 
(*predecessor, reduction*)

(*might be easier to add an measure that gets calculated on the fly*)

type_synonym ('a, 'b) sppf_items = "('a, 'b) items  \<times> ('a, 'b) sppf_pointers" 
(*add an additional nat for measure*)


datatype ('a, 'b) sppf = Node
  (node_head:"('a, 'b) symbol")
  (node_production:"('a, 'b) symbol list")
  (node_dot:nat)
  (node_origin:nat)
  (node_end:nat)

definition sppf_nonterminal :: "('a, 'b) sppf \<Rightarrow> ('a, 'b) symbol"
where
  "sppf_nonterminal x = node_head x"

definition sppf_rhs :: "('a, 'b) sppf \<Rightarrow> ('a, 'b) sentence"
where
  "sppf_rhs x = node_production x"

definition sppf_\<alpha> :: "('a, 'b) sppf \<Rightarrow> ('a, 'b) sentence"
where
  "sppf_\<alpha> x = take (node_dot x) (sppf_rhs x)"

definition sppf_\<beta> :: "('a, 'b) sppf \<Rightarrow> ('a, 'b) sentence"
where 
  "sppf_\<beta> x = drop (node_dot x) (sppf_rhs x)"


derive ccompare "item"
context LocalLexing begin

lemma csorted_set_distinct:
  fixes X :: "(('a, 'b) item \<times> 'c list) set"
  assumes "finite X"
  shows csorted_set: "set (csorted_list_of_set X) = X" and csorted_distinct: "distinct (csorted_list_of_set X)"
proof -
  have ID_ccompare_SomeI: "ID ccompare \<noteq> (None :: 'd :: ccompare comparator option) \<Longrightarrow>
    ID ccompare = Some (ccomp :: 'd comparator)"
    by simp
  have c: "ID ccompare = Some (ccomp :: (('a, 'b) item \<times> 'c list) comparator)"
    apply (rule ID_ccompare_SomeI)
    unfolding is_ccompare_item[unfolded is_ccompare_def] is_ccompare_prod[unfolded is_ccompare_def] is_ccompare_list[unfolded is_ccompare_def]
    using ccomp
    by auto
  note cl = ID_ccompare[OF c]
  show "set (csorted_list_of_set X) = X"
    using assms
    unfolding csorted_list_of_set_def
    by (subst c) (auto simp: linorder.set_sorted_list_of_set[OF cl assms])
  show "distinct (csorted_list_of_set X)"
    using assms
    unfolding csorted_list_of_set_def
    by (subst c) (auto simp: linorder.distinct_sorted_list_of_set[OF cl])
qed


lemma csorted_set_distinct':
  fixes X :: "(('a, 'b) item \<times> ('a, 'b) item) set"
  assumes "finite X"
  shows csorted_set': "set (csorted_list_of_set X) = X" and csorted_distinct': "distinct (csorted_list_of_set X)"
proof -
  have ID_ccompare_SomeI: "ID ccompare \<noteq> (None :: 'd :: ccompare comparator option) \<Longrightarrow>
    ID ccompare = Some (ccomp :: 'd comparator)"
    by simp
  have c: "ID ccompare = Some (ccomp :: (('a, 'b) item \<times> ('a, 'b) item) comparator)"
    apply (rule ID_ccompare_SomeI)
    unfolding is_ccompare_item[unfolded is_ccompare_def] is_ccompare_prod[unfolded is_ccompare_def]
    using ccomp
    by auto
  note cl = ID_ccompare[OF c]
  show "set (csorted_list_of_set X) = X"
    using assms
    unfolding csorted_list_of_set_def
    by (subst c) (auto simp: linorder.set_sorted_list_of_set[OF cl assms])
  show "distinct (csorted_list_of_set X)"
    using assms
    unfolding csorted_list_of_set_def
    by (subst c) (auto simp: linorder.distinct_sorted_list_of_set[OF cl])
qed

lemma csorted_set_distinct'':
  fixes X :: "(('a, 'b) item) set"
  assumes "finite X"
  shows csorted_set'': "set (csorted_list_of_set X) = X" and csorted_distinct'': "distinct (csorted_list_of_set X)"
proof -
  have ID_ccompare_SomeI: "ID ccompare \<noteq> (None :: 'd :: ccompare comparator option) \<Longrightarrow>
    ID ccompare = Some (ccomp :: 'd comparator)"
    by simp
  have c: "ID ccompare = Some (ccomp :: (('a, 'b) item) comparator)"
    apply (rule ID_ccompare_SomeI)
    unfolding is_ccompare_item[unfolded is_ccompare_def] 
    using ccomp
    by auto
  note cl = ID_ccompare[OF c]
  show "set (csorted_list_of_set X) = X"
    using assms
    unfolding csorted_list_of_set_def
    by (subst c) (auto simp: linorder.set_sorted_list_of_set[OF cl assms])
  show "distinct (csorted_list_of_set X)"
    using assms
    unfolding csorted_list_of_set_def
    by (subst c) (auto simp: linorder.distinct_sorted_list_of_set[OF cl])
qed

(*need a simpler measure to guarantee monotonicity on the pointers*)
fun  measure_help::"('a,'b) sppf_pointers \<Rightarrow> ('a, 'b) item \<Rightarrow> nat" where
"measure_help (pred, red ) i = (if i \<notin> (dom pred) then 0 else snd (the ( pred i)))"

definition reduction_pointers::"('a, 'b) pointers" where
"reduction_pointers = Map.empty"


definition predecessor_pointers::"('a, 'b) pointers" where
"predecessor_pointers = Map.empty"

definition is_lexed::"('a, 'b) item \<Rightarrow> ('a, 'b) item \<Rightarrow> bool" where
"is_lexed p x = ((item_end x - item_end p) \<in> (Lex (item_rhs p! item_dot p) Doc (item_end p)))"

fun correct_red_pred_match::"('a, 'b) sppf_pointers \<Rightarrow> bool" where
"correct_red_pred_match (pred, red) = (\<forall> node \<in> (dom red) . next_symbol (fst (the (pred node)))
 = Some (item_nonterminal (fst (the (red node)))))"

fun correct_lexing::"('a, 'b) sppf_pointers \<Rightarrow> bool" where
"correct_lexing (pred, red) = (\<forall> x \<in> (dom pred) . x \<notin> dom red \<longrightarrow>
    is_lexed (fst (the (pred x))) x)"

fun correct_bounds::"('a, 'b) sppf_pointers \<Rightarrow> bool" where
"correct_bounds (pred, red) = (\<forall> x \<in> (dom pred) . item_origin x = item_origin (fst (the (pred x))) 
  \<and> item_end x \<ge> item_end (fst (the (pred x))) \<and> (\<forall> x \<in> (dom red) . item_origin (fst (the (red x))) = item_end (fst (the (pred x))) \<and> 
    item_end x = item_end (fst (the (red x)))))"
fun red_implies_pred_dom::"('a, 'b) sppf_pointers \<Rightarrow> bool" where
"red_implies_pred_dom (pred, red) = ( dom red \<subseteq> dom pred)"
(*other relations to predecessor*)
fun  pred_increments::"('a, 'b) sppf_pointers \<Rightarrow> bool" where
"pred_increments (pred, red) = (\<forall> node \<in>  (dom pred) . item_dot node = (Suc (item_dot (fst (the (pred node)))))
  \<and> item_rule node = item_rule (fst (the (pred node))))"

fun no_red_implies_terminal::"('a, 'b) sppf_pointers \<Rightarrow> bool" where
"no_red_implies_terminal (pred, red) = (\<forall> node \<in>  (dom pred) . node \<notin> (dom red) 
    \<longrightarrow> (\<exists> t . next_symbol (fst (the (pred node))) = Some t \<and> is_terminal t))"
fun invariant_pointers'::"('a, 'b) sppf_pointers \<Rightarrow> bool" where
"invariant_pointers' s = (pred_increments s \<and> correct_bounds s \<and> correct_lexing s \<and> 
  correct_red_pred_match s \<and> red_implies_pred_dom s \<and> no_red_implies_terminal s)"

fun dom_sup_items::"('a, 'b) sppf_pointers \<Rightarrow> ('a, 'b) items \<Rightarrow> bool" where
"dom_sup_items (pred, red) I =  ({i . i\<in> I \<and> item_dot i >0} \<subseteq> dom pred)" (*this actually implies zero dot too*)

fun dom_no_scan::"('a, 'b) sppf_pointers \<Rightarrow> ('a, 'b) items \<Rightarrow> bool" where
"dom_no_scan (pred, red) I = (\<forall> node \<in> I . node \<notin> dom (pred) \<longrightarrow> item_origin node = item_end node)"

fun Predict' :: "nat \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow> ('a, 'b) sppf_items"
where
  "Predict' k (I, p) = (Predict k I, p)" (*what can be said about added states here?*)

(*theorem "is_ccompare TYPE (('a, 'b) item)"*)

lemma Predict'_bounds:"valid_bounds I \<Longrightarrow> valid_bounds (fst (Predict' k (I, p))) "
  by (auto simp add: Predict_bounds)
lemma Predict'_finite:"finite I \<Longrightarrow> Predict' k (I, p) = (I', p') \<Longrightarrow> finite I'"
  by (auto simp add:Predict_Finite') 

lemma Predict'_rule:"valid_rule I \<Longrightarrow> valid_rule (fst (Predict' k (I, p)))"
  by (auto simp add: Predict_rule)

lemma Predict_eq:"fst (Predict' k  I)  = Predict k (fst I)"
  using Predict_def 
  by (metis (no_types, hide_lams) Predict'.elims fst_conv)

lemma Predict'_dom_sup:
  assumes "dom_sup_items p I" "Predict' k (I, p) = (I', p') "
  shows  "dom_sup_items p' I'"
proof -
  from Predict_top assms(2) have 1:"I' \<subseteq> I \<union> (\<lambda>r. init_item r k) ` \<RR>" by auto
  have "{i . i\<in> ((\<lambda>r. init_item r k) ` \<RR>) \<and> item_dot i >0} = {}" by auto
  with 1 have "{i . i\<in> I' \<and> item_dot i >0} \<subseteq> {i . i\<in> I \<and> item_dot i >0}" by blast
  with assms(1) have "{i . i\<in> I' \<and> item_dot i >0} \<subseteq> dom (fst p)" 
    by (metis (no_types, lifting)  dom_sup_items.elims(2) fst_conv subsetD subsetI)
  then show ?thesis using assms(2) 
    by (metis (no_types, lifting)  Pair_inject Predict'.simps dom_sup_items.elims(3) fst_conv)
qed

lemma Predict'_dom_no_scan:
  assumes "dom_no_scan p I" "Predict' k (I, p) = (I', p')"
  shows "dom_no_scan p' I'"
proof -
  from assms(2) have eq:"p = p'" by simp
  from Predict_top assms(2) have 1:"I' \<subseteq> I \<union> (\<lambda>r. init_item r k) ` \<RR>" by auto
  from assms eq have 2:"(\<forall> node \<in> I . node \<notin> dom (fst p') \<longrightarrow> item_origin node = item_end node)" 
    apply(cases p') by auto
  from 1 have "\<forall> i \<in> (\<lambda>r. init_item r k) ` \<RR> . item_origin i = item_end i" by simp
  with 1 2 have "(\<forall> node \<in> I' . node \<notin> dom (fst p') \<longrightarrow> item_origin node = item_end node)" 
    apply(cases p') by auto
  then show ?thesis apply(cases p') by simp
qed
(*prove of acyclicity \<Longrightarrow> also, if pointed to, can't change*)

fun Complete_pointers_step::"('a, 'b) sppf_pointers \<Rightarrow> (('a, 'b) item\<times> ('a, 'b) item) \<Rightarrow> ('a, 'b) sppf_pointers" where
"Complete_pointers_step (pred, red) (p', r')= (if ((inc_item p' (item_end r')) \<notin> (dom pred))
   then (pred((inc_item p' (item_end r'))\<mapsto> (p',  (measure_help (pred, red) p') + (measure_help (pred , red) r') + 1)), 
        red((inc_item p' (item_end r'))\<mapsto> (r', 0)) ) 
    else (pred, red) )"

fun Complete_pointers::"('a, 'b) sppf_pointers \<Rightarrow> (('a, 'b) item \<times> ('a, 'b) item) set \<Rightarrow> ('a, 'b) sppf_pointers" where
"Complete_pointers p I = foldl Complete_pointers_step 
       p (csorted_list_of_set I)"

fun Complete_extend::"nat \<Rightarrow> ('a, 'b) items \<Rightarrow> (('a, 'b) item \<times> ('a, 'b) item) set" where
"Complete_extend k I= { (x, y) | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y)}"

fun Complete' :: "nat \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow> ('a, 'b) sppf_items"
where
  "Complete' k (I, p) = (Complete k I,  (Complete_pointers p (Complete_extend k I)))"

lemma Complete'_finite:"finite I \<Longrightarrow> Complete' k (I, p) = (I', p') \<Longrightarrow> finite I'"
  by (auto simp add: Complete_Finite')

lemma Complete'_bounds:"valid_bounds I \<Longrightarrow> Complete' k (I, p) = (I', p') \<Longrightarrow> valid_bounds I'"
  by (auto simp add: Complete_bounds)

lemma Complete'_rule:"valid_rule I \<Longrightarrow> Complete' k (I, p) = (I',p') \<Longrightarrow> valid_rule I'"
  by (auto simp add: Complete_rule)

fun in_set::"('a, 'b) sppf_pointers \<Rightarrow> ('a, 'b) items \<Rightarrow> bool" where
"in_set (pred, red) I = (\<forall> (i', k) \<in> (ran red \<union> ran pred). (i' \<in> I))"

fun red_complete::"('a, 'b) sppf_pointers  \<Rightarrow> bool" where
"red_complete (pred, red) = (\<forall> (i, k) \<in> (ran red) . is_complete i)"


fun measure_help_monotone::"('a, 'b) sppf_pointers \<Rightarrow> bool" where
"measure_help_monotone (pred, red) = ((\<forall> i \<in> (dom pred ) . (measure_help (pred, red) i) > (measure_help (pred, red) 
  (fst (the (pred i))))) \<and> (\<forall> i \<in> (dom red ) . (measure_help (pred, red) i) > (measure_help (pred, red) 
  (fst (the (red i))))))"

(*
lemma "dom_sup_items p I \<Longrightarrow> case  Complete' k (I, p) of (I', p') \<Rightarrow> dom_sup_items p' I'"
  apply (cases p) apply auto 
*)

definition Completable::"('a, 'b) item \<Rightarrow> ('a, 'b) item \<Rightarrow> bool" where
"Completable pred red = (next_symbol pred = Some (fst (item_rule red)) \<and> (item_end pred = item_origin red))"

lemma Complete_pointers_step:
  assumes "Complete_pointers_step  p (pred_i, red_i) = p'"
        "measure_help_monotone p \<and> red_complete p" "is_complete red_i" 
        "in_set p I" "pred_i \<in> I" "red_i \<in> I" 
        "invariant_pointers' p" 
        "Completable pred_i red_i" "dom_sup_items p I" "valid_bounds I"
  shows "measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I \<and> invariant_pointers' p' \<and> dom_sup_items p' I \<and> valid_bounds I"
proof -
  obtain new_i where new_def:"new_i = (inc_item pred_i (item_end red_i))" by blast
  from assms have p_simp:"p' = (if ((inc_item pred_i (item_end red_i)) \<notin> (dom (fst p)))
   then ((fst p)((inc_item pred_i (item_end red_i))\<mapsto> (pred_i,  (measure_help p pred_i) + (measure_help p red_i) + 1)), 
        (snd p)((inc_item pred_i (item_end red_i))\<mapsto> (red_i, 0))) else p)" 
    by (metis Complete_pointers_step.simps prod.collapse)
  (*new item values*)
  have new_val:"item_dot new_i = Suc (item_dot pred_i) \<and> item_rule new_i = item_rule pred_i \<and>
        item_end new_i = item_end red_i \<and> item_origin new_i = item_origin pred_i" using new_def by simp 
  (*No item to be added*)
  {assume  "new_i \<in> dom (fst p)"
    with p_simp new_def have "p' = p" by simp
    with assms have "measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I \<and> invariant_pointers' p' \<and> dom_sup_items p' I" by simp
  }
  then have 1:"new_i \<in> dom (fst p) \<Longrightarrow> measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I
    \<and> invariant_pointers' p' \<and> dom_sup_items p' I \<and> valid_bounds I" using assms(10) by blast
  (*Item added*)
  {
    assume  assms':"new_i \<notin> dom (fst p)"
    with p_simp new_def have p_simp':"fst p' = (fst p)(new_i
          \<mapsto> (pred_i,  (measure_help p pred_i) + (measure_help p red_i) + 1))" 
       and p_simp'':"snd p' =  (snd p)(new_i\<mapsto> (red_i, 0))" apply simp using p_simp new_def assms' by simp
    then have new_dom:"dom (fst p') = dom (fst p) \<union> {new_i}" 
          and new_dom':"dom (snd p') = dom (snd p) \<union> {new_i} "by auto 
   
    (*measure pred*)
    (*premise*)
    from assms(2) have prem_mon:"(\<forall> i \<in> (dom (fst p)) . (measure_help p i) > (measure_help p 
  (fst (the ((fst p) i)))))"by (metis measure_help_monotone.simps prod.collapse)
    from p_simp' have map_unchanged:"\<forall> i . new_i \<noteq> i \<longrightarrow> (fst p') i = (fst p) i" by auto
    from new_val have "item_dot new_i > 0" by simp
    with assms(9) assms'  have new_not_in_I:"new_i \<notin> I" apply(cases p) by auto  
    with assms(4) have "new_i \<notin> fst ` (ran (fst p) \<union> ran (snd p))" apply(cases p)  by auto
    (*prove measure not changing*)
    from map_unchanged assms' have  fst_unchanged:"\<forall> i \<in> dom (fst p) . (fst p') i = (fst p) i" by auto
    have measure_invar:"\<forall> i \<in> dom (fst p) . measure_help p' i = measure_help p i"
      using map_unchanged  surjective_pairing assms' 
      by (metis UnI1 measure_help.simps new_dom) 
    (*prove mapped to not changing*)
    have dom_ran:"\<forall> i \<in> dom (fst p) . the ((fst p) i) \<in> ran (fst p)" by (auto simp add: ran_def)
    from assms(4) have "\<forall> i \<in> ran (fst p) .  fst i \<in> I" apply (cases p) by auto
    then have "\<forall> i \<in> dom (fst p) . fst (the ((fst p) i)) \<in> I" using dom_ran by auto
    with new_not_in_I have "\<forall> i \<in> dom (fst p) . fst (the ((fst p) i)) \<noteq> new_i" by blast
    then have measure_invar':"\<forall> i \<in> dom (fst p) . measure_help p' (fst (the ((fst p) i))) = measure_help p (fst (the ((fst p) i)))"
      using map_unchanged by (metis Un_empty_right Un_insert_right insertE measure_help.simps measure_invar new_dom prod.collapse)(*need a few others to*)
    then have "\<forall> i \<in> dom (fst p) . measure_help p' (fst (the ((fst p') i))) = measure_help p (fst (the ((fst p) i)))"
      using fst_unchanged by auto
    with prem_mon measure_invar have fst_p'_mon:"(\<forall> i \<in> (dom (fst p)) . (measure_help p' i) > (measure_help p' 
  (fst (the ((fst p') i)))))" by simp
    (*new_item added*)
    have neq_pred:"new_i \<noteq> pred_i \<and> new_i \<noteq> red_i" using new_def using assms(5) assms(6) new_not_in_I by blast
    from new_dom have "measure_help p' new_i = snd (the ((fst p') new_i))"
      by (metis Un_iff insertCI measure_help.simps prod.collapse) 
    with p_simp' have "measure_help p' new_i = (measure_help p pred_i) + (measure_help p red_i) + 1" by simp
    with map_unchanged neq_pred have new_i_meas:"measure_help p' new_i = (measure_help p' pred_i) + (measure_help p' red_i) + 1" 
      by (metis (mono_tags, lifting) domD domI measure_help.simps prod.collapse) 
    then have "measure_help p' new_i > measure_help p' (fst (the ((fst p') new_i)))" using p_simp' by auto
    with fst_p'_mon new_dom have measure_monotone:"(\<forall> i \<in> (dom (fst p')) . (measure_help p' i) > (measure_help p' 
  (fst (the ((fst p') i)))))" by simp

    (*measure red*)
    (*premise*) 
    (*\<notin> snd p*)
    from assms(7) have "red_implies_pred_dom p" by simp
    then  have dom1:"dom (snd p) \<subseteq> dom (fst p)"
      by (metis red_implies_pred_dom.simps surjective_pairing)
    have assms'':"new_i \<notin> (dom (snd p))" using assms' using dom1 by blast

    from assms(2) have prem_mon':"(\<forall> i \<in> (dom (snd p)) . (measure_help p i) > (measure_help p 
  (fst (the ((snd p) i)))))" by (metis measure_help_monotone.simps prod.collapse)
    from p_simp'' have map_unchanged':"\<forall> i . new_i \<noteq> i \<longrightarrow> (snd p') i = (snd p) i" by auto
    from map_unchanged' assms'' have  snd_unchanged:"\<forall> i \<in> dom (snd p) . (snd p') i = (snd p) i" by auto
    have measure_invar:"\<forall> i \<in> dom (snd p) . measure_help p' i = measure_help p i"
      using map_unchanged'  surjective_pairing assms'' 
      by (metis gr_implies_not0 measure_help.simps measure_invar prem_mon') 

    from new_dom dom1 have red_in_pred:"\<forall> i \<in> dom (snd p) . i \<in> dom (fst p) \<and> i \<in> dom (fst p')" by auto
    have dom_ran':"\<forall> i \<in> dom (snd p) . the ((snd p) i) \<in> ran (snd p)" by (auto simp add: ran_def)
    from assms(4) have "\<forall> i \<in> ran (snd p) .  fst i \<in> I" apply (cases p) by auto
    then have "\<forall> i \<in> dom (snd p) . fst (the ((snd p) i)) \<in> I" by (auto simp add: dom_ran') 
    with new_not_in_I have map_neq_new:"\<forall> i \<in> dom (snd p) . fst (the ((snd p) i)) \<noteq> new_i" by blast
    then have measure_invar':"\<forall> i \<in> dom (snd p) . (fst p') (fst (the ((snd p) i))) 
          = (fst p) (fst (the ((snd p) i)))" using map_unchanged by fast
    from map_neq_new have map_dom':
        "\<forall> i \<in> dom (snd p) . fst (the ((snd p) i)) \<in> dom (fst p) \<longleftrightarrow> 
      fst (the ((snd p) i)) \<in> dom (fst p')" using p_simp' by simp
    have "\<forall> i \<in> dom (snd p) . measure_help p' (fst (the ((snd p) i)))
          = measure_help p (fst (the ((snd p) i)))" apply(cases p) apply(cases p') 
      using measure_invar' map_dom' by auto
    then have "\<forall> i \<in> dom (snd p) . measure_help p' (fst (the ((snd p') i))) = measure_help p (fst (the ((snd p) i)))"
      using snd_unchanged by auto
    with prem_mon' measure_invar have snd_p'_mon:"(\<forall> i \<in> (dom (snd p)) . (measure_help p' i) > (measure_help p' 
  (fst (the ((snd p') i)))))" by simp
    
    (*new item*)
    from new_i_meas have "measure_help p' new_i > measure_help p' (fst (the ((snd p') new_i)))" using p_simp'' by auto
    with snd_p'_mon new_dom' have "(\<forall> i \<in> (dom (snd p')) . (measure_help p' i) > (measure_help p' 
  (fst (the ((snd p') i)))))" by blast 
    with measure_monotone have monotone:"measure_help_monotone p'" 
      using measure_help_monotone.elims(3) by fastforce

    (*in_set p*)
    from p_simp' have ran_fst:"ran (fst p') \<subseteq> ran (fst p) \<union> {(pred_i,  measure_help p pred_i + measure_help p red_i + 1)}" by (auto simp add: ran_def)
    from assms have add:"\<forall> (i, k ) \<in> {(pred_i, 0)} .  i \<in> I" by blast
    from assms(4) have 2:"\<forall> (i, k ) \<in> (ran (fst p)) . i \<in> I" 
      by (metis Un_iff  fst_conv in_set.elims(2))
    from ran_fst add 2 have in_set:"\<forall> (i, k ) \<in> (ran (fst p')) . i \<in> I" by auto

    from p_simp assms' new_def have red_update:"snd p' = (snd p)(new_i \<mapsto> (red_i, 0))" by simp 
    then have 1:"ran (snd p') \<subseteq> ran (snd p) \<union> {(red_i, 0)}" by (auto simp add: ran_def) (*self proved lemma needed*) 

    from assms have add:"\<forall> (i, k ) \<in> {(red_i, 0)} . is_complete i \<and> i \<in> I" by blast
    from assms(4) have 2:"\<forall> (i, k ) \<in> (ran (snd p)) . i \<in> I" 
      by (metis UnI1 assms(4)  in_set.elims(2) snd_conv)
    from assms(2) have "\<forall> (i, k ) \<in> (ran (snd p)) . is_complete i"  
      by (metis red_complete.simps snd_conv surj_pair)
    then have complete:"\<forall> (i, k ) \<in> (ran (snd p')) . is_complete i \<and> i \<in> I" using add 1 2  by auto
    (*invariant_pointers'*)
    (*domain*)

    from red_update have "dom (snd p') = dom (snd p) \<union> {new_i}" by simp
    with new_dom dom1 have "dom (snd p') \<subseteq> dom (fst p')"  by auto
    then have red_pred_dom:"red_implies_pred_dom p'"
      by (metis red_implies_pred_dom.simps surjective_pairing)
    (*pred_increment*)
    from assms(7) have inc1:"(\<forall> node \<in>  (dom (fst p)) . item_dot node = (Suc (item_dot (fst (the ((fst p) node)))))
  \<and> item_rule node = item_rule (fst (the ((fst p) node))))" 
      by (metis invariant_pointers'.elims(2) pred_increments.simps prod.collapse)
    then have inc2:"(\<forall> node \<in>  (dom (fst p)) . item_dot node = (Suc (item_dot (fst (the ((fst p') node)))))
  \<and> item_rule node = item_rule (fst (the ((fst p') node))))" by (simp add: fst_unchanged) (*pointer unchanged*)
    from p_simp' new_val have "item_dot new_i = (Suc (item_dot (fst (the ((fst p') new_i)))))
  \<and> item_rule new_i = item_rule (fst (the ((fst p') new_i)))" by simp
    then have "(\<forall> node \<in>  {new_i} . item_dot node = (Suc (item_dot (fst (the ((fst p') node)))))
  \<and> item_rule node = item_rule (fst (the ((fst p') node))))" by simp
    with inc2 have pred_inc:"(\<forall> node \<in>  (dom (fst p')) . item_dot node = (Suc (item_dot (fst (the ((fst p') node)))))
  \<and> item_rule node = item_rule (fst (the ((fst p') node))))" using new_dom by blast
    (*correct_bounds*)
    from assms(7) have correct_bounds_prem:"correct_bounds p" by simp
    then have bound_pred:"(\<forall> x \<in> (dom (fst p)) . item_origin x = item_origin (fst (the ((fst p) x))) 
  \<and> item_end x \<ge> item_end (fst (the ((fst p) x))))" and 
      bound_red:"(\<forall> x \<in> (dom (snd p)) . item_origin (fst (the ((snd p) x))) = item_end (fst (the ((fst p) x))) \<and> 
    item_end x = item_end (fst (the ((snd p) x))))" 
      apply (metis correct_bounds.simps  prod.collapse) using correct_bounds_prem  apply(cases p) 
      by (metis (no_types, lifting) correct_bounds.simps dom1 fst_conv snd_conv subsetD)
    then have bound_pred':"(\<forall> x \<in> (dom (fst p)) . item_origin x = item_origin (fst (the ((fst p') x))) 
  \<and> item_end x \<ge> item_end (fst (the ((fst p') x))))" and 
      bound_red':"(\<forall> x \<in> (dom (snd p)) . item_origin (fst (the ((snd p') x))) = item_end (fst (the ((fst p') x))) \<and> 
    item_end x = item_end (fst (the ((snd p') x))))" using fst_unchanged apply simp using bound_red dom1 fst_unchanged snd_unchanged
      by (metis assms'' map_unchanged) (*map stays for non updated*)
    (*new_item*)
    from assms(10) have "valid_bounds I" by simp
    with  assms(6) have "item_end red_i \<ge> item_origin red_i" using valid_bounds_def by simp
    with assms(8)  have "item_end red_i \<ge> item_end pred_i"  using Completable_def by simp (*hold by to be proven I_bounds_correct / invariant \<Longrightarrow> items_based*)
    with p_simp' new_val have "item_origin new_i = item_origin (fst (the ((fst p') new_i))) \<and> item_end new_i \<ge> 
      item_end (fst (the ((fst p') new_i)))" by simp   
    with bound_pred' new_dom have bound_pred'':"(\<forall> x \<in> (dom (fst p')) . item_origin x = item_origin (fst (the ((fst p') x))) 
  \<and> item_end x \<ge> item_end (fst (the ((fst p') x))))" by auto
    have "item_end new_i = item_end red_i \<and> item_origin red_i = item_end pred_i" 
      using new_def assms(8) Completable_def by auto
    then have "item_end new_i = item_end (fst (the ((snd p') new_i))) \<and> 
        item_origin (fst (the ((snd p') new_i))) = item_end (fst (the ((fst p') new_i)))" using p_simp' p_simp''
      by simp
    with bound_red' new_dom' have bound_red'':"(\<forall> x \<in> (dom (snd p')) . item_origin (fst 
      (the ((snd p') x))) = item_end (fst (the ((fst p') x))) \<and> 
    item_end x = item_end (fst (the ((snd p') x))))" by simp
    (*correct bounds reduction pointer*)
    
    with bound_pred'' have correct_bounds:"correct_bounds p'" apply(cases p') by auto
    (*correct match*)
    have pointer_unchanged:"\<forall> node . node \<noteq> new_i \<longrightarrow> (fst p) node = (fst p') node \<and> (snd p) node = (snd p') node" 
      using p_simp' p_simp'' by simp


    from assms(7) have "correct_red_pred_match p" by auto
    then have "(\<forall> node \<in> (dom (snd p)) . next_symbol (fst (the ((fst p) node)))
 = Some (item_nonterminal (fst (the ((snd p) node)))))" 
      by (metis correct_red_pred_match.simps prod.collapse)
    then have match:"(\<forall> node \<in> (dom (snd p)) . next_symbol (fst (the ((fst p') node)))
 = Some (item_nonterminal (fst (the ((snd p') node)))))" 
      using pointer_unchanged assms'' by metis
    from red_update have dom_snd:"dom (snd p') = dom (snd p) \<union> {new_i}" by simp
    from assms(8) have "next_symbol pred_i = Some (item_nonterminal red_i)" 
      using Completable_def item_nonterminal_def by metis
    then have "next_symbol (fst (the ((fst p') new_i)))
    = Some (item_nonterminal (fst (the ((snd p') new_i))))" using p_simp' p_simp'' by auto
    with match have "(\<forall> node \<in> (dom (snd p')) . next_symbol (fst (the ((fst p') node)))
 = Some (item_nonterminal (fst (the ((snd p') node)))))" using dom_snd by simp
    then have match':"correct_red_pred_match p'" 
      using assms' new_def p_simp by auto
    (*Correct lexing*) (*holds trivially*)
    from assms' have pointer_unchanged':
        "\<forall> node . node \<noteq> new_i \<longrightarrow> node \<notin> dom (snd p) \<longleftrightarrow>  node \<notin> (dom (snd p'))" 
          using p_simp' p_simp'' by auto
    from assms(7) have "(\<forall> x \<in> (dom (fst p)) . x \<notin> dom (snd p) \<longrightarrow>
    is_lexed (fst (the ((fst p) x))) x)" 
      by (metis correct_lexing.simps invariant_pointers'.simps surjective_pairing)
    with pointer_unchanged have "(\<forall> x \<in> (dom (fst p)) . x \<notin> dom (snd p) \<longrightarrow>
    is_lexed (fst (the ((fst p') x))) x)" using assms' pointer_unchanged' pointer_unchanged by metis
    then have prev_lex:"(\<forall> x \<in> (dom (fst p)) . x \<notin> dom (snd p') \<longrightarrow>
    is_lexed (fst (the ((fst p') x))) x)" using pointer_unchanged' assms' by metis
    have "new_i \<in> dom (fst p') \<and> new_i \<in> dom (snd p')" using p_simp' p_simp'' by simp
     with prev_lex have "(\<forall> x \<in> (dom (fst p')) . x \<notin> dom (snd p') \<longrightarrow>
    is_lexed (fst (the ((fst p') x))) x)" using new_dom by simp
     then have lexing:"correct_lexing p'" using correct_lexing.elims(3) by fastforce
    (*dom_sup_I*)
      from assms(9) have "{i . i\<in> I \<and> item_dot i >0} \<subseteq> dom (fst p)" 
       by (metis (no_types, lifting) Pair_inject dom_sup_items.elims(2) prod.collapse)
     then have dom_sub_I:"dom_sup_items p' I" using new_dom 
       by (metis (no_types, lifting) Pair_inject UnCI dom_sup_items.elims(3) prod.collapse subsetD subsetI)
    (*no red implies*)
     from assms(7) have "no_red_implies_terminal p" by simp
     then have "(\<forall> node \<in>  (dom (fst p)) . node \<notin> (dom (snd p)) 
    \<longrightarrow> (\<exists> t . next_symbol (fst (the ((fst p) node))) = Some t \<and> is_terminal t))" apply(cases p) by auto
     then have no_red:"(\<forall> node \<in>  (dom (fst p)) . node \<notin> (dom (snd p')) 
    \<longrightarrow> (\<exists> t . next_symbol (fst (the ((fst p') node))) = Some t \<and> is_terminal t))" 
       using pointer_unchanged' pointer_unchanged assms' by metis
     have "new_i \<notin> (dom (snd p')) \<longrightarrow>(\<exists> t . next_symbol (fst (the ((fst p') new_i))) = Some t \<and> is_terminal t)"
       using new_dom' by simp
     with no_red have no_red_implies_terminal:"no_red_implies_terminal p'" apply(cases p') using new_dom by simp

    (*final summary*)
     have "invariant_pointers' p'" using lexing match' correct_bounds pred_inc red_pred_dom no_red_implies_terminal 
       by (metis invariant_pointers'.elims(3) pred_increments.simps prod.collapse)
     with complete monotone in_set dom_sub_I have "measure_help_monotone p' \<and> red_complete p' 
      \<and> in_set  p' I \<and> invariant_pointers' p' \<and> dom_sup_items p' I \<and> valid_bounds I"
      using red_complete.elims(3) assms(10)
      by (metis (no_types, lifting) Un_iff fst_conv in_set.elims(3) prod.case_eq_if snd_conv)
  }
  then show ?thesis using 1 by blast
qed

lemma Complete_extend_help:"\<forall> (i, i') \<in> (Complete_extend k I) . is_complete i' \<and> i \<in> I \<and> i' \<in> I"
  using is_complete_def bin_def by auto

lemma Complete_extend_help':"\<forall> (i, i') \<in> (Complete_extend k I) . next_symbol i = Some (item_nonterminal i') \<and> item_end i = item_origin i'"
  using is_complete_def bin_def by auto

lemma Complete_extend_help'':"\<forall> (i, i') \<in> (Complete_extend k I) . \<not> (is_complete i)"
  using Complete_extend_help' next_symbol_not_complete by blast

lemma finite_Complete_extend:"finite I \<Longrightarrow> finite (Complete_extend k I)"
  using bin_def finite_subset [where ?A="Complete_extend k I" and ?B="I \<times> I"] finite_cartesian_product by auto
lemma Complete_pointers:
  assumes "Complete_pointers p (Complete_extend k I) = p'" 
      "measure_help_monotone p \<and> red_complete p \<and> in_set p I \<and> invariant_pointers' p \<and> dom_sup_items p I" "valid_bounds I"
      "finite I"
  shows "measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I \<and> invariant_pointers' p'"
proof -
  have fin_ext:"finite (Complete_extend k I)" using finite_Complete_extend assms(4) by blast (*added assumption to carry around*)
  have 0:"\<forall> (i, i') \<in> (Complete_extend k I) . is_complete i' \<and> i \<in> I \<and> i' \<in> I" using Complete_extend_help by blast
  obtain new where new_def:"new = csorted_list_of_set (Complete_extend k I)" by blast
  then have eq:"set new = Complete_extend k I" using fin_ext csorted_set_distinct'(1) (*type issue*)by blast
  then have 1:"\<forall> (i, i') \<in> (set new) . is_complete i' \<and> i \<in> I \<and> i' \<in> I" using 0  by simp    
  from new_def have 2:"\<forall> (i, i') \<in> (set new) . next_symbol i = Some (item_nonterminal i') \<and>                 
      item_end i = item_origin i'" using Complete_extend_help' eq by auto 

  (**)
  from assms new_def have "p' = foldl Complete_pointers_step   p new" by simp
  with 1 assms(2) 2 show ?thesis 
  proof (induct new arbitrary: p)
    case Nil
    then have "p = p'" by simp
  then show ?case using Nil by auto
  next
    case (Cons a new)
    from Cons(2) have 0:"fst a \<in> I " and 1:"snd a \<in> I " and 2:" is_complete (snd a)" by auto
    from Cons(3) have 3:"measure_help_monotone p \<and> red_complete p " and 4:" in_set p I" 
        and 5:"invariant_pointers' p" and 7:"dom_sup_items p I"by auto
    from Cons(4) have "next_symbol (fst a) = Some (fst(item_rule (snd a))) 
      \<and> item_end (fst a) = item_origin (snd a)" using item_nonterminal_def by force
    then have 6:"Completable (fst a) (snd a)" using Completable_def by blast
    obtain p'' where p'':"Complete_pointers_step  p (fst a, snd a) = p''" by blast
    then  have p''_invar:"measure_help_monotone p'' \<and> red_complete p'' \<and> in_set p'' I \<and> invariant_pointers' p''
    \<and> dom_sup_items p'' I" 
        using Complete_pointers_step [OF p'' 3 2 4 0 1 5 6 7 assms(3)] by simp
  
    from p'' Cons have "p' = foldl Complete_pointers_step   p'' new" by auto
    then  show ?case using Cons(1) p''_invar Cons by auto 
  qed
qed

(**)

lemma Complete'_Complete:"Complete' k (I, p) = (I', p') \<Longrightarrow> I' = I \<union> ((\<lambda> (i, i') . inc_item i k) ` Complete_extend k I)"
  by (auto simp add: Complete_def)

lemma Complete_extend_item_end_k:"\<forall> (i, i') \<in> Complete_extend k i . item_end i' = k" 
  by (auto simp add: bin_def)

lemma Complete_pointers_step_extends_domain:
  assumes "Complete_pointers_step  p (i, i') = p'"
  shows "dom (fst p') = dom (fst p) \<union> {(inc_item i (item_end i'))}"
proof -
  obtain i'' where i''_def:"i'' = (inc_item i (item_end i'))" by blast
  show ?thesis 
  proof (cases "i'' \<in> dom (fst p)")
    case True
    then have "p = p'" apply (cases p) using assms i''_def by simp
    with True have 1:"dom (fst p')  = dom (fst p)" apply(cases p) by simp
    from True have "dom (fst p)  = dom (fst p) \<union> {i''}" by blast
    then show ?thesis using 1 i''_def by simp 
  next
    case False
    then have "fst p' = (fst p)(i''\<mapsto> (i,  measure_help p i + measure_help p i' + 1))" 
        apply(cases p) using assms i''_def by fastforce
    then show ?thesis using i''_def by auto
  qed
qed

lemma Complete_pointers_extends_domain:
  assumes "Complete_pointers p (Complete_extend k I ) = p'" "finite I" 
  shows "dom (fst p') = dom (fst p) \<union> (\<lambda> (i, i'). inc_item i (item_end i')) `(Complete_extend k I )"
proof -
  have finite:"finite (Complete_extend k I)" using assms(2) using finite_Complete_extend by presburger
  obtain new where new_def:"new = csorted_list_of_set (Complete_extend k I )" by blast
  then have eq:"set new = Complete_extend k I " using finite using csorted_set' by presburger 
  from assms new_def have "p' = foldl Complete_pointers_step   p new" by simp
  then have "dom (fst p') = dom (fst p) \<union> (\<lambda>(i, i'). inc_item i (item_end i')) ` (set new)"
  proof (induction new arbitrary: p)
    case Nil
    then show ?case by simp
  next
    case (Cons a new)
    obtain p'' where step:"p'' = Complete_pointers_step p a" by blast
    then have 1:"dom (fst p'') = dom (fst p) \<union> {((\<lambda>(i, i'). inc_item i (item_end i')) a)}" 
      apply (cases p'') apply(cases a) using Complete_pointers_step_extends_domain by simp
    from Cons have "p' = foldl Complete_pointers_step p'' new" using step by simp
    then have "dom (fst p') = dom (fst p'') \<union> (\<lambda>(i, i'). inc_item i (item_end i')) ` (set new)" 
      using Cons by auto
    then show ?case using 1 by simp
  qed
  then show ?thesis using eq by simp
qed

lemma Complete'_dom_sup:
  assumes "Complete' k (I, p) = (I', p')" "dom_sup_items p I" "finite I"
  shows "dom_sup_items p' I'"
proof -
  obtain I'' where I''_def:"I'' = (\<lambda> (i, i'). inc_item i (item_end i' )) `(Complete_extend k I)" by simp
  then have I''_def':"I'' = (\<lambda> (i, i'). inc_item i k) `(Complete_extend k I)" using Complete_extend_item_end_k by fast 
  from assms(1) have I'_def:"I' =  I \<union> I''" using Complete'_Complete  I''_def' by blast (*needs additional proof corresponding to item_end i' = k*)
  from assms(1) have "Complete_pointers p (Complete_extend k I ) = p'" by simp
  then have 2:"dom (fst p') = dom (fst p) \<union> I''" apply (cases p) apply (cases p') 
    using I''_def Complete_pointers_extends_domain assms(3) by blast
  from assms(2) have 3:"{i . i\<in> I \<and> item_dot i >0} \<subseteq> dom (fst p)" apply(cases p) by simp
  have "{i . i\<in> I' \<and> item_dot i >0} \<subseteq> {i . i\<in> I \<and> item_dot i >0} \<union> I''" using I'_def by auto
  with 2 3 have "{i . i\<in> I' \<and> item_dot i >0} \<subseteq> dom (fst p')" by auto 
  then show ?thesis apply(cases p') by simp
qed

lemma Complete'_dom_no_scan:
  assumes "Complete' k (I, p) = (I', p')" "dom_no_scan p I" "finite I"
  shows "dom_no_scan p' I'"
proof - 
   obtain I'' where I''_def:"I'' = (\<lambda> (i, i'). inc_item i (item_end i' )) `(Complete_extend k I)" by simp
  then have I''_def':"I'' = (\<lambda> (i, i'). inc_item i k) `(Complete_extend k I)" using Complete_extend_item_end_k by fast 
  from assms(1) have I'_def:"I' =  I \<union> I''" using Complete'_Complete  I''_def' by blast (*needs additional proof corresponding to item_end i' = k*)
  from assms(1) have "Complete_pointers p (Complete_extend k I ) = p'" by simp
  then have 2:"dom (fst p') = dom (fst p) \<union> I''" apply (cases p) apply (cases p') 
    using I''_def Complete_pointers_extends_domain assms(3) by blast
  then have new:"\<forall> i \<in> I'' . i \<in> dom (fst p')" by simp
  from assms(2) have "\<forall> i \<in> I . i \<notin> dom (fst p) \<longrightarrow> item_origin i = item_end i" apply(cases p) by simp
  with 2 have "\<forall> i \<in> I . i \<notin> dom (fst p') \<longrightarrow> item_origin i = item_end i" by simp
  with new I'_def have "\<forall> i \<in> I' . i \<notin> dom (fst p') \<longrightarrow> item_origin i = item_end i" by blast
  then show ?thesis apply(cases p') by simp
qed


lemma Complete'_pointers:"Complete' k (I, p) = (I', p') \<Longrightarrow> 
    measure_help_monotone p \<and> red_complete p \<and> in_set p I \<and> invariant_pointers' p \<and> dom_sup_items p I \<and> dom_no_scan p I \<and> valid_bounds I \<and> finite I\<Longrightarrow>
    measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I \<and> invariant_pointers' p' \<and> dom_sup_items p' I' \<and> dom_no_scan p' I' \<and> valid_bounds I'"
  using Complete_pointers Complete'_dom_sup Complete'_dom_no_scan 
    Complete'_bounds
  by (metis Complete'.simps Pair_inject)


(*also for all predecessor pointers*)

lemma Complete_eq:"fst (Complete' k  I)  = Complete k (fst I)"
  using Complete_def 
  by (smt (verit, ccfv_SIG) Complete'.elims fst_conv)
(*need list conversion*)


section "Proof over scan pointers for reconstruction
      - assumptions about the relation to the Doc String are added here specifically"

fun Scan_pointers_step::" ('a, 'b) sppf_pointers \<Rightarrow> ('a::ccompare, 'b::ccompare) item \<times> 'c::ccompare list 
 \<Rightarrow> ('a, 'b) sppf_pointers" where
"Scan_pointers_step (pred, red) (i, token) =  (if ((inc_item i (item_end i + length token)) \<notin> (dom pred))
   then (pred((inc_item i (item_end i + length token))\<mapsto> (i,  measure_help (pred, red) i + 1)), red ) else (pred, red) )"

fun Scan_pointers::"('a, 'b) sppf_pointers \<Rightarrow> (('a::ccompare, 'b::ccompare) item \<times> 'c::ccompare list) set \<Rightarrow> ('a, 'b) sppf_pointers" where
"Scan_pointers p I = foldl Scan_pointers_step p (csorted_list_of_set I)  " (*add precedence pointers*)

(*have to prove that measure does not change for all others*)

fun Scan_extend::"nat \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> (('a, 'b) item \<times> ('c) list) set" where
"Scan_extend k I T= {(x, c) | x  t c. x \<in> bin I k \<and> (t, c) \<in> T \<and>
       next_symbol x = Some t}"


lemma Scan_pointers_step_invar:
  assumes "Scan_pointers_step  p (i, c) = p'"
        "measure_help_monotone p \<and> red_complete p"  
        "in_set p I" "i \<in> I" "invariant_pointers' p" "dom_sup_items p I" "length c \<in> (Lex (item_rhs i! item_dot i) Doc (item_end i))"
        "\<exists> t . next_symbol i = Some t \<and> is_terminal t" "length c > 0"
      shows "measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I \<and> invariant_pointers' p' 
            \<and> dom_sup_items p' I"
proof -
  obtain new where new_def:"new = (inc_item i (item_end i + length c))" by blast
  have new_val:"item_dot new = Suc (item_dot i) \<and> item_rule new = item_rule i \<and>
        item_end new = (item_end i + length c) \<and> item_origin new = item_origin i" 
    using new_def by auto (*hold by increment*)
 
  {
    assume assms':"new \<notin> dom (fst p)"
    with assms new_def have step:"p' = ((fst p)(new\<mapsto> (i,   measure_help p i + 1)), snd p )" 
      by (metis Scan_pointers_step.simps prod.collapse)
    (*equality of red*)
    then have eq:"ran (snd p') = ran (snd p)" by auto
    from assms(2) have "\<forall> (i, k ) \<in> (ran (snd p)) . is_complete i"  
      by (metis red_complete.simps snd_conv surj_pair)
    then have 1:"red_complete p'" using eq
      using local.step red_complete.simps by presburger
  
    have "\<forall> (i, k ) \<in> (ran (snd p)) .  i \<in> I" 
      by (metis Un_iff assms(3) in_set.elims(2) snd_conv)
    with eq have inSet:"\<forall> (i, k ) \<in> (ran (snd p')) .  i \<in> I" by auto

    have new_dom:"dom (fst p') = dom (fst p) \<union> {new}" using step by simp
    (*measure*)
    (*original statement*)
   from assms(2) have prem_mon:"(\<forall> i \<in> (dom (fst p)) . (measure_help p i) > (measure_help p 
  (fst (the ((fst p) i)))))"by (metis measure_help_monotone.simps prod.collapse)
   from step have map_unchanged:"\<forall> i . new \<noteq> i \<longrightarrow> (fst p') i = (fst p) i" by auto
   from new_val have "item_dot new > 0" by simp
   with assms(6) assms'  have new_not_in_I:"new \<notin> I" apply(cases p) by auto  (*this will used to prove that the mapped to can't change*)
   with assms(3) have "new \<notin> fst ` (ran (fst p) \<union> ran (snd p))" apply(cases p) by auto 
    (*prove measure not changing*)
   from map_unchanged assms' have  fst_unchanged:"\<forall> i \<in> dom (fst p) . (fst p') i = (fst p) i" by auto
    have measure_invar:"\<forall> i \<in> dom (fst p) . measure_help p' i = measure_help p i"
      using map_unchanged  surjective_pairing assms' 
      by (metis UnI1 measure_help.simps new_dom) 
    (*prove mapped to not changing*)
    have "\<forall> i \<in> dom (fst p) . (the ((fst p) i)) \<in> ran (fst p)" by (auto simp add: ran_def)
    with assms(3) have "\<forall> i \<in> dom (fst p) . fst (the ((fst p) i)) \<in> I" apply(cases p) by force
    with new_not_in_I have "\<forall> i \<in> dom (fst p) . fst (the ((fst p) i)) \<noteq> new" by blast
    then have measure_invar':"\<forall> i \<in> dom (fst p) . measure_help p' (fst (the ((fst p) i))) = 
        measure_help p (fst (the ((fst p) i)))"
      using map_unchanged by (metis Un_empty_right Un_insert_right insertE measure_help.simps 
              measure_invar new_dom prod.collapse)(*need a few others to*)
    then have "\<forall> i \<in> dom (fst p) . measure_help p' (fst (the ((fst p') i))) = measure_help p (fst (the ((fst p) i)))"
      using fst_unchanged by auto
    with prem_mon measure_invar have fst_p'_mon:"(\<forall> i \<in> (dom (fst p)) . (measure_help p' i) > (measure_help p' 
  (fst (the ((fst p') i)))))" by simp
    (*new_item added*)
    have neq_pred:"new \<noteq> i" using new_def using assms(4)  new_not_in_I by blast
    from new_dom have "measure_help p' new = snd (the ((fst p') new))"
      by (metis Un_iff insertCI measure_help.simps prod.collapse) 
    with step have "measure_help p' new = (measure_help p i) + 1" by simp
    with map_unchanged neq_pred have new_i_meas:"measure_help p' new = (measure_help p' i) + 1" 
      by (metis (mono_tags, lifting) domD domI measure_help.simps prod.collapse) 
    then have "measure_help p' new > measure_help p' (fst (the ((fst p') new)))" using step  by auto
    with fst_p'_mon new_dom have measure_monotone:"(\<forall> i \<in> (dom (fst p')) . (measure_help p' i) > (measure_help p' 
  (fst (the ((fst p') i)))))" by simp
    (*measure red*)
    (*premise*) 
    (*\<notin> snd p*)
    from assms have "red_implies_pred_dom p" by simp
    then  have dom1:"dom (snd p) \<subseteq> dom (fst p)"
      by (metis red_implies_pred_dom.simps surjective_pairing)
    have assms'':"new \<notin> (dom (snd p))" using assms' using dom1 by blast

    from assms(2) have prem_mon':"(\<forall> i \<in> (dom (snd p)) . (measure_help p i) > (measure_help p 
  (fst (the ((snd p) i)))))" by (metis measure_help_monotone.simps prod.collapse)
    from step have map_unchanged':"\<forall> i . new \<noteq> i \<longrightarrow> (snd p') i = (snd p) i" by auto
    from map_unchanged' assms'' have  snd_unchanged:"\<forall> i \<in> dom (snd p) . (snd p') i = (snd p) i" by auto
    have measure_invar:"\<forall> i \<in> dom (snd p) . measure_help p' i = measure_help p i"
      using map_unchanged'  surjective_pairing assms'' 
      by (metis gr_implies_not0 measure_help.simps measure_invar prem_mon') 
    from dom1 have dom1':"\<forall> i \<in> dom (snd p) . i\<in> dom (fst p)" by blast
    from assms(3) have inset:"(\<forall> (i', k) \<in> (ran (fst p) \<union> ran (snd p)). (i' \<in> I))" apply(cases p) by auto
    then have "\<forall> i \<in> dom (snd p) . the ((snd p) i) \<in> ran (snd p)" by (auto simp add: ran_def)
    with inset  have "\<forall> i \<in> dom (snd p) . fst (the ((snd p) i)) \<in> I" apply (cases "(the ((snd p) i))") by force
    with new_not_in_I have map_neq_new:"\<forall> i \<in> dom (snd p) . fst (the ((snd p) i)) \<noteq> new" by blast
    then have map_same:"\<forall> i \<in> dom (snd p) . (fst p') (fst (the ((snd p) i))) = (fst p) (fst (the ((snd p) i)))" 
      using map_unchanged by metis
    from map_neq_new have map_dom':
        "\<forall> i \<in> dom (snd p) . fst (the ((snd p) i)) \<in> dom (fst p) \<longleftrightarrow> 
      fst (the ((snd p) i)) \<in> dom (fst p')" using step by simp
    then have measure_invar':"\<forall> i \<in> dom (snd p) . measure_help p' (fst (the ((snd p) i))) 
          = measure_help p (fst (the ((snd p) i)))" by (metis measure_help.simps prod.collapse map_same )
    then have "\<forall> i \<in> dom (snd p) . measure_help p' (fst (the ((snd p') i))) = measure_help p (fst (the ((snd p) i)))"
      using snd_unchanged by auto
    with prem_mon' measure_invar step have snd_p'_mon:"(\<forall> i \<in> (dom (snd p')) . (measure_help p' i) > (measure_help p' 
  (fst (the ((snd p') i)))))" by simp  
    with measure_monotone have monotone_p':"measure_help_monotone p'"
      using local.step by auto
    (*in set*)
    from step have sub:"ran (fst p') \<subseteq> ran (fst p) \<union> {(i,   measure_help p i + 1)}" apply (cases p') 
        by (auto simp add: ran_def)
    from assms(3) have 2:"\<forall> (i, k ) \<in> (ran (fst p)) . i \<in> I" 
      by (metis UnCI fst_conv in_set.elims(2))
    with sub have "\<forall> (i', k ) \<in> (ran (fst p')) . i' \<in>  fst ` ran (fst p) \<or> i' = i" by force
    then have "\<forall> (i', k ) \<in> (ran (fst p')) . i' \<in> I" using 2 assms by fastforce
    with inSet have inset:"in_set p' I" 
      by (metis (no_types, lifting) Un_iff fst_conv in_set.elims(3) snd_eqD)
    (*helpers*)
    from step  assms' new_def have red_update:"snd p' = (snd p)" by simp
    from step have pred_update:"fst p' = (fst p)(new \<mapsto> (i, measure_help p i + 1))" by simp
    then have new_dom:"dom (fst p') = dom (fst p) \<union> {new}" by auto
    (*invariant_pointers'*)
    (*domain*)
    from assms(5) have dom1:"dom (snd p) \<subseteq> dom (fst p)" apply(cases p) by (auto simp add: dom_def) 
    from red_update have "dom (snd p') = dom (snd p)" by simp
    with new_dom dom1 have "dom (snd p') \<subseteq> dom (fst p')"  by auto
    then have red_pred_dom:"red_implies_pred_dom p'" 
      by (metis prod.collapse red_implies_pred_dom.simps)
    from step have pointers_unchanged:"\<forall> node . node \<noteq> new \<longrightarrow> (fst p) node = (fst p') node" by simp
    from dom1 assms' have assms'':"new \<notin> dom (snd p)" by blast
    (*pred_increment*)
    from assms(5) have inc0:"pred_increments p" by auto
    then have inc1:"(\<forall> node \<in>  (dom (fst p)) . item_dot node = (Suc (item_dot (fst (the ((fst p) node)))))
  \<and> item_rule node = item_rule (fst (the ((fst p) node))))" 
      by (metis pred_increments.simps prod.collapse)
    then have inc2:"(\<forall> node \<in>  (dom (fst p)) . item_dot node = (Suc (item_dot (fst (the ((fst p') node)))))
  \<and> item_rule node = item_rule (fst (the ((fst p') node))))" using pointers_unchanged assms' by metis(*because no change*)
    from pred_update new_val have "item_dot new = (Suc (item_dot (fst (the ((fst p') new)))))
  \<and> item_rule new = item_rule (fst (the ((fst p') new)))" by simp
    then have "(\<forall> node \<in>  {new} . item_dot node = (Suc (item_dot (fst (the ((fst p') node)))))
  \<and> item_rule node = item_rule (fst (the ((fst p') node))))" by simp
    with inc2 have pred_inc:"(\<forall> node \<in>  (dom (fst p')) . item_dot node = (Suc (item_dot (fst (the ((fst p') node)))))
  \<and> item_rule node = item_rule (fst (the ((fst p') node))))" using new_dom by blast
    then have pred_increments:"pred_increments p'" 
      using pred_increments.elims(3) by fastforce
    (*correct_bounds*)
    from assms(5) have bound:"correct_bounds p" by simp
    then  have bound_pred:"(\<forall> x \<in> (dom (fst p)) . item_origin x = item_origin (fst (the ((fst p) x))) 
  \<and> item_end x \<ge> item_end (fst (the ((fst p) x))))" and 
      bound_red:"(\<forall> x \<in> (dom (snd p)) . item_origin (fst (the ((snd p) x))) = item_end (fst (the ((fst p) x))) \<and> 
    item_end x = item_end (fst (the ((snd p) x))))" 
      apply (metis correct_bounds.simps prod.collapse) using bound 
      by (metis (no_types, lifting) correct_bounds.simps dom1 in_mono surjective_pairing)
    then have bound_pred':"(\<forall> x \<in> (dom (fst p)) . item_origin x = item_origin (fst (the ((fst p') x))) 
  \<and> item_end x \<ge> item_end (fst (the ((fst p') x))))" and 
      bound_red':"(\<forall> x \<in> (dom (snd p)) . item_origin (fst (the ((snd p') x))) = item_end (fst (the ((fst p') x))) \<and> 
    item_end x = item_end (fst (the ((snd p') x))))" using pointers_unchanged assms' 
       apply metis using bound_red red_update assms''
      using pointers_unchanged by auto (*map stays for non updated*)

    (**)
    from assms(9) have "length c >0" by blast 
    with new_val pred_update have "item_origin new = item_origin (fst (the ((fst p') new))) \<and> item_end new \<ge>
      item_end (fst (the ((fst p') new)))" by simp (*do we need strict inequality*)   
    with bound_pred' new_dom have bounds_pred':"(\<forall> x \<in> (dom (fst p')) . item_origin x = item_origin (fst (the ((fst p') x))) 
  \<and> item_end x \<ge> item_end (fst (the ((fst p') x))))" by auto
    with bound_red' red_update have correct_bounds:"correct_bounds p'"  using correct_bounds.elims(3) 
      by fastforce
    (*correct match*)
    from assms(5) have "correct_red_pred_match p" by simp
    then have "(\<forall> node \<in> (dom (snd p)) . next_symbol (fst (the ((fst p) node)))
 = Some (item_nonterminal (fst (the ((snd p) node)))))" by (metis correct_red_pred_match.simps prod.collapse)
    with pointers_unchanged assms'' red_update have match:"correct_red_pred_match p'" 
      by (metis correct_red_pred_match.elims(3) fst_conv snd_conv)
    (*correct lexing*)
    from assms(5) have "correct_lexing p" by simp
    then have "(\<forall> x \<in> (dom (fst p)) . x \<notin> dom (snd p) \<longrightarrow>
    is_lexed (fst (the ((fst p) x))) x)" by (metis correct_lexing.simps surjective_pairing)
    then have correct_lexing:"(\<forall> x \<in> (dom (fst p)) . x \<notin> dom (snd p') \<longrightarrow>
    is_lexed (fst (the ((fst p') x))) x)" using pointers_unchanged assms' red_update by metis
    have prem:"new \<notin> dom (snd p')" using assms'' red_update by auto

    from assms(7) have "is_lexed i new" using new_def by (simp add: is_lexed_def) 
    
    then have "new \<notin> dom (snd p') \<longrightarrow> is_lexed i new" by simp
    with correct_lexing new_dom have "(\<forall> x \<in> (dom (fst p')) . x \<notin> dom (snd p') \<longrightarrow>
    is_lexed (fst (the ((fst p') x))) x)" using pred_update by simp
    then have correct_lexing':"correct_lexing p'"
      using correct_lexing.elims(3) by fastforce
    (*dom_sup_items*)
    from assms(6) have "{i . i\<in> I \<and> item_dot i >0} \<subseteq> dom (fst p)" apply (cases p) by auto
    with new_dom have "{i . i\<in> I \<and> item_dot i >0} \<subseteq> dom (fst p')" by auto
    then have dom_sup:"dom_sup_items p' I" apply(cases p') by auto
    (*no red implies terminal*)
    from assms(5) have "(\<forall> node \<in>  (dom (fst p)) . node \<notin> (dom (snd p)) 
    \<longrightarrow> (\<exists> t . next_symbol (fst (the ((fst p) node))) = Some t \<and> is_terminal t))" apply(cases p) by auto
    with pointers_unchanged assms' red_update have no_red:"(\<forall> node \<in>  (dom (fst p)) . node \<notin> (dom (snd p')) 
    \<longrightarrow> (\<exists> t . next_symbol (fst (the ((fst p') node))) = Some t \<and> is_terminal t))" by metis
    from step assms(8) have "(\<exists> t . next_symbol (fst (the ((fst p') new))) = Some t \<and> is_terminal t)" by simp
    with prem have "new \<notin> dom (snd p') \<longrightarrow> (\<exists> t . next_symbol (fst (the ((fst p') new))) = Some t \<and> is_terminal t)"
      by blast
    with no_red new_dom have no_red_implies_terminal:"no_red_implies_terminal p'" apply(cases p') by auto
    (*summary*)
    have "invariant_pointers' p'" using match pred_increments correct_bounds correct_lexing' red_pred_dom 
       no_red_implies_terminal by simp
    with  monotone_p' 1 inset dom_sup have "measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I 
      \<and> invariant_pointers' p' \<and> dom_sup_items p' I" by blast
  }
  then have case1:"new \<notin> dom (fst p) \<Longrightarrow> measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I
    \<and> invariant_pointers' p' \<and> dom_sup_items p' I" by blast
  {
    assume "new \<in> dom (fst p)"
    with assms new_def have step:"p' = p" 
      by (metis Scan_pointers_step.simps prod.collapse)
    then have "measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I \<and> invariant_pointers' p' 
    \<and> dom_sup_items p' I" using assms by blast
  }
  with case1 show ?thesis by blast
qed
(*add all the terminal statements there too*)
fun Scan' :: "('a, 'b,'c) token set \<Rightarrow> nat \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow> ('a, 'b) sppf_items"
where
  "Scan' T k (I, p) = (Scan T k I, Scan_pointers p (Scan_extend k I T))"

lemma Scan'_finite:"finite I \<and> finite T \<Longrightarrow> Scan' T k (I, p) = (I', p') \<Longrightarrow> finite I'"
  by (auto simp add: Scan_Finite)

lemma Scan'_bounds:"valid_bounds I \<Longrightarrow> Scan' T k (I, p) = (I', p') \<Longrightarrow> valid_bounds I'"
  by (auto simp add: Scan_bounds)

lemma Scan'_rule:"valid_rule I \<Longrightarrow>  Scan' T k (I, p) = (I', p') \<Longrightarrow> valid_rule I'"
  by (auto simp add: Scan_rule)

definition Tokens_lexed::"nat \<Rightarrow> ('a, 'b', 'c) token set \<Rightarrow> bool" where
"Tokens_lexed k T = (\<forall> (t, c) \<in> T . drop k (take (length c) Doc) = c)"

lemma Scan_extend_help: (*add statement about everything being lexed*)
  assumes "Tokens_lexed k T " 
  shows " \<forall> (i, c) \<in> (Scan_extend k I T) .   i \<in> I \<and> drop k (take (length c) Doc) = c"
proof -
  have 1:"\<forall> (i, c) \<in> (Scan_extend k I T) . i \<in> I \<and> (\<exists> t . (t, c) \<in> T)" using bin_def by auto+
  then show ?thesis 
    using Tokens_lexed_def assms by fastforce
qed

lemma Scan_extend_help':"\<forall> (i, c) \<in> (Scan_extend k I T) .   i \<in> I"
  using bin_def by auto

lemma Scan_extend_top:"Scan_extend k I T \<subseteq> (\<lambda> (i, (t,c)) . (i, c)) `( I \<times>  T)"
proof - 
  have 1:"Scan_extend k I T \<subseteq> {(x, c)| x t c.  x \<in> I  \<and> (t, c) \<in> T }" using bin_def by fastforce
  have 2:"\<forall> (i ,c) \<in> {(x, c)| x t c.  x \<in> I  \<and> (t, c) \<in> T } . (\<exists> t . (i, (t, c)) \<in> I \<times> T)" by blast
  with 1 have "Scan_extend k I T \<subseteq> (\<lambda> (i, (t, c)) . (i, c)) ` (I \<times> T)" by force
  then show ?thesis by blast
qed

lemma Scan_extend_finite:
  assumes "finite T " "finite I " 
  shows "finite (Scan_extend k I T)" 
proof -
  have "finite ((\<lambda> (i, (t,c)) . (i, c)) `( I \<times>  T))" using assms finite_cartesian_product by blast
  then show ?thesis using Scan_extend_top finite_subset by metis
qed

lemma Scan_extend_lexes:
  assumes "\<forall> (t, c) \<in> T . (length c) \<in> (Lex t Doc k)"
  shows "\<forall> (i, c) \<in> (Scan_extend k I T) . (length c) \<in> (Lex (item_rhs i ! item_dot i) Doc (item_end i))"
proof -
  have 1:"\<forall> (i, c) \<in> (Scan_extend k I T) . item_end i = k" by (auto simp add: bin_def)
  have 2:"\<forall> (i, c) \<in> (Scan_extend k I T) .  (\<exists> t . (t, c) \<in> T \<and> Some t = next_symbol i)" by auto
  then have "\<forall> (i, c) \<in> (Scan_extend k I T) . (\<exists> t . (t, c) \<in> T \<and> Some t = next_symbol i \<and>  
      (length c) \<in> (Lex t Doc k))" using assms by blast
  then have "\<forall> (i, c) \<in> (Scan_extend k I T) . (\<exists> t . (t, c) \<in> T \<and>   Some t = Some (item_rhs i ! item_dot i) \<and>  
      (length c) \<in> (Lex t Doc k))" using next_symbol_def 
    by (smt (z3) case_prodD case_prodI2 option.discI)
  then have "\<forall> (i, c) \<in> (Scan_extend k I T) . (\<exists> t . (t, c) \<in> T \<and>
      (length c) \<in> (Lex (item_rhs i ! item_dot i) Doc k))" by blast
  then have "\<forall> (i, c) \<in> (Scan_extend k I T) .   
      (length c) \<in> (Lex (item_rhs i ! item_dot i) Doc k)" by fastforce
  with 1 show ?thesis by fast
qed

lemma Scan_extend_next_terminal: "\<forall> (t, c) \<in> T . is_terminal t \<Longrightarrow> \<forall> (i, c) \<in> (Scan_extend k I T) .
   (\<exists> t. is_terminal t \<and> next_symbol i = Some t )"
  by auto

lemma Scan_extend_nonempty:"\<forall> (t, c) \<in> T . length c > 0 \<Longrightarrow> \<forall> (i, c) \<in> (Scan_extend k I T) 
  . length c > 0" by auto

lemma Scan_pointers:
  assumes "Scan_pointers p (Scan_extend k I T) = p'" 
          "measure_help_monotone p \<and> red_complete p \<and> in_set p I \<and> invariant_pointers' p \<and> dom_sup_items p I"
          "finite T" "finite I" "\<forall> (t, c) \<in> T . (length c) \<in> (Lex t Doc k)" "\<forall> (t, c) \<in> T . is_terminal t" 
          "\<forall> (t, c) \<in> T . length c > 0"
  shows "measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I \<and> invariant_pointers' p'"
proof -
  obtain new where new_def:"new = csorted_list_of_set (Scan_extend k I T)" by blast
  then have 1:"\<forall> (i, c) \<in> (set new) .  i \<in> I"  by (metis Scan_extend_help' csorted_set Scan_extend_finite assms(3) assms(4))
  from new_def have lexes:"\<forall> (i, c) \<in> (set new) . (length c) \<in> (Lex (item_rhs i ! item_dot i) Doc (item_end i))" 
    using Scan_extend_finite Scan_extend_lexes assms(3) assms(4) assms(5) csorted_set by presburger
  from new_def have is_terminal:"\<forall> (i, c) \<in> (set new) . (\<exists> t . is_terminal t \<and> next_symbol i = Some t)"
    using Scan_extend_finite Scan_extend_next_terminal assms csorted_set by presburger
  from new_def have non_empty_tokens:"\<forall> (i, c) \<in> (set new) . length c > 0"
    using Scan_extend_finite Scan_extend_nonempty assms csorted_set by presburger
  from assms new_def have "p' = foldl Scan_pointers_step   p new" by simp
  with assms(2) 1 lexes is_terminal non_empty_tokens 
    show ?thesis 
  proof (induction new arbitrary: p)
    case Nil
    then have "p' = p" by simp
    then show ?case using Nil by simp
  next
    case (Cons a new)
    from Cons(2) have 1:"measure_help_monotone p \<and> red_complete p" and 2:"in_set p I" by auto
    from Cons(3) have 3:"fst a \<in> I" by auto
    from Cons(2) have 4:"invariant_pointers' p" by blast
    from Cons(2) have 5:"dom_sup_items p I" by blast
    from Cons(4) have 6:"length (snd a) \<in> Lex (item_rhs (fst a) ! item_dot (fst a)) Doc (item_end (fst a))" by auto
    from Cons(5) have 7:"\<exists> t .  next_symbol (fst a ) = Some t \<and> is_terminal t" by auto
    from Cons(6) have 8:"length (snd a)  > 0" by force
    obtain p'' where p'':"Scan_pointers_step p (fst a, snd a) = p''" by blast
    then  have p''_invar:"measure_help_monotone p'' \<and> red_complete p'' \<and> in_set p'' I 
        \<and> invariant_pointers' p'' \<and> dom_sup_items p'' I" using 
         Scan_pointers_step_invar [OF p'' 1 2 3 4 5 6 7 8]  by simp
    from p'' Cons have "p' = foldl Scan_pointers_step  p'' new" by auto
    then show ?case using Cons p''_invar by simp 
  qed
qed

lemma in_set_trans:
  assumes "in_set p I " " I \<subseteq> I' "
  shows " in_set p I'"
proof -
  from assms have "(\<forall> (i', k) \<in> (ran (fst p) \<union> ran (snd p)). (i' \<in> I))"
    by (metis (no_types, lifting) case_prod_beta' in_set.simps inf_sup_aci(5) prod.collapse)
  with assms(2) show ?thesis
    by (metis (mono_tags, lifting) assms(1) case_prod_beta' in_set.elims(3) in_set.simps subset_iff)
qed

lemma Scan_sub:"Scan k T I = I' \<Longrightarrow> I \<subseteq> I'"
  by (auto simp add: Scan_def)
lemma Scan'_sub:"Scan' k T (I,  p)  = (I', p') \<Longrightarrow> I \<subseteq> I'" 
  using Scan_sub by auto

lemma Scan_pointers_step_extends_domain:
  assumes "Scan_pointers_step  p (i, c) = p'"
  shows "dom (fst p') = dom (fst p) \<union> {(inc_item i (item_end i + length c))}"
proof -
  obtain i' where i'_def:"i' = (inc_item i (item_end i + length c))" by blast
  show ?thesis 
  proof (cases "i' \<in> dom (fst p)")
    case True
    then have "p = p'" apply (cases p) using assms i'_def by simp
    with True have 1:"dom (fst p')  = dom (fst p)" apply(cases p) by simp
    from True have "dom (fst p)  = dom (fst p) \<union> {i'}" by blast
    then show ?thesis using 1 i'_def by simp 
  next
    case False
    then have "fst p' = (fst p)(i'\<mapsto> (i,  measure_help p i + 1))" 
        apply(cases p) using assms i'_def by fastforce
    then show ?thesis using i'_def by auto
  qed
qed

lemma Scan_pointers_extends_domain:
  assumes "Scan_pointers p (Scan_extend k I T) = p'" "finite I" "finite T"
  shows "dom (fst p') = dom (fst p) \<union> (\<lambda> (i,c ). inc_item i (item_end i + length c)) `(Scan_extend k I T)"
proof -
  obtain new where new_def:"new = csorted_list_of_set (Scan_extend k I T)" by blast
  then have eq:"set new = Scan_extend k I T" using csorted_set Scan_extend_finite assms by auto 
  from assms new_def have "p' = foldl Scan_pointers_step   p new" by simp
  then have "dom (fst p') = dom (fst p) \<union> (\<lambda>(i, c). inc_item i (item_end i + length c)) ` (set new)"
  proof (induction new arbitrary: p)
    case Nil
    then show ?case by simp
  next
    case (Cons a new)
    obtain p'' where step:"p'' = Scan_pointers_step p a" by blast
    then have 1:"dom (fst p'') = dom (fst p) \<union> {((\<lambda>(i, c). inc_item i (item_end i + length c)) a)}" 
      apply (cases p'') apply(cases a) using Scan_pointers_step_extends_domain by simp
    from Cons have "p' = foldl Scan_pointers_step p'' new" using step by simp
    then have "dom (fst p') = dom (fst p'') \<union> (\<lambda>(i, c). inc_item i (item_end i + length c)) ` (set new)" 
      using Cons by auto
    then show ?case using 1 by simp
  qed
  then show ?thesis using eq by simp
qed

lemma Scan_extend_eq_Scan_add:"(\<lambda> (i,c ). inc_item i (item_end i + length c)) `(Scan_extend k I T) 
  = { inc_item x (k + length c) | x t c. x \<in> bin I k \<and> (t, c) \<in> T \<and>
       next_symbol x = Some t }"
proof -
  have 1:"{inc_item x (k + length c) | x t c. x \<in> bin I k \<and> (t, c) \<in> T \<and>
       next_symbol x = Some t } = (\<lambda> (i,c ). inc_item i (k + length c)) `(Scan_extend k I T)" by auto
  have "\<forall> (i, c )\<in> Scan_extend k I T . item_end i = k" using bin_def by auto 
  then have "(\<lambda> (i,c ). inc_item i (item_end i + length c)) `(Scan_extend k I T) = 
    (\<lambda> (i,c ). inc_item i (k + length c)) `(Scan_extend k I T)" by fast
  with 1 show ?thesis by simp
qed
lemma Scan_dom_sup:
  assumes "Scan'  T k (I,  p)  = (I', p')" "dom_sup_items p I" "finite I" "finite T"
  shows "dom_sup_items p' I'"
proof -
  obtain I'' where I''_def:"I'' = (\<lambda> (i,c ). inc_item i (item_end i + length c)) `(Scan_extend k I T)" by simp
  from assms(1) have 1:"Scan T k I = I'" by simp
  then have I'_def:"I' =  I \<union> I''" using Scan_def I''_def Scan_extend_eq_Scan_add by simp
  from assms(1) have "Scan_pointers p (Scan_extend k I T) = p'" by simp
  then have 2:"dom (fst p') = dom (fst p) \<union> I''" apply (cases p) apply (cases p') 
    using I''_def Scan_pointers_extends_domain assms by meson
  from assms(2) have 3:"{i . i\<in> I \<and> item_dot i >0} \<subseteq> dom (fst p)" apply(cases p) by simp
  have "{i . i\<in> I' \<and> item_dot i >0} \<subseteq> {i . i\<in> I \<and> item_dot i >0} \<union> I''" using I'_def by auto
  with 2 3 have "{i . i\<in> I' \<and> item_dot i >0} \<subseteq> dom (fst p')" by auto 
  then show ?thesis apply(cases p') by simp
qed


lemma Scan'_dom_no_scan:
  assumes "Scan' T k (I, p) = (I', p')" "dom_no_scan p I" "finite I" "finite T" 
  shows "dom_no_scan p' I'"
proof - 
  obtain I'' where I''_def:"I'' = (\<lambda> (i,c ). inc_item i (item_end i + length c)) `(Scan_extend k I T)" by simp
  from assms(1) have 1:"Scan T k I = I'" by simp
  then have I'_def:"I' =  I \<union> I''" using Scan_def I''_def 
    using Scan_extend_eq_Scan_add by auto
  from assms(1) have "Scan_pointers p (Scan_extend k I T) = p'" by simp
  then have 2:"dom (fst p') = dom (fst p) \<union> I''" apply (cases p) apply (cases p') 
    using I''_def Scan_pointers_extends_domain assms by meson
  then have new:"\<forall> i \<in> I'' . i \<in> dom (fst p')" by simp
  from assms(2) have "\<forall> i \<in> I . i \<notin> dom (fst p) \<longrightarrow> item_origin i = item_end i" apply(cases p) by simp
  with 2 have "\<forall> i \<in> I . i \<notin> dom (fst p') \<longrightarrow> item_origin i = item_end i" by simp
  with new I'_def have "\<forall> i \<in> I' . i \<notin> dom (fst p') \<longrightarrow> item_origin i = item_end i" by blast
  then show ?thesis apply(cases p') by simp
qed


lemma Scan'_pointers:"finite I \<and> finite T \<Longrightarrow> \<forall>(t, c)\<in>T. length c \<in> Lex t Doc k \<Longrightarrow> 
  \<forall>(t, c)\<in>T. is_terminal t \<Longrightarrow>  \<forall>(t, c)\<in>T. length c > 0 \<Longrightarrow>
  Scan'  T k (I,  p)  = (I', p') \<Longrightarrow> measure_help_monotone p \<and> red_complete p \<and> in_set p I 
    \<and> invariant_pointers' p \<and> dom_sup_items p I \<and> dom_no_scan p I \<Longrightarrow>
  measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I \<and> invariant_pointers' p' \<and> 
  dom_sup_items p' I' \<and> dom_no_scan p' I'"
  using Scan_pointers[where ?T = "T" and ?I = "I" and ?k="k" and ?p="p" and ?p'="p'"]
    Scan_dom_sup [where ?T = "T" and ?I = "I" and ?k="k" and ?p="p" and ?p'="p'"] 
    Scan'_dom_no_scan [where ?T = "T" and ?I = "I" and ?k="k" and ?p="p" and ?p'="p'"] by simp

lemma Scan'_pointers':
  assumes "Scan'  T k (I,  p)  = (I', p') " "finite I \<and> finite T" "\<forall>(t, c)\<in>T. length c \<in> Lex t Doc k"
          "\<forall>(t, c)\<in>T. is_terminal t" "\<forall>(t, c)\<in>T. length c > 0"
          "measure_help_monotone p \<and> red_complete p \<and> in_set p I \<and> invariant_pointers' p \<and> dom_sup_items p I
          \<and> dom_no_scan p I"
  shows "measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I' \<and> 
        invariant_pointers' p' \<and> dom_sup_items p' I' \<and> dom_no_scan p' I'"
proof -
  have "I \<subseteq> I'" using assms Scan'_sub by blast
  with Scan'_pointers [OF assms(2) assms(3) assms(4) assms(5) assms(1) assms(6) ] show ?thesis 
    using in_set_trans  assms by blast
qed

lemma Scan_eq:"fst (Scan' T k  I)  = Scan T k (fst I)"
  using Scan_def 
  by (smt (verit) Complete'.elims Scan'.simps fst_conv)

fun step'::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow> ('a, 'b) sppf_items" where
"step' k T   =(\<lambda> I. Scan' T k (Complete' k (Predict' k I))) "


lemma step'_invar:
  assumes "step' k T (I, p) = (I', p')" 
          "measure_help_monotone p \<and> red_complete p \<and> in_set p I \<and> invariant_pointers' p"
          "finite I \<and> finite T" "valid_bounds I" "valid_rule I" "dom_sup_items p I" "dom_no_scan p I"
          "\<forall>(t, c)\<in>T. length c \<in> Lex t Doc k" "\<forall>(t, c)\<in>T. is_terminal t" "\<forall>(t, c)\<in>T. length c > 0"
        shows "measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I' \<and> invariant_pointers' p' 
              \<and> finite I' \<and> valid_bounds I' \<and> valid_rule I' \<and> dom_sup_items p' I' \<and> dom_no_scan p' I'"
proof -
  obtain I'' p'' where step1:"(I'', p'') = Predict' k (I, p)" by simp
  then have 0:"p'' = p \<and> (Predict k I) =  I''" by auto 
  then have 1:"p'' = p \<and>  I \<subseteq>  I''" by (auto simp add: Predict_def) 
  then have inv:"measure_help_monotone p'' \<and> red_complete p'' \<and> in_set p'' I'' 
    \<and> invariant_pointers' p'' " using assms in_set_trans  by blast
  from step1 assms have fin1:"finite I''" by (auto simp add: Predict'_finite)
  from step1 assms have bound1:"valid_bounds I''" using Predict_bounds 0 by blast
  from step1 assms have rule1:"valid_rule I''" using Predict'_rule by simp
  from step1 assms have dom_sup1:"dom_sup_items p'' I''" using Predict'_dom_sup 1 by metis
  from step1 assms have dom_no_scan1:"dom_no_scan p'' I''" using Predict'_dom_no_scan by metis 
  obtain I''' p''' where step2:"(I''', p''') = Complete' k (I'', p'')" by simp
  then have 2:"measure_help_monotone p''' \<and> red_complete p''' \<and> in_set p''' I'' \<and> 
    invariant_pointers' p''' \<and> dom_sup_items p''' I''' \<and> dom_no_scan p''' I'''" using Complete'_pointers inv dom_sup1 
    dom_no_scan1 bound1 fin1 by auto
  from step2 have "I'' \<subseteq> I'''" by (auto simp add: Complete_def)
  with 2 have inv':"measure_help_monotone p''' \<and> red_complete p''' \<and> in_set p''' I'''
      \<and> invariant_pointers' p''' \<and> dom_sup_items p''' I''' \<and> dom_no_scan p''' I'''" 
    using in_set_trans by blast
  from step2 fin1 have fin2:"finite I'''" by (auto simp add: Complete'_finite)
  from step2 bound1 have bound2:"valid_bounds I'''" by (auto simp add: Complete'_bounds)
  from step2 rule1 have rule2:"valid_rule I'''" by (auto simp add: Complete'_rule)
  have step3:"(I', p') = Scan' T k (I''', p''')" using step1 step2  assms(1) by auto
  then have inv'':"measure_help_monotone p' \<and> red_complete p' \<and> in_set p' I' \<and> invariant_pointers' p' 
  \<and> dom_sup_items p' I' \<and> dom_no_scan p' I'"
    using Scan'_pointers' assms inv' fin2  by simp
  from step3 fin2 assms have fin3:"finite I'" using Scan'_finite by metis
  from step3 bound2 have bound3:"valid_bounds I'" and rule3: "valid_rule I'" using Scan'_bounds apply metis
    using step3 rule2 Scan'_rule by metis
  with inv'' fin3 show ?thesis using assms by simp
qed

section "\<pi> function"

fun \<pi>' :: "nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow> ('a, 'b) sppf_items"
where
  "\<pi>' k T I = 
     while (\<lambda> I. fst (step' k T I) \<noteq> fst I) (step' k T) I"

lemma step_eq:"fst (step' k T I)  = step k T (fst I)" 
  using step_def Complete_eq Predict_eq Scan_eq by simp

definition invariant''::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow>('a, 'b) sppf_items \<Rightarrow> bool" where
"invariant'' k  T init I = (\<exists> n . funpower (step k T) n  (fst init)   = fst I)" (*there exists a *)

lemma inv''_1:
  assumes "invariant'' k T I s " " fst (step' k T s) \<noteq> fst s" 
  shows " invariant'' k T I (step' k T s)"
proof -
  from assms obtain n where 1:"funpower (step k T) n  (fst I)   = fst s" using invariant''_def by blast
  from assms have "step k T (fst s) = fst (step' k T s)" using step_eq by auto
  with 1  have "funpower (step k T) (Suc n) (fst I) = fst (step' k T s)" by auto
  then show ?thesis using invariant''_def by blast
qed

lemma step_inc':
  "funpower (step k T) n I = s \<Longrightarrow>  s \<subseteq> funpower (step k T) (n' + n) I"
proof (induction n')
  case 0
  then show ?case by simp
next
  case (Suc n')
  have "funpower (step k T) (Suc (n' + n) ) I = step k T (funpower (step k T) (n' + n) I)" by auto
  then have "(funpower (step k T) (n' + n) I) \<subseteq> funpower (step k T) (Suc (n' + n)) I " using step_def 
    using step_inc by auto
  then show ?case using Suc by simp
qed

lemma inv''_2:
  assumes "invariant'' k T I s " " fst (step' k T s) = fst s" 
  shows "\<pi> k T (fst I) = fst s"
proof -
  obtain new where new_def:"new = step' k T s" by simp
  with assms(2)  have "fst new \<subseteq> fst s" by blast (*how does it hold?*)
  from assms(1) have "(\<exists>n. funpower (step k T) n (fst I) = fst s)" using invariant''_def by simp
  then obtain n where base:"funpower (step k T) n  (fst I)   = fst s"  by blast
  then have  1:"funpower (step k T) (n' + n)  (fst I) = fst s" for n'
  proof (induction n')
    case 0
    then show ?case using base by simp
  next
    case (Suc n')
    have "funpower (step k T) (Suc n' + n) (fst I) =  step k T (funpower  (step k T) (n' + n)  (fst I))"  by simp
    then have "funpower (step k T) (Suc n' + n) (fst I) =  step k T (fst s)" using Suc by auto
    then show ?case using assms step_eq by auto
  qed  
  from base have 2:"natUnion' n (\<lambda> n. funpower (\<lambda> I. Scan T k (Complete k (Predict k I))) n (fst I)) = fst s" 
      using step_natunion' 
      by (simp add: add.commute) 
  from 1 have "\<forall> n' \<ge> 0 . funpower (step k T) (n' + n)  (fst I) = fst s" by simp
  from 1 have "\<Union> {((\<lambda> n. funpower (\<lambda> I. Scan T k (Complete k (Predict k I))) n (fst I)) n') | n' .n' \<ge> n} = (fst s)" 
    apply (auto simp add: step_def) 
    apply (metis add.commute less_eqE) 
    using nat_le_iff_add by auto
  then have "natUnion (\<lambda> n. funpower (\<lambda> I. Scan T k (Complete k (Predict k I))) n (fst I)) = (fst s)" 
    apply (auto simp add: natUnion_def) using step_inc' 2 
    by (smt (z3) Union_iff mem_Collect_eq natUnion'_def nat_le_linear)
  then show ?thesis by (simp add: \<pi>_def limit_def )
qed

definition invariant'''::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow>('a, 'b) sppf_items \<Rightarrow> bool" where
"invariant''' k  T init I = (invariant'' k  T init I \<and>  fst (step' k T I) \<noteq> fst I)" (*there exists a *)

(*new measure*)
definition meas_All_top'::"('a, 'b) sppf_items  \<Rightarrow> nat" where
"meas_All_top' I  = card {s . s \<in> All_top \<and>   s \<notin> (fst I)}"
(*modified all_top version*)
definition invariant_All_top'::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow> bool" where
"invariant_All_top'  k  T init I = ((fst I) \<subseteq> All_top \<and> k \<le> length Doc \<and> (\<forall> (t, c) \<in> T . k + length c \<le> length Doc) 
   \<and> (\<exists> n . fst (funpower (step' k T) n  init)   = fst I))" (*there exists a *)

lemma invariant_All_top'_step:
  assumes "invariant_All_top' k T I s" "fst (step' k T s) \<noteq> fst s" 
  shows "invariant_All_top' k T I (step' k T s)"
proof -
  from assms obtain n where "fst (funpower (step' k T) n  I)   = fst s" 
    using invariant_All_top'_def by meson
  then have 1:"fst (funpower (step' k T) (Suc n)  I) = step k T (fst s)" using step_eq by simp
  with assms invariant_All_top'_def have "step k T (fst s) \<subseteq> All_top" using step_def Step_All_top by simp
  with assms invariant_All_top'_def 1 step_eq show ?thesis by metis
qed

lemma step_eq':"fst (funpower (step' k T) n  init)   =  funpower (step k T) n (fst init) "
proof (induct n arbitrary: I)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "fst (funpower (step' k T) (Suc n) init) = fst (step' k T (funpower (step' k T)  n init))"
    by simp
  with step_eq have "fst (funpower (step' k T) (Suc n) init) = step  k T (fst (funpower (step' k T)  n init))"
    by simp
  with Suc show ?case by simp
qed 

lemma invariant_All_top'_final:
  assumes "invariant_All_top' k T I s " "fst (step' k T s) = fst s " 
  shows "\<pi> k T (fst I) = fst s \<and> fst s \<subseteq> All_top \<and> step k T (fst s) = (fst s)"
proof -
  obtain n where  "fst s \<subseteq> All_top \<and> fst (funpower (step' k T) n  I)   = fst s" 
    using assms(1)  by (auto simp add: invariant_All_top'_def)
  then have "invariant_All_top k T (fst I) (fst s)" 
     using step_eq' invariant_All_top_def invariant_All_top'_def assms(1) by presburger
   with step_eq assms(2) show ?thesis
     using limit' by presburger
qed

lemma  meas_All_top'_decreasing:
  assumes "invariant_All_top'  k  T init  x \<and> fst (step' k T x) \<noteq> fst x"
  shows "meas_All_top'  (step' k T x) < meas_All_top' x "
proof -
  obtain x' x'' where x':"x' = fst x \<and> x'' = step k T x'" by simp 
  then have x'':"x'' = fst (step' k T x)" using step_eq by simp
  from x' assms have top:"x' \<subseteq> All_top" using invariant_All_top'_def  by simp
  then have top':"x'' \<subseteq> All_top" using x' assms invariant_All_top'_def Step_All_top step_def by simp
  from assms have "x' \<subset> x''" using   step_inc  x' step_eq by fast 
  with top top' have "{s . s \<in> All_top \<and>   s \<notin>  step k T x'} \<subset> {s . s \<in> All_top \<and>   s \<notin>   x'}" 
    by (smt (verit, best) Collect_mono_iff subset_iff subset_not_subset_eq x')
  then have sub:"{s . s \<in> All_top \<and>   s \<notin>  fst (step' k T x)} \<subset> {s . s \<in> All_top \<and>   s \<notin>   (fst x)}"
    using x' x'' by simp
  from All_top_fin have fin:"finite  {s . s \<in> All_top \<and>   s \<notin> (fst x)}" by simp
  show ?thesis apply(simp add: meas_All_top'_def) using sub fin   psubset_card_mono by auto
qed

lemma wf_All_top:"wf {(t, s). invariant_All_top' k T init  s \<and> fst (step' k T s) \<noteq> fst s \<and> t = step' k T s}"
  using wf_if_measure [where ?P="\<lambda> x . invariant_All_top' k T init x \<and> fst (step' k T x) \<noteq> fst x" 
      and ?g="(\<lambda> I .  step' k T I)"and ?f = "meas_All_top'"]
  meas_All_top'_decreasing  by fastforce

lemma All_top_equality:
  assumes  "k \<le> length Doc" "\<forall> (t, c) \<in> T. k + length c \<le> length Doc" "fst I \<subseteq> All_top"
  shows "fst (\<pi>' k T I ) = \<pi> k T (fst I)"
proof -
  have "funpower (step' k T) 0 I = I" by simp
  then have 0:"invariant_All_top' k T I I" using invariant_All_top'_def using assms by metis
  from assms have 1:"\<pi> k T (fst I) = while (\<lambda> I .  step k T I  \<noteq> I) (step k T) (fst I)" 
      using \<pi>_termination_All_top by simp
  have 2:"\<pi>' k T I = while (\<lambda> I .  step k T (fst I)  \<noteq> (fst I)) (step' k T)  I" using step_eq by simp
  have "\<pi> k T (fst I) = fst (while (\<lambda> I .  fst (step' k T  I)  \<noteq> (fst I)) (step' k T)  I) "
    apply (rule while_rule_lemma [where ?P = "invariant_All_top' k T I" and?b = "(\<lambda> I .  fst (step' k T  I)  \<noteq> fst I)" and ?c = "step' k T" and ?s =  "I" ])
    using invariant_All_top'_step apply simp
    using invariant_All_top'_final  apply simp (*should probably add other invariants*)
    using wf_All_top assms apply blast
    using 0 by simp
  then show ?thesis by simp
qed

(*inherited wf*)

section "Other invariants"

fun invariant_pointers::"('a, 'b) sppf_items \<Rightarrow> bool" where
"invariant_pointers (I, s) = (measure_help_monotone s \<and> red_complete s \<and> in_set  s I \<and> 
invariant_pointers' s \<and> finite I \<and> valid_bounds I \<and> valid_rule I \<and> dom_sup_items s I \<and> dom_no_scan s I)"

lemma invariant_pointers_step:
  assumes "finite T " "\<forall>(t, c)\<in>T. length c \<in> Lex t Doc k" 
   "\<forall>(t, c)\<in>T . is_terminal t " "\<forall>(t, c)\<in>T. length c > 0" "invariant_pointers Ip"  
  shows "invariant_pointers (step' k T Ip)" 
proof -
  obtain I p where 1:"(I, p) = Ip" by (metis invariant_pointers.cases)
  with assms have 2:"measure_help_monotone p \<and> red_complete p \<and> in_set p I \<and> invariant_pointers' p" by force
  from 1 assms have 3:" valid_bounds I" and 4:" valid_rule I " and 5:" dom_sup_items p I " 
    and 6:"dom_no_scan p I" by auto
  from 1 assms have 7:"finite I \<and> finite T" by auto
  obtain I' p'  where step:"step' k T (I, p) = (I', p')" using 1 by fastforce
  then have "invariant_pointers (I', p') "  using step'_invar [OF step 2 7 3 4 5 6 assms(2) assms(3) assms(4)] by simp
  with step 1 show ?thesis by simp
qed

definition invariant4::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow>('a, 'b) sppf_items \<Rightarrow> bool" where
"invariant4 k  T init I = (invariant'' k  T init I \<and>  invariant_pointers I \<and> finite T \<and> (\<forall>(t, c)\<in>T. length c \<in> Lex t Doc k)
    \<and> (\<forall>(t, c)\<in>T. is_terminal t) \<and> (\<forall>(t, c)\<in>T. length c > 0))" (*there exists a *)

thm while_rule_lemma [where ?P = "invariant4 k T (I, p)" and?b = "(\<lambda> I .  fst (step' k T  I)  \<noteq> fst I)" 
and ?c = "step' k T" and ?s =  "(I, p)"  and ?Q="invariant_pointers"]


lemma inv4_1:"invariant4 k T I s \<Longrightarrow> fst (step' k T s) \<noteq> fst s \<Longrightarrow> invariant4 k T I (step' k T s)"
  apply (simp add:invariant4_def) 
  using inv''_1 invariant_pointers_step by auto

lemma inv4_2:"invariant4 k T (I, p) s \<Longrightarrow> \<not> fst (step' k T s) \<noteq> fst s \<Longrightarrow> invariant_pointers s"
  using invariant4_def by auto

lemma wf_sub: "{(t, s). invariant4 k T (I, p) s \<and> fst (step' k T s) \<noteq> fst s \<and> t = step' k T s} \<subseteq> 
  {(t, s). invariant'' k T (I, p )s \<and> fst (step' k T s) \<noteq> (fst s) \<and> t = step' k T s}"
  using invariant4_def by blast


(*the one invariant of non-empty tokens might be better off removed*)
definition invariant_pointers_All_top::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) sppf_items \<Rightarrow>('a, 'b) sppf_items \<Rightarrow> bool" where
"invariant_pointers_All_top k  T init I = (invariant_All_top' k  T init I \<and>  invariant_pointers I \<and> finite T \<and> (\<forall>(t, c)\<in>T. length c \<in> Lex t Doc k)
    \<and> (\<forall>(t, c)\<in>T. is_terminal t) \<and> (\<forall>(t, c)\<in>T. length c > 0))" 

lemma invariant_pointers_All_top_step:"invariant_pointers_All_top k T I s \<Longrightarrow> 
fst (step' k T s) \<noteq> fst s \<Longrightarrow> invariant_pointers_All_top k T I (step' k T s)"
  apply (simp add:invariant_pointers_All_top_def) 
  using invariant_All_top'_step invariant_pointers_step by auto

lemma invariant_pointers_All_top_final:"invariant_pointers_All_top k T I s \<Longrightarrow> 
  fst (step' k T s) = fst s \<Longrightarrow> invariant_pointers s"
  by (simp add:invariant_pointers_All_top_def) 

lemma wf_invariant_pointers_All_top_help: "{(t, s). invariant_pointers_All_top k T (I, p) s \<and> fst (step' k T s) \<noteq> fst s \<and> t = step' k T s} \<subseteq> 
  {(t, s). invariant_All_top' k T (I, p )s \<and> fst (step' k T s) \<noteq> (fst s) \<and> t = step' k T s}"
  using invariant_pointers_All_top_def by blast 

lemma wf_invariant_pointers_All_top:"wf {(t, s). invariant_pointers_All_top k T (I, p) s \<and> fst (step' k T s) \<noteq> fst s \<and> t = step' k T s}"
  using  wf_subset [OF wf_All_top wf_invariant_pointers_All_top_help] by blast


lemma \<pi>'_pointer_invariants:
  assumes "invariant_pointers (I, p)" 
      "(\<forall> (t, c) \<in> T . length c > 0) \<and> (\<forall>(t, c)\<in>T. length c \<in> Lex t Doc k) \<and> (\<forall>(t, c)\<in>T. is_terminal t)
      \<and> finite T"
      "k \<le> length Doc" "\<forall> (t, c) \<in> T. k + length c \<le> length Doc" "I \<subseteq> All_top"
  shows "invariant_pointers (\<pi>' k T (I, p ))"
proof -
  have "fst (funpower (step' k T) 0 (I, p)) = fst (I, p) \<and> fst (I, p) \<subseteq> All_top" using assms by simp
  then have 0:"invariant_All_top' k T (I, p) (I, p)" using invariant_All_top'_def assms by blast 
  then have init':"invariant_pointers_All_top k T (I, p) (I, p)" using invariant_pointers_All_top_def
      assms(1) assms(2)  by (meson funpower.simps(1))
   have "invariant_pointers (while (\<lambda>I. fst (step' k T I) \<noteq> fst I) (step' k T) (I, p))"
    apply (rule while_rule_lemma [where ?P = "invariant_pointers_All_top k T (I, p)" and?b = "(\<lambda> I .  fst (step' k T  I)  \<noteq> fst I)" 
and ?c = "step' k T" and ?s =  "(I, p)"  and ?Q="invariant_pointers"])
     using invariant_pointers_All_top_step apply blast 
     using invariant_pointers_All_top_final apply blast
     using wf_invariant_pointers_All_top apply blast
     using init' by blast
   then show ?thesis by simp
 qed


fun update_tree::"('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> ('a, 'b) derivtree" where 
"update_tree (DT r b) t = (DT r (b@[t]))" |
"update_tree (Leaf s) t = (Leaf s)"|
"update_tree (Inner s) t = (Inner s)"

fun step_I'::"nat \<Rightarrow> (('a, 'b, 'c) token set \<times> ('a, 'b) sppf_items) \<Rightarrow> 
  (('a, 'b, 'c) token set \<times> ('a, 'b) sppf_items)" where
" step_I' k (T, I) = (Tokens k T (fst I), \<pi>' k (Tokens k T (fst I)) I)"


fun \<J>' :: "nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) sppf_items"
and \<I>' :: "nat \<Rightarrow> ('a, 'b) sppf_items"
and \<T>' :: "nat \<Rightarrow> nat \<Rightarrow> ('a, 'b, 'c) token set"
where
  "\<J>' 0 0 = \<pi>' 0 {} (Init, (Map.empty, Map.empty))" (*Initial Element*)
| "\<J>' k (Suc u) = \<pi>' k (\<T>' k (Suc u)) (\<J>' k u)" (*Early parsing*)
| "\<J>' (Suc k) 0 = \<pi>' (Suc k) {} (\<I>' k)" 
| "\<T>' k 0 = {}"
| "\<T>' k (Suc u) = Tokens k (\<T>' k u) (fst (\<J>' k u))" (*selector step*)
| "\<I>' k = (snd (while (\<lambda> T.  fst (step_I'  k T) \<noteq> (fst T)) (step_I' k) 
  ({}, \<J>'  k 0)))" (*upperbound at least Doc length \<Longrightarrow> no proper upperground here*)

(*proofs via induction actually*)
(*
lemma \<J>'_eq:
  shows  "fst (\<J>' k k') = \<J> k k'" "\<T>' k k' = \<T> k k'" "fst (\<I>' k) = \<I> k"
*)

fun iterate::"nat \<Rightarrow> (('a, 'b, 'c) token set \<times> ('a, 'b) sppf_items) \<Rightarrow> 
  (('a, 'b, 'c) token set \<times> ('a, 'b) sppf_items)" where
"iterate k s = (while (\<lambda> s. fst (step_I' k s) \<noteq> fst s) (step_I' k) s)"


lemma step_I'_eq:"fst (step_I' k s) = fst (step_I k (fst s, fst (snd s)))"
  by (metis fst_conv prod.collapse step_I'.simps step_I.simps)

(*unused*)
(*
lemma step_I'_eq':"fst (snd (step_I' k s)) = snd (step_I k (fst s, fst (snd s)))"
  using All_top_equality  (*additional assumption to carry about*)
*)
definition invariant_T_top'::"nat \<Rightarrow> (('a, 'b, 'c) token set \<times> ('a, 'b) sppf_items) \<Rightarrow> bool" where
"invariant_T_top' k T = ((fst (snd T) = fst (step' k (fst T) (snd T))) \<and>  (\<exists> k' . (\<J> k k' = fst (snd T)) \<and> (\<T> k k' = fst T)) 
    \<and> (fst T) \<subseteq> TokensAt k (fst(snd T)) \<and> fst T \<subseteq> TokensAt_top k \<and> fst (snd T) \<subseteq> All_top)"

lemma \<J>'_step:
  assumes "invariant_T_top' k s " "fst (step_I' k s) \<noteq> fst s" "k \<le> length Doc"
  shows "invariant_T_top' k (step_I' k s)"
proof -
  obtain T I p  where s_def:"(T, I, p) = s" apply(cases s ) by blast
  then obtain k' where 1:"(\<J> k k' = I) \<and> (\<T> k k' = T)" using assms(1) 
      invariant_T_top'_def by fastforce
  from assms(1) invariant_T_top'_def have "(I = fst (step' k (T) (I, p)))" using s_def by fastforce
  with step_eq  have 2:"I = step k T I" by force
  from s_def  assms(1) invariant_T_top'_def have 
    3:"T \<subseteq> TokensAt k I \<and> T \<subseteq> TokensAt_top k \<and> I \<subseteq> All_top" by fastforce
  with 1 2 have invar:"invariant_T_top k (T, I)"  using invariant_T_top_def by auto
  from assms(2) step_I'_eq s_def have "fst (step_I k (T, I)) \<noteq> T" by force
  with assms(3) invar have 6:"invariant_T_top k (step_I k (T, I))" using \<J>_step by force
  (*could in theory also just be reused anyways*)
  (*step equality*)
  obtain T' I' p' where 2:"(T', I', p') = step_I' k s" apply(cases "step_I' k s") by simp
  with s_def have 4:"T' = Tokens k T I \<and> (I', p') = \<pi>' k (Tokens k T  I) (I, p)" by force
  with 1 have T':"T' = \<T> k (Suc k')" by force
  from 3 4 have "T' \<subseteq> (TokensAt k I)" using Tokens_def Sel_is_selector is_selector_def by blast
  then have valid_tokens:"\<forall> (t, c) \<in> T' . k + length c \<le> length Doc " using TokensAt_subset_\<X> \<X>_length_bound by fastforce
  have 5:"I' = \<pi> k T' I" using All_top_equality [OF assms(3) valid_tokens, where ?I="(I, p)"] using 4 3 
    by (metis fst_conv)
  with 4 have "I' = \<J> k (Suc k')" using 1 T' by simp 
  from 5 4 have "(T', I') = (step_I k (T, I))" by simp
  then show ?thesis using 2 6 
    by (metis (no_types, lifting) fst_conv invariant_T_top'_def invariant_T_top_def snd_conv step_eq)
qed

lemma step_I'_help:
  assumes "\<T>' k (Suc k') = \<T>' k k' "" \<J>' k k' = step' k (\<T>' k k') (\<J>' k k')" 
  shows     "\<T>' k (Suc (Suc k')) = \<T>' k k' \<and> \<J>' k k' = \<J>'  k (Suc k')"
proof -
  from assms have "\<J>'  k (Suc k') = \<pi>' k (\<T>' k k') (\<J>' k k')" by simp
  then have 1:"\<J>'  k (Suc k') = while (\<lambda> I. fst (step' k (\<T>' k k') I) \<noteq> fst I) (step' k (\<T>' k k')) (\<J>' k k')" by simp
  with assms(2) have "\<not> (\<lambda> I. fst (step' k (\<T>' k k') I) \<noteq> fst I) (\<J>' k k')" by simp
  with 1 have 2:"\<J>'  k (Suc k') = (\<J>' k k')" using while_unfold by (smt (z3))
  with assms(1) have "\<T>' k (Suc (Suc k')) = Sel (\<T>' k  k') (TokensAt k (fst (\<J>' k k')))" using
    Tokens_def by simp
  then have "\<T>' k (Suc (Suc k')) = \<T>' k (Suc k')" using Tokens_def by simp 
  then show ?thesis using 2 assms(1) by simp
qed

(*unnecessary actually \<longrightarrow> we just care about reusing the old part*)

(*use nat union case *)
lemma invariant_T_top_lift:"invariant_T_top' k (T, I, p) \<Longrightarrow> invariant_T_top k (T, I)"
 using invariant_T_top_def invariant_T_top'_def step_eq by fastforce
lemma \<J>'_final: (*using natunion formulation, it seems easier to just add the invariant that (fst (snd) = J_k*)
  (*only the needed information is carried around*)
  assumes "invariant_T_top' k s " "fst (step_I' k s) = fst s" "k \<le> length Doc"
  shows "natUnion (\<J> k) = fst (snd s) \<and> natUnion (\<J> k)   \<subseteq> All_top" (*and pointer invariants*)
proof -
  obtain T I p where T_def:"(T, I, p) = s" apply (cases s) by blast
  obtain k' where def:"(\<J> k k' = fst (snd s)) \<and> (\<T> k k' = fst s)" using invariant_T_top'_def assms(1) by blast
  (*should lifted from a theorem in Local Lexing*)
  have "fst (step_I' k s) = (Tokens k (fst s) (fst (snd s)))" apply(cases s) by auto
  with assms(2) def have "Tokens k (\<T> k k') (\<J> k k') = \<T> k k'" by simp
  then have "\<T> k (Suc k') = \<T> k k'" using  Tokens_def by simp

  from T_def assms have 4:"invariant_T_top k (T, I)" 
    using invariant_T_top_lift by blast
  from assms T_def have "fst (step_I k (T, I)) = T" by auto
  then have "\<I> k = I \<and> \<I> k \<subseteq> All_top" using \<J>_final [OF 4] assms(3) by auto
  then have "natUnion (\<J> k) = (\<J> k k')" using def T_def by auto 
  (*to be proven in LocalLexing*)
  then show ?thesis using invariant_T_top'_def assms def by blast  
qed

fun meas_T_I'::"nat \<Rightarrow> (('a, 'b, 'c) token set \<times> ('a, 'b) sppf_items)  \<Rightarrow> nat " where
"meas_T_I' k (T, I)  = card {s . s \<in> TokensAt_top k \<and>   s \<notin> T}"

lemma meas_T_I'_help:"meas_T_I k (T, I) = meas_T_I' k (T, I, p)"
  by auto

lemma meas_T_I'_help':"meas_T_I' k (step_I' k (T, I, p)) = meas_T_I k (step_I k (T, I))"
  by simp
lemma meas_T_I'_decreases:
  assumes "invariant_T_top' k s" "fst (step_I' k s) \<noteq> fst s" 
  shows "meas_T_I' k (step_I' k s) < meas_T_I' k s"
proof -
  obtain T I p  where s_def:"(T, I, p) = s" apply(cases s ) by blast
  then obtain k' where 1:"\<J> k k' = I \<and> \<T> k k' = T" using assms(1) 
      invariant_T_top'_def by fastforce
  from assms(1) invariant_T_top'_def have "(I = fst (step' k (T) (I, p)))" using s_def by fastforce
  with step_eq  have 2:"I = step k T I" by force
  from s_def  assms(1) invariant_T_top'_def have 
    "T \<subseteq> TokensAt k I \<and> T \<subseteq> TokensAt_top k \<and> I \<subseteq> All_top" by fastforce
  with 1 2 have invar:"invariant_T_top k (T, I)"  using invariant_T_top_def by auto
  from assms(2) step_I'_eq s_def have "fst (step_I k (T, I)) \<noteq> T" by force
  with meas_T_I_decreases invar have "meas_T_I k (step_I k (T, I)) < meas_T_I k (T, I)" by force
  (*then upload measure*)
  then show ?thesis using meas_T_I'_help meas_T_I'_help' s_def by force 
qed

lemma init':
  assumes "Suc k \<le> length Doc " "fst (\<I>' k) = \<I> k"
  shows " invariant_T_top' (Suc k) ({}, \<J>' (Suc k) 0)"
proof -
  have 0:"\<I> k \<subseteq> All_top" using \<I>_k_sub_All_top assms by simp
  have 1:"((\<exists> k' . (\<J> (Suc k) k' = \<J> (Suc k) 0) \<and> (\<T> (Suc k) k' = {})) 
    \<and> {} \<subseteq> TokensAt (Suc k) (\<J> (Suc k) 0) \<and> {}  \<subseteq> TokensAt_top (Suc k))" by fastforce
  have t:"\<forall>(t, c)\<in> {}. Suc k + length c \<le> length Doc" by blast
  have step:"\<J>' (Suc k) 0  = \<pi>' (Suc k) {} (\<I>' k)" by simp
  then have 2:"fst (\<J>' (Suc k) 0)  = \<pi> (Suc k) {} (\<I> k)" using All_top_equality [OF assms(1) t] 
    using assms 0  by auto
  then have "fst (\<J>' (Suc k) 0) = \<J> (Suc k) 0" by auto
  
  then show ?thesis using init 
    using assms(1) 0 invariant_T_top'_def invariant_T_top_def step_eq by auto
qed

lemma wf_T_I':"wf {(t, s). invariant_T_top' k s \<and> fst (step_I' k s) \<noteq> fst s \<and> t = step_I' k s}"
  using wf_if_measure [where ?P="\<lambda> s . invariant_T_top' k s \<and> fst (step_I' k s) \<noteq> fst s" and ?g="step_I' k" 
        and ?f= "meas_T_I' k"] meas_T_I'_decreases by simp

lemma \<I>'_equality:"fst (\<I>' k) = \<I> k \<Longrightarrow> (Suc k) \<le> length Doc \<Longrightarrow> \<I> (Suc k) = 
  fst (snd (while (\<lambda> T.  fst (step_I'  (Suc k) T) \<noteq> (fst T)) (step_I' (Suc k)) ({}, \<J>' (Suc k) 0))) \<and> \<I> (Suc k) \<subseteq> All_top"
    apply (rule while_rule_lemma [where   ?s =  "({}, \<J>' (Suc k) 0)" and ?c="step_I' (Suc k)" 
          and ?b="(\<lambda> TI.  fst (step_I'  (Suc k) TI) \<noteq> fst TI)" and ?Q = "\<lambda> f . \<I> (Suc k)  = fst (snd f) 
    \<and> \<I> (Suc k) \<subseteq> All_top" and ?P="invariant_T_top' (Suc k) "])
  using \<J>'_step apply presburger
  using \<I>.simps \<J>'_final apply blast
  using wf_T_I' apply blast
  using init' by blast



definition \<I>'_pointer_invariants::"nat \<Rightarrow> ( ('a, 'b) sppf_items) \<Rightarrow> bool" where
"\<I>'_pointer_invariants k I = (invariant_pointers I \<and> fst I = \<I> k) "

definition \<I>'_pointer_invariants'::"nat \<Rightarrow> (('a, 'b, 'c) token set \<times>  ('a, 'b) sppf_items) \<Rightarrow> bool"
where
  "\<I>'_pointer_invariants' k TI = (invariant_T_top' k TI \<and> invariant_pointers (snd TI))"

lemma TokensAt_invariants:
  assumes "k \<le> length Doc"
  shows "(\<forall>(t, c)\<in>TokensAt k I . length c \<in> Lex t Doc k \<and> is_terminal t \<and>  k + length c \<le> length Doc) 
  \<and> finite (TokensAt k I)"
proof -
  obtain T_top where top_def:"T_top = { (t, s) | t s  l. is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc) }" by blast
  then have 1:"\<forall>(t, c) \<in> T_top. is_terminal t" by blast
  then have "\<forall>(t, c) \<in> T_top . \<exists> l.  t \<in> \<TT> \<and> l \<in> Lex t Doc k \<and> c = take l (drop k Doc)" 
    using top_def by (simp add: terminal_in_\<TT>)
  then have "\<forall>(t, c) \<in> T_top . \<exists> l.  is_lexer (Lex t) \<and> l \<in> Lex t Doc k \<and> 
    c = take l (drop k Doc) " using Lex_is_lexer by auto
  then have "\<forall>(t, c) \<in> T_top . \<exists> l.   (\<forall> l. (k \<le> length Doc \<and> l \<in> Lex t Doc k \<longrightarrow> k + l \<le> length Doc) 
        \<and> (length Doc < k \<longrightarrow> Lex t Doc k = {})) \<and> l \<in> Lex t Doc k \<and> 
    c = take l (drop k Doc) " apply(simp add: is_lexer_def) by auto
  with assms have "\<forall>(t, c) \<in> T_top . \<exists> l.   l \<in> Lex t Doc k \<and> 
    c = take l (drop k Doc) \<and> l + k \<le> length Doc" using assms by fastforce
  then have "\<forall>(t, c) \<in> T_top . \<exists> l.   l \<in> Lex t Doc k \<and> 
    c = take l (drop k Doc) \<and> l + k \<le> length Doc \<and> length c = l" by fastforce
  then have "\<forall>(t, c) \<in> T_top . \<exists> l.   length c \<in> Lex t Doc k \<and> length c + k \<le> length Doc" by auto 
  then have 2:"\<forall>(t, c) \<in> T_top . length c \<in> Lex t Doc k \<and> length c + k \<le> length Doc" by simp
  have finite:"finite (TokensAt k I)" by (meson TokensAt_top finite_TokensAt_top finite_subset)
  from top_def have "TokensAt k I \<subseteq> T_top" using TokensAt_def by blast
  then show ?thesis using 1 2 finite by fastforce
qed

lemma I_step:
  assumes"k \<le> length Doc "
         "\<I>'_pointer_invariants'  k s" "fst (step_I' k s) \<noteq> fst s "
  shows " \<I>'_pointer_invariants' k (step_I' k s)"
proof -
  obtain T I p  where s_def:"(T, I, p) = s" apply(cases s ) by blast
  from assms(2) have 1:"invariant_T_top' k s " using \<I>'_pointer_invariants'_def by blast
  then have  res1:"invariant_T_top' k (step_I' k s)" using \<J>'_step assms by auto
  (*invariants hold*)
  from assms(2) have 2:"invariant_pointers (I,p)" using s_def \<I>'_pointer_invariants'_def 
    by fastforce
  from 1 have I_top:"I \<subseteq> All_top" using invariant_T_top'_def s_def by auto
  obtain T' where T':"T' = (Tokens k T I)" by simp
  from 1 have 3:"T \<subseteq> TokensAt k I" using invariant_T_top'_def s_def by auto
  have selected:"(Tokens k T I) = Sel T (TokensAt k I)" using Tokens_def  by simp
  then  have 4:"(Tokens k T I) \<subseteq> TokensAt k I"  using 3 Sel_is_selector is_selector_def by blast 
      (*needs a few steps*)(*should immediately hold*)
  with T' have T'_sub:"T' \<subseteq> TokensAt k I" by blast
  from selected have nonzero:"(\<forall> (t, c) \<in> T' . length c > 0)" using T' no_nonempty_tokens by blast
  from TokensAt_invariants [OF assms(1), where ?I="I"] T'_sub have 
    "(\<forall>(t, c)\<in>T'. length c \<in> Lex t Doc k \<and> is_terminal t \<and> 
    k + length c \<le> length Doc) \<and> finite (T')" using finite_subset by blast
  with nonzero have T'_invars:"(\<forall> (t, c) \<in> T' . length c > 0) \<and> (\<forall>(t, c)\<in>T'. length c \<in> Lex t Doc k) \<and> (\<forall>(t, c)\<in>T'. is_terminal t)
      \<and> finite T'" and T'_valid:"(\<forall> (t, c) \<in> T'. k + length c \<le> length Doc)" by auto
  have "snd (step_I' k s) =  \<pi>' k T' (I, p)" using s_def T' by auto
  then have "invariant_pointers (snd (step_I' k s))" 
    using \<pi>'_pointer_invariants [OF 2 T'_invars assms(1) T'_valid I_top] by simp
  with res1 show ?thesis using \<I>'_pointer_invariants'_def by blast
qed


lemma I_final:
  assumes "k \<le> length Doc " "\<I>'_pointer_invariants'  k s " 
          "\<not> fst (step_I' k s) \<noteq> fst s"
  shows  "\<I>'_pointer_invariants k (snd s)"
proof -
  have 0:"invariant_pointers (snd s)" using assms(2)  \<I>'_pointer_invariants'_def by blast
  obtain T I p  where s_def:"(T, I, p) = s" apply(cases s ) by blast
  with assms(3) have 1:"\<not> fst (step_I k (T, I)) \<noteq> fst (T, I)" by force
  from assms(2) s_def have "invariant_T_top k (T, I)" 
    using \<I>'_pointer_invariants'_def invariant_T_top'_def invariant_T_top_def step_eq by auto 
  with 1 assms(1) have "\<I> k = I" using \<J>_final by simp
  then show ?thesis using 0 s_def 
    using \<I>'_pointer_invariants'_def \<I>'_pointer_invariants_def \<I>.simps \<J>'_final assms(1) assms(2) assms(3) by blast
qed

lemma subset:"{(t, s). \<I>'_pointer_invariants' k s \<and> fst (step_I' k s) \<noteq> fst s \<and> t = step_I' k s}
    \<subseteq>{(t, s). invariant_T_top' k s \<and> fst (step_I' k s) \<noteq> fst s \<and> t = step_I' k s}"
  by (simp add: Collect_mono \<I>'_pointer_invariants'_def case_prod_beta')

lemma wf_pointer_invariants:
"wf {(t, s). \<I>'_pointer_invariants' k s \<and> fst (step_I' k s) \<noteq> fst s \<and> t = step_I'  k s}"
  using wf_subset [OF  wf_T_I' subset] by blast

lemma init'':
  assumes "\<I>'_pointer_invariants k (\<I>' k) " "Suc k \<le> length Doc "
  shows "\<I>'_pointer_invariants' (Suc k) ({}, \<J>' (Suc k) 0)"
proof -
  obtain I p where Ip:"(I, p) = (\<I>' k)" apply(cases "(\<I>' k)") by simp
  then  have 1:"invariant_pointers (I, p)" 
    using \<I>'_pointer_invariants_def by (metis assms(1))
  from assms Ip have I:"I = \<I> k"  using \<I>'_pointer_invariants_def by (metis  fst_conv) 
  then have I_alltop:"I \<subseteq> All_top" using \<I>_k_sub_All_top assms(2) by simp
  have 2:"(\<forall>(t, c)\<in>{}. 0 < length c) \<and> (\<forall>(t, c)\<in>{}. length c \<in> Lex t Doc (Suc k)) \<and> (\<forall>(t, c)\<in>{}. is_terminal t) \<and> finite {}"
    by blast
  have "\<J>' (Suc k) 0 = \<pi>' (Suc k) {} (\<I>' k)" by simp
  then have  3:"invariant_pointers (\<J>' (Suc k) 0)" using \<pi>'_pointer_invariants [OF 1 2 assms(2)] 
      assms I_alltop Ip by simp
  from init' [OF assms(2)] have "invariant_T_top' (Suc k) ({}, \<J>' (Suc k) 0)" using  I Ip 
    using \<I>'_pointer_invariants_def assms(1) by presburger
  with 3 show ?thesis using \<I>'_pointer_invariants'_def by auto
qed
(*Init \<longrightarrow> iss*)

(*have to include the All_top assumption*)

lemma \<I>'_pointer_invariants:"\<I>'_pointer_invariants k (\<I>' k) \<Longrightarrow> (Suc k) \<le> length Doc \<Longrightarrow> 
  \<I>'_pointer_invariants (Suc k) (snd (while (\<lambda> T.  fst (step_I'  (Suc k) T) \<noteq> (fst T)) (step_I' (Suc k)) 
  ({}, \<J>' (Suc k) 0)))"
    apply (rule while_rule_lemma [where   ?s =  "({}, \<J>' (Suc k) 0)" and ?c="step_I' (Suc k)" 
          and ?b="(\<lambda> TI.  fst (step_I'  (Suc k) TI) \<noteq> fst TI)" and 
          ?Q = "\<lambda> f . \<I>'_pointer_invariants (Suc k) (snd f) " and ?P="\<I>'_pointer_invariants' (Suc k)"])
  using I_step apply blast
  using I_final apply blast
  using wf_pointer_invariants apply blast
  using init'' by blast



definition I::"('a, 'b) items" where
"I = fst  (\<I>' (length Doc))"

definition pred::"('a, 'b) pointers" where
"pred = fst (snd (\<I>' (length Doc)))"


definition red::"('a, 'b) pointers" where
"red = snd (snd (\<I>' (length Doc)))"
(*measure*)

lemma empty_pred:"measure_help_monotone (Map.empty, Map.empty) \<and> red_complete (Map.empty, Map.empty) \<and>  
    in_set (Map.empty, Map.empty) Init \<and> invariant_pointers' (Map.empty, Map.empty)"
  by auto

lemma empty_tokens:"\<forall>(t, c)\<in>{}. 0 < length c "
  by simp

lemma Init_top:"Init \<subseteq> (\<lambda> r .init_item r 0)`\<RR> "
  using Init_def by blast
lemma init_valid_rules:"valid_rule Init"
  using Init_top init_item_def using valid_rule_def by auto

lemma finite_init:"finite Init" by (meson finite_surj finite_grammar Init_top) 
lemma valid_bounds_init:"valid_bounds Init"
  by (auto simp add: valid_bounds_def init_item_def Init_def)

lemma init_dom_sup:"dom_sup_items (Map.empty, Map.empty) Init"
  using Init_top init_item_def by auto

lemma init_dom_no_scan:"dom_no_scan (Map.empty, Map.empty) Init"
  using Init_top init_item_def by auto

lemma invariant_pointers_init:"invariant_pointers (Init , (Map.empty, Map.empty))"
using finite_init 
    valid_bounds_init init_valid_rules init_dom_sup init_dom_no_scan  by simp

lemma \<J>_init:"invariant_pointers (\<J>' 0 0)"
  using \<pi>'_pointer_invariants [OF invariant_pointers_init, where ?T="{}" and ?k="0"]
  Init_sub_All_top'  by simp


lemma \<J>_equality:"fst (\<J>' 0 0) = \<J> 0 0"
  using All_top_equality [where ?T="{}" and ?k="0" and ?I="(Init, (Map.empty, Map.empty))"] 
  Init_sub_All_top' by simp
(*Finiteness probagation*)

lemma \<J>_finite:"finite (fst (\<J>' 0 0))"
  by (metis \<J>_init fst_conv invariant_pointers.elims(2))


lemma \<I>'_pointer_invariants':"\<I>'_pointer_invariants k (\<I>' k) \<Longrightarrow> (Suc k) \<le> length Doc \<Longrightarrow> 
  \<I>'_pointer_invariants (Suc k) (\<I>' (Suc k))"
   using \<I>'_pointer_invariants by simp

lemma \<I>'_0_start:"\<I>'_pointer_invariants' 0 ({}, \<J>' 0 0)"
proof -
  have 0:"(invariant_T_top 0 ({}, \<J> 0 0))"  using \<I>_0_start by auto 
  have 1:"\<forall>(t, c)\<in>{}. 0 < length c " and 2:" finite {} \<and> finite (fst  (Init, (Map.empty, Map.empty)))"
    apply fastforce by (simp add: finite_init)
  obtain I p  where s_def:"(I, p) = \<J>' 0 0" apply(cases "\<J>' 0 0") by simp
  then have "fst (\<J>' 0 0) = \<J> 0 0" using \<J>_equality by auto
  with 0 have 2:"(invariant_T_top' 0 ({}, \<J>' 0 0))" 
    using invariant_T_top'_def invariant_T_top_def step_eq by auto
  with \<J>_init show ?thesis using \<I>'_pointer_invariants'_def by auto
qed

lemma \<I>'_0_pointer_invariants:"\<I>'_pointer_invariants 0 
  (snd (while (\<lambda> T.  fst (step_I'  0 T) \<noteq> (fst T)) (step_I' 0) 
  ({}, \<J>' 0 0)))"
    apply (rule while_rule_lemma [where   ?s =  "({}, \<J>' 0 0)" and ?c="step_I' 0" 
          and ?b="(\<lambda> TI.  fst (step_I'  0 TI) \<noteq> fst TI)" and 
          ?Q = "\<lambda> f . \<I>'_pointer_invariants 0 (snd f) " and ?P="\<I>'_pointer_invariants' 0"])
  using I_step apply blast
  using I_final apply blast
  using wf_pointer_invariants apply blast
  using \<I>'_0_start by blast

theorem \<I>'_invariants:"k \<le> length Doc \<Longrightarrow> \<I>'_pointer_invariants k (\<I>' k)"
  apply(induct k) using \<I>'_0_pointer_invariants apply simp 
  using Suc_leD \<I>'_pointer_invariants' by presburger
 (*actually conditioned on only parsing until doc length*)

(*where are the other invariants*)

lemma TokensAt_top':"{ (t, s) | t s x l. x \<in> bin I' k \<and> 
     next_symbol x = Some t \<and> is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc) } \<subseteq> { (t, s) | t s  l. is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc) }"
  by blast


lemma TokensAt_top:"TokensAt k I' \<subseteq> {(t, s) | t s l. is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc) }"
  by (auto simp add: TokensAt_top' TokensAt_def)

(*Lexing condition \<longrightarrow> holds because of lexer confition  *)

lemma TokensAt_top_lex':"\<forall> (t,c) \<in> {(t, s) | t s l. is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc) \<and> length s = l} . length c \<in> Lex t Doc k \<and> is_terminal t"
  by simp


thm "All_top_equality"

lemma \<J>_step_equality':
  assumes "k \<le> length Doc" "fst (\<J>' k u) = (\<J> k u)"  "fst (\<J>' k u) \<subseteq> All_top" "\<T>' k  u = \<T> k  u" 
          "\<T>' k  u \<subseteq> \<T>' k  (Suc u)" "(\<T>' k (Suc u)) \<subseteq> TokensAt k (fst (\<J>' k  u))"
        shows "fst (\<J>' k (Suc u)) = (\<J> k (Suc u)) \<and> \<T>' k  (Suc u) = \<T> k (Suc u) 
          \<and>  \<T>' k (Suc u) \<subseteq> \<T>' k  (Suc (Suc u)) \<and> (\<T>' k (Suc (Suc u))) \<subseteq> TokensAt k (fst (\<J>' k  (Suc u)))"
proof -
  (*premises for step*)

  have 0:"\<T>' k (Suc (Suc u)) = Tokens k (\<T>' k (Suc u)) (fst (\<J>' k (Suc u)))" by force
  have "\<T>' k (Suc u) = Tokens k (\<T>' k u) (fst (\<J>' k  u))" by force
  then have sub:"\<T>' k (Suc u) \<subseteq> TokensAt k (fst (\<J>' k u))" using assms by blast
  
  from TokensAt_invariants [OF assms(1), where ?I = "(fst (\<J>' k u))"] assms(6) have
    "(\<forall>(t, c)\<in> (\<T>' k (Suc u)). length c \<in> Lex t Doc k \<and> is_terminal t \<and> k + 
    length c \<le> length Doc) \<and> finite (\<T>' k (Suc u))" using finite_subset by blast
  then have val_lexing:"\<forall>(t, c)\<in> (\<T>' k (Suc u)) .  length c + k  \<le> length Doc" by auto

  from assms have 2:"\<T>' k (Suc u) = \<T> k (Suc u)" by force
  then have sol1:"fst (\<J>' k (Suc u)) = (\<J> k (Suc u))" using
       All_top_equality [OF  assms(1) , where ?T="\<T>' k (Suc u)" and ?I="(\<J>' k u)" ] assms(3) val_lexing
       assms by fastforce
  
  then have "fst (\<J>' k (Suc u)) = \<pi> k (\<T> k (Suc u)) (fst (\<J>' k u))" using assms(2) by auto
  then have "(fst (\<J>' k u)) \<subseteq> fst (\<J>' k (Suc u))" using \<pi>_monotone by presburger
  then have 3:"TokensAt k (fst (\<J>' k u)) \<subseteq> TokensAt k (fst (\<J>' k (Suc u)))" 
    by (meson mono_TokensAt mono_subset_elem subsetI)
  with sub have 4:"\<T>' k (Suc u) \<subseteq> TokensAt k (fst (\<J>' k (Suc u)))" by blast
  with 0 have sol3:"\<T>' k (Suc (Suc u)) \<subseteq> TokensAt k (fst (\<J>' k (Suc u)))" using Tokens_def Sel_is_selector
    is_selector_def by blast
  from 4 0 have sol5:"\<T>' k (Suc u) \<subseteq> \<T>' k (Suc (Suc u))" using Tokens_def Sel_is_selector
    is_selector_def by blast 
   have "  \<T>' k (Suc u) = Tokens k (\<T>' k u) (fst (\<J>' k u))" by auto
  with sol1 assms(4) have sol4:"\<T>' k (Suc u) = \<T> k (Suc u)" using 2 by force
  (*Token proofs*)
  show ?thesis using sol1 2 sol3  sol4 sol5 by blast
qed

thm "All_top_equality"

lemma \<J>_step_0:
  shows   "fst (\<J>' 0 u) = (\<J> 0 u) \<and> \<T>' 0 u = \<T>  0  u 
          \<and>  \<T>' 0  u \<subseteq> \<T>' 0  (Suc u) \<and> (\<T>' 0 (Suc u)) \<subseteq> TokensAt 0 (fst (\<J>' 0   u))"
proof (induct u)
  case 0
  with  \<I>'_invariants have 0:"fst (Init, (Map.empty, Map.empty)) = Init" by simp
  then have 1:"fst (Init, (Map.empty, Map.empty)) \<subseteq> All_top" by (simp add: Init_sub_All_top')
  have "\<T>' 0 0 = \<T> 0 0" by simp
  have 2:"fst (\<J>' 0 0) = \<J> 0 0 " using All_top_equality [OF _  _ 1 , where ?T="{}"] 0 by simp
  have "\<T>' 0 (Suc 0) = Sel {} (TokensAt 0 (fst (\<J>' 0 0)))" using Tokens_def by auto 
  then have "\<T>' 0 (Suc 0) \<subseteq> (TokensAt 0 (fst (\<J>' 0 0)))" 
      using Sel_is_selector is_selector_def by blast
  then show ?case using 2 by simp
next
  case (Suc u)
  then have "fst (\<J>' 0 u) \<subseteq> All_top" using \<I>_k_sub_All_top  \<J>_k_sub_\<I>_k  by blast
  with Suc  show ?case using \<J>_step_equality' [where ?k="0"] by blast
qed

lemma \<J>_step_equality'':
  assumes "(Suc k) \<le> length Doc"
  shows   "fst (\<J>' (Suc k) u) = (\<J> (Suc k) u) \<and> \<T>' (Suc k) u = \<T>  (Suc k)  u 
          \<and>  \<T>' (Suc k)  u \<subseteq> \<T>' (Suc k)  (Suc u) \<and> (\<T>' (Suc k) (Suc u)) \<subseteq> TokensAt (Suc k) (fst (\<J>' (Suc k)   u))"
proof (induct u)
  case 0
  with assms  \<I>'_invariants have 0:"fst (\<I>' k) = (\<I> k)" using \<I>'_pointer_invariants_def by simp
  then have 1:"fst (\<I>' k) \<subseteq> All_top" using Suc_leD \<I>_k_sub_All_top assms by blast
  have "\<T>' (Suc k) 0 = \<T> (Suc k) 0" by simp
  have 2:"fst (\<J>' (Suc k) 0) = \<J> (Suc k) 0 " 
    using All_top_equality [OF assms _ 1 , where ?T="{}"] 0 by simp
  have "\<T>' (Suc k) (Suc 0) = Sel {} (TokensAt (Suc k) (fst (\<J>' (Suc k) 0)))" using Tokens_def by auto 
  then have "\<T>' (Suc k) (Suc 0) \<subseteq> (TokensAt (Suc k) (fst (\<J>' (Suc k) 0)))" 
      using Sel_is_selector is_selector_def by blast
  then show ?case using 2 by simp
next
  case (Suc u)
  then have "fst (\<J>' (Suc k) u) \<subseteq> All_top" using \<I>_k_sub_All_top  \<J>_k_sub_\<I>_k assms by blast
  with Suc  show ?case using \<J>_step_equality' [OF assms] by metis
qed


lemma \<J>_step_eq:"k \<le> length Doc \<Longrightarrow> fst (\<J>' k u) = \<J> k u"
  apply(cases "k")
  using  \<J>_step_0 apply simp using \<J>_step_equality'' by blast



lemma Tokens_monotone:
  assumes "k \<le> length Doc "
  shows "(\<T>' k u)  \<subseteq> \<T>' k (Suc u) \<and> (\<T>' k (Suc u)) \<subseteq> TokensAt k (fst (\<J>' k  u))"
proof (induction u)
  case 0
  have 0:"{} \<subseteq> TokensAt k (fst (\<J>' k 0))" by blast
  have "\<T>' k (Suc 0) = Tokens k (\<T>' k 0) (fst (\<J>' k 0))" by simp
  then have "\<T>' k (Suc 0) = Sel  {} (TokensAt k (fst (\<J>' k 0)))" using Tokens_def by simp
  then have 1:"(\<T>' k (Suc 0)) \<subseteq>  TokensAt k (fst (\<J>' k   0))" using 
      Sel_is_selector is_selector_def 0 by blast
  with 1 show ?case by auto
next
  case (Suc u)
  then have 0:"\<T>' k (Suc (Suc u)) = Tokens k (\<T>' k (Suc u)) (fst (\<J>' k (Suc u)))" by force
  have "\<T>' k (Suc u) = Tokens k (\<T>' k u) (fst (\<J>' k  u))" by force
  then have 1:"\<T>' k (Suc u) \<subseteq> TokensAt k (fst (\<J>' k u))" using Suc by blast
  (*token mononicity*)
  have 3:"(fst (\<J>' k u)) = \<J> k u \<and> (fst (\<J>' k (Suc u))) = \<J> k (Suc u)" using \<J>_step_eq assms by blast 
  have "\<J> k u \<subseteq> \<J> k (Suc u)" using \<J>_subset_Suc_u by auto
  with 3 have  "(fst (\<J>' k u)) \<subseteq> (fst (\<J>' k (Suc u)))" by blast (*from monotonicity of step*)
  then have 2:"TokensAt k (fst (\<J>' k u)) \<subseteq> TokensAt k (fst (\<J>' k (Suc u)))" 
    by (meson mono_TokensAt mono_subset_elem subsetI)
  with 1 have "\<T>' k (Suc u) \<subseteq> TokensAt k (fst (\<J>' k (Suc u)))" by blast
  with  0 show ?case using Tokens_def [where ?k="k" and ?T="\<T>' k (Suc u)" 
        and ?I="(fst (\<J>' k (Suc u)))"] Sel_is_selector is_selector_def by blast 
qed

lemma TokensAt_finite:"k \<le> length Doc \<Longrightarrow> finite (TokensAt k I')"
  using TokensAt_invariants by blast
lemma Tokens_lex:"k \<le> length Doc \<Longrightarrow> \<forall>(t, c)\<in> (\<T>' k u). length c \<in> Lex t Doc k"
  using TokensAt_invariants Tokens_monotone by blast

lemma Tokens_lex_length:"k \<le> length Doc \<Longrightarrow> \<forall>(t, c)\<in> (\<T>' k u) . length c + k \<le> length Doc"
  using TokensAt_invariants Tokens_monotone  by fastforce 

lemma Tokens_terminal:"k \<le> length Doc \<Longrightarrow> \<forall>(t, c)\<in> (\<T>' k u) . is_terminal t" 
  using Tokens_monotone TokensAt_invariants by fast 

lemma Tokens0_finite:"finite (\<T>' k 0)"
  by auto
lemma Tokens_finite:"k \<le> length Doc \<Longrightarrow> finite (\<T>' k u)"
  using TokensAt_finite Tokens_monotone finite_subset Tokens0_finite by metis

lemma Tokens_finite_nonempty0:"(\<forall> (t, c) \<in> (\<T>' k 0) . 0 < length c)"
  by simp
lemma Tokens_finite_nonempty':"(\<forall> (t, c) \<in> (\<T>' k (Suc u)) . 0 < length c)"
  using Tokens_def Sel_is_nonempty non_empty_selector_def Tokens_finite by fastforce 

lemma Tokens_finite_nonempty:"k \<le> length Doc \<Longrightarrow> (\<forall> (t, c) \<in> (\<T>' k u) . 0 < length c) \<and> finite (\<T>' k u)"
  by (metis not0_implies_Suc Tokens_finite_nonempty' Tokens_finite_nonempty0 Tokens_finite)

lemma TokensAt_terminal:"\<forall>(t, c)\<in> TokensAt k I . is_terminal t"
  by (auto simp add: TokensAt_def)

lemma \<J>_step_equality''':
  assumes "k \<le> length Doc" "fst (\<J>' k u) = (\<J> k u)"  "fst (\<J>' k u) \<subseteq> All_top" "\<T>' k  u = \<T> k  u" " finite (fst (\<J>' k u))" 
          "\<T>' k  u \<subseteq> \<T>' k  (Suc u)" "(\<T>' k (Suc u)) \<subseteq> TokensAt k (fst (\<J>' k  u))"
        shows "fst (\<J>' k (Suc u)) = (\<J> k (Suc u)) \<and> \<T>' k  (Suc u) = \<T> k (Suc u) 
          \<and>  \<T>' k (Suc u) \<subseteq> \<T>' k  (Suc (Suc u)) \<and> (\<T>' k (Suc (Suc u))) \<subseteq> TokensAt k (fst (\<J>' k  (Suc u)))"
proof -
  have 0:"\<T>' k (Suc (Suc u)) = Tokens k (\<T>' k (Suc u)) (fst (\<J>' k (Suc u)))" by force
  have "\<T>' k (Suc u) = Tokens k (\<T>' k u) (fst (\<J>' k  u))" by force
  then have sub:"\<T>' k (Suc u) \<subseteq> TokensAt k (fst (\<J>' k u))" using assms by blast
  
  from TokensAt_invariants [OF assms(1), where ?I = "(fst (\<J>' k u))"] assms(7) have
    "(\<forall>(t, c)\<in> (\<T>' k (Suc u)). length c \<in> Lex t Doc k \<and> is_terminal t \<and> k + 
    length c \<le> length Doc) \<and> finite (\<T>' k (Suc u))" using finite_subset by blast
  then have val_lexing:"\<forall>(t, c)\<in> (\<T>' k (Suc u)) .  length c + k  \<le> length Doc" by auto

  have 1:"finite (\<T>' k (Suc u)) \<and> (\<forall>(t, c)\<in>\<T>' k (Suc u). 0 < length c)" 
    using Tokens_finite_nonempty assms(1) by blast
  with assms have 2:"\<T>' k (Suc u) = \<T> k (Suc u)" by force
  then have sol1:"fst (\<J>' k (Suc u)) = (\<J> k (Suc u))" using
       All_top_equality [OF  assms(1) , where ?T="\<T>' k (Suc u)" and ?I="(\<J>' k u)" ] assms(3) val_lexing
       assms by fastforce
  
  then have "fst (\<J>' k (Suc u)) = \<pi> k (\<T> k (Suc u)) (fst (\<J>' k u))" using assms(2) by auto
  then have "(fst (\<J>' k u)) \<subseteq> fst (\<J>' k (Suc u))" using \<pi>_monotone by presburger
  then have 3:"TokensAt k (fst (\<J>' k u)) \<subseteq> TokensAt k (fst (\<J>' k (Suc u)))" 
    by (meson mono_TokensAt mono_subset_elem subsetI)
  with sub have 4:"\<T>' k (Suc u) \<subseteq> TokensAt k (fst (\<J>' k (Suc u)))" by blast
  with 0 have sol3:"\<T>' k (Suc (Suc u)) \<subseteq> TokensAt k (fst (\<J>' k (Suc u)))" using Tokens_def Sel_is_selector
    is_selector_def by blast
  from 4 0 have sol5:"\<T>' k (Suc u) \<subseteq> \<T>' k (Suc (Suc u))" using Tokens_def Sel_is_selector
    is_selector_def by blast 
   have "  \<T>' k (Suc u) = Tokens k (\<T>' k u) (fst (\<J>' k u))" by auto
  with sol1 assms(4) have sol4:"\<T>' k (Suc u) = \<T> k (Suc u)" using 2 by force
  (*Token proofs*)
  show ?thesis using sol1 2 sol3  sol4 sol5 by blast
qed


lemma \<J>_step:
  assumes "k \<le> length Doc" "invariant_pointers (\<J>' k u)" "fst (\<J>' k u) = (\<J> k u)" "\<T>' k  u = \<T> k  u"
  shows "invariant_pointers (\<J>' k (Suc u)) \<and> fst (\<J>' k (Suc u)) = (\<J> k (Suc u)) \<and> \<T>' k  (Suc u) = \<T> k (Suc u)"
proof - 
  (*from assms finite_\<J>_k have 0:"finite (fst (\<J>' k (Suc u)))" by simp*)
  from assms have 1:"measure_help_monotone (snd(\<J>' k u))  
    \<and> red_complete (snd(\<J>' k u)) \<and> in_set (snd(\<J>' k u)) (fst(\<J>' k u)) \<and> invariant_pointers' (snd(\<J>' k u)) " 
    by (metis invariant_pointers.simps prod.collapse)
  have 2:"(\<forall> (t, c) \<in> (\<T>' k (Suc u)) . 0 < length c)"   
      using Tokens_finite_nonempty 
      apply simp  using Tokens_finite_nonempty assms by (metis \<T>'.simps(2))   
  from assms have "finite (fst (\<J>' k  u))" by (metis invariant_pointers.simps prod.collapse)
  then have 3:"finite (\<T>' k (Suc u)) \<and> finite (fst (\<J>' k  u))" using Tokens_finite_nonempty assms(1) by blast
  from assms have 4:"valid_bounds (fst (\<J>' k  u))" by (metis invariant_pointers.simps prod.collapse)
  from assms have 5:"valid_rule (fst (\<J>' k  u))" by (metis invariant_pointers.simps prod.collapse)
  from assms have 6:"dom_sup_items (snd(\<J>' k u)) (fst (\<J>' k u))" by (metis invariant_pointers.simps prod.collapse)

  (*should be proven differently from the invariants*)
  have 7:"\<forall>(t, c)\<in> (\<T>' k (Suc u)). length c \<in> Lex t Doc k" using Tokens_lex assms(1) by blast (*prove that it is smaller then this*)
  have 8:"\<forall>(t, c)\<in> (\<T>' k (Suc u)) . is_terminal t" using Tokens_terminal assms(1) by blast
  have val_lexing:"\<forall>(t, c)\<in> (\<T>' k (Suc u)) .  length c + k  \<le> length Doc" using Tokens_lex_length assms(1) by blast

  have val_lexing':"(\<forall>(t, c)\<in>(\<T>' k (Suc u)) . 0 < length c) \<and> (\<forall>(t, c)\<in>(\<T>' k (Suc u)) . length c \<in> Lex t Doc k)
       \<and> (\<forall>(t, c)\<in>(\<T>' k (Suc u)) . is_terminal t) \<and> finite (\<T>' k (Suc u))" using 3  7 8 2 by blast 
  from assms(2) have 10:"invariant_pointers (fst (\<J>' k u), snd (\<J>' k u))" by simp
  have All_top:"fst (\<J>' k u) \<subseteq> All_top" using assms \<I>_k_sub_All_top \<J>_k_sub_\<I>_k by blast
  from assms have 9:"dom_no_scan (snd(\<J>' k u)) (fst (\<J>' k u))" by (metis invariant_pointers.simps prod.collapse)
  have invariants:"invariant_pointers (\<pi>' k (\<T>' k (Suc u)) (fst (\<J>' k u), snd (\<J>' k u)))" 
    using \<pi>'_pointer_invariants [OF 10 val_lexing' assms(1)] All_top val_lexing
    by fastforce
  (*equality*)
 
  have 1:"finite (\<T>' k (Suc u)) \<and> (\<forall>(t, c)\<in>\<T>' k (Suc u). 0 < length c)" using Tokens_finite_nonempty assms(1) by blast
  with assms have tokens_eq:"\<T>' k (Suc u) = \<T> k (Suc u)" by force
  then have items_eq:"fst (\<J>' k (Suc u)) = (\<J> k (Suc u))" using 
      All_top_equality [OF  assms(1) , where ?T="\<T>' k (Suc u)" and ?I="(\<J>' k u)" ] All_top val_lexing
       assms by fastforce
  show ?thesis using \<J>'.simps(2) invariants tokens_eq items_eq  by force
qed

lemma \<J>_step_equality:
  assumes "k \<le> length Doc" "fst (\<J>' k u) = (\<J> k u)  " "\<T>' k  u = \<T> k  u" " finite (fst (\<J>' k u))" 
  shows "fst (\<J>' k (Suc u)) = (\<J> k (Suc u)) \<and> \<T>' k  (Suc u) = \<T> k (Suc u)"
proof -
  have All_top:"fst (\<J>' k u) \<subseteq> All_top" using assms \<I>_k_sub_All_top \<J>_k_sub_\<I>_k by blast
 from assms have 2:"\<T>' k (Suc u) = \<T> k (Suc u)" by force
  then have val_lexing:"\<forall>(t, c)\<in> (\<T>' k (Suc u)) .  length c + k  \<le> length Doc" 
    using Tokens_lex_length assms(1) by blast
 
  have 1:"finite (\<T>' k (Suc u)) \<and> (\<forall>(t, c)\<in>\<T>' k (Suc u). 0 < length c)" using Tokens_finite_nonempty assms(1) by blast
   then have "fst (\<J>' k (Suc u)) = (\<J> k (Suc u))" using 
       All_top_equality [OF  assms(1) , where ?T="\<T>' k (Suc u)" and ?I="(\<J>' k u)" ] All_top val_lexing
       assms by fastforce
  then show ?thesis using 2 by blast
qed



lemma \<I>_step:
  assumes "Suc k \<le> length Doc" "invariant_pointers (\<I>' k)" "fst (\<I>' k) = \<I> k"  
  shows "invariant_pointers (\<J>' (Suc k) 0) \<and> fst (\<J>' (Suc k) 0) = (\<J> (Suc k) 0) \<and> \<T>' (Suc k)  0 = \<T> (Suc k) 0"
proof - 
  from assms have 1:"measure_help_monotone (snd(\<I>' k ))  
    \<and> red_complete (snd(\<I>' k )) \<and> in_set (snd(\<I>' k )) (fst(\<I>' k )) \<and> invariant_pointers' (snd(\<I>' k )) 
  " 
    by (metis invariant_pointers.simps prod.collapse)
  have 2:"(\<forall> (t, c) \<in> {} . 0 < length c)"  by blast
  have 3:"finite {} \<and> finite (fst (\<I>' k ))" apply (cases "\<I>' k") using assms by auto
  from assms have 4:"valid_bounds (fst (\<I>' k))" by (metis invariant_pointers.simps prod.collapse)
  from assms have 5:"valid_rule (fst (\<I>' k))" by (metis invariant_pointers.simps prod.collapse)
  from assms have 6:"dom_sup_items (snd  (\<I>' k)) (fst (\<I>' k))" by (metis invariant_pointers.simps prod.collapse)
  from assms have 7:"dom_no_scan (snd  (\<I>' k)) (fst (\<I>' k))" by (metis invariant_pointers.simps prod.collapse)
  have 8:"\<forall>(t, c)\<in> {}. length c \<in> Lex t Doc (Suc k)"  by blast
  have All_top:"fst (\<I>' k) \<subseteq> All_top" using assms \<I>_k_sub_All_top by simp
  have val_lexing:"\<forall>(t, c)\<in> {} . (Suc k) + length c  \<le> length Doc" using Tokens_lex_length assms(1) by blast
 
  have ip:"invariant_pointers (fst (\<I>' k ), snd (\<I>' k ))" using assms(2) by simp
  from assms have "invariant_pointers (\<pi>' (Suc k) {} (fst (\<I>' k ), snd (\<I>' k )))"
    using \<pi>'_pointer_invariants [OF ip , where ?T="{}" and ?k="Suc k"] All_top val_lexing by blast
  then have invariants:"invariant_pointers (\<J>' (Suc k) 0)" using \<J>'.simps(3)[where ?k="k"] by simp
  (*equality*)
  have 9:"\<T>' (Suc k)  0 = \<T>' (Suc k) 0" by blast
 
  have "\<forall>(t, c)\<in>{}. 0 < length c" by blast
  then have items_eq:"fst (\<J>' (Suc k) 0) = (\<J> (Suc k) 0)" using
        All_top_equality [OF  assms(1) val_lexing All_top] assms by fastforce
  show ?thesis using  invariants items_eq  by auto
qed
(*central theorem of high importance*)
(*
  unnecessary now
*)
lemma \<I>_invar:
  "k \<le> length Doc \<Longrightarrow> invariant_pointers (\<I>' k) \<and> fst (\<I>' k ) = \<I> k"
  using \<I>'_invariants \<I>'_pointer_invariants_def by blast

theorem invariants:"invariant_pointers (I, (pred, red))"
  using \<I>_invar I_def pred_def red_def by fastforce

theorem item_equality:"I = \<I> (length Doc)"
  using \<I>_invar I_def by blast 

theorem I_finite: "finite I"
  using invariants by simp


theorem wf:"measure_help_monotone (pred, red)"
  using invariants by simp

theorem inset:"in_set (pred, red) I"
  using invariants by simp

theorem reduction_complete:"red_complete (pred, red)"
  using invariants by simp

theorem invariants':"invariant_pointers' (pred, red)"
  using invariants by simp
definition pointer_measure::"('a, 'b) item \<Rightarrow> nat" where
"pointer_measure i= measure_help (pred, red) i"

definition pointer_measure'::"('a, 'b) item \<Rightarrow> nat" where
"pointer_measure' i = (if i \<notin> I then 0 else (if i \<notin> (dom pred \<union> dom red) then 1 else snd (the ( pred i))))"

section "Pointer Invariants"

theorem pointer_wf:"\<forall> node \<in>  (dom pred) . pointer_measure node > pointer_measure (fst (the (pred node)))"
  using wf pointer_measure_def by auto
theorem pointer_wf':"\<forall> node \<in>  (dom red) . pointer_measure node > pointer_measure (fst (the (red node)))"
  using wf pointer_measure_def by auto

theorem pointer_wf'':"\<forall> node \<in>  (dom red) . node \<in> dom pred"
  using invariants by auto

lemma pred_inc:"\<forall> node \<in>  (dom pred) . item_dot node = (Suc (item_dot (fst (the (pred node)))))"
  using invariants by auto

lemma pred_rule:"\<forall> node \<in>  (dom pred) . item_rule node = item_rule (fst (the (pred node)))"
  using invariants by auto
lemma pred_in_Items:"\<forall> node \<in>  (dom pred) . (fst (the (pred node)))  \<in> I" 
proof -
  have "\<forall> node \<in>  (dom pred) . the (pred node) \<in> ran pred" apply(auto simp add: ran_def) done 
  then show ?thesis using inset by force
qed
lemma red_in_Items:"\<forall> node \<in>  (dom red) . (fst (the (red node)))  \<in> I" 
proof -
  have "\<forall> node \<in> (dom red). the (red node) \<in> ran red" by (auto simp add: dom_def ran_def)
  then show ?thesis using inset by force
qed

lemma red_complete:"\<forall> node \<in>  (dom red) . is_complete(fst (the (red node)))"
proof -
  have "\<forall> node \<in> (dom red). the (red node) \<in> ran red" by (auto simp add: ran_def)
  then show ?thesis using reduction_complete by force
qed


lemma red_is_pred_next:"\<forall> node \<in> (dom red) . next_symbol (fst (the (pred node))) = Some (item_nonterminal (fst (the (red node))))"
  using invariants by auto

lemma incomplete_implies_dot_le_rhs:"\<not> is_complete node \<Longrightarrow> item_dot node < length (item_rhs node)"
  by (auto simp add: is_complete_def)

lemma no_red_terminal_next:"\<forall> node \<in>  (dom pred) . node \<notin> (dom red) 
    \<longrightarrow> (\<exists> t . next_symbol (fst (the (pred node))) = Some t \<and> is_terminal t)"
  using invariants by simp
lemma pred_terminal:"\<forall> node \<in>  (dom pred) . node \<notin> (dom red) 
    \<longrightarrow> (item_rhs (fst (the (pred node)))) ! (item_dot (fst (the (pred node)))) \<in> \<TT>"
proof -
  from no_red_terminal_next have "\<forall> node \<in>  (dom pred) . node \<notin> (dom red) 
    \<longrightarrow> (\<exists> t . item_rhs (fst (the (pred node))) ! (item_dot (fst (the (pred node)))) =  t \<and> is_terminal t)" 
    by (metis next_symbol_not_complete option.sel next_symbol_def)
  then have "\<forall> node \<in>  (dom pred) . node \<notin> (dom red) 
    \<longrightarrow> is_terminal (item_rhs (fst (the (pred node))) ! (item_dot (fst (the (pred node)))))" by simp
  then show ?thesis by (meson is_terminal_')
qed

lemma pred_incomplete:"\<forall> node \<in>  (dom pred) . \<not> is_complete(fst (the (pred node)))" 
  by (metis red_is_pred_next  no_red_terminal_next  next_symbol_not_complete)(*should be a lemma from the next symbols*)


lemma pred_terminal':"node \<in>  (dom pred) \<and>  node \<notin> (dom red) 
    \<Longrightarrow> (item_rhs (fst (the (pred node)))) ! (item_dot (fst (the (pred node)))) \<in> \<TT>"
  using  pred_terminal by blast 

(*actual invariant*)
lemma dot0_if_no_pred:"node \<in> I \<Longrightarrow> node \<notin> (dom pred \<union> dom red) \<Longrightarrow> item_dot node = 0" 
  using invariants by auto

(*additional proof item_dot node = 0 \<Longrightarrow> item_end node = item_origin node \<longrightarrow> maybe just include*)
lemma no_scan_if_no_pred:"node \<in> I \<Longrightarrow> node \<notin> (dom pred \<union> dom red) \<Longrightarrow> 
  item_end node = item_origin node" 
  using invariants by auto(*proven from predict*)

lemma node_valid:"node \<in> I \<Longrightarrow> item_rule node \<in> \<RR>" 
  using invariants valid_rule_def by simp (*has to be proven differently*)

lemma next_lexes:"\<forall> x \<in> (dom pred) . x \<notin> dom red \<longrightarrow>
    is_lexed (fst (the (pred x))) x"
  using invariants by simp


lemma Item_bounds:"\<forall> i \<in> I. item_origin i \<le> item_end i" 
  using invariants valid_bounds_def by simp

lemma pred_item_bounds:"\<forall> x \<in> (dom pred) . item_origin x = item_origin (fst (the (pred x))) \<and> item_end x \<ge> item_end (fst (the (pred x)))"
  using invariants by simp

lemma bound_help:"(\<forall> x \<in> (dom pred) . item_origin x = item_origin (fst (the (pred x))) 
  \<and> item_end x \<ge> item_end (fst (the (pred x))) \<and> (\<forall> x \<in> (dom red) . item_origin (fst (the (red x))) = item_end (fst (the (pred x))) \<and> 
    item_end x = item_end (fst (the (red x)))))"
  using invariants by simp
lemma red_item_bounds:"\<forall> x \<in> (dom red) . item_origin (fst (the (red x))) = item_end (fst (the (pred x))) \<and>
    item_end x = item_end (fst (the (red x)))"
  using bound_help 
  by (meson pointer_wf'')



definition ms'::"(('a, 'b) item \<times> ('a, 'b) item ) set" where
"ms' = {(i, j) | i j . j \<in> (dom pred) \<and> i = fst (the (pred j))} "

lemma ms'_wf:"wf ms'"
proof -
  have 1:"\<forall> node . node \<in> (dom pred) \<longrightarrow> pointer_measure (fst (the (pred node))) < pointer_measure node" using pointer_wf by blast
  then show ?thesis using wf_if_measure [where ?P="(\<lambda> x. x \<in> (dom pred))" and ?f="pointer_measure" and ?g="\<lambda> x . (fst (the (pred x)))"] 
    by (smt (verit, ccfv_SIG) Collect_cong case_prodI2 ms'_def old.prod.case split_part)
qed
(*invariant \<Longrightarrow> for each item constructed tree + subtrees \<Longrightarrow>  valid until point*)
(*complete items imply correct tree*)
function build_tree::"('a, 'b) item \<Rightarrow> ('a, 'b) derivtree" where
"build_tree node  = (if (node \<notin> (dom pred \<union> dom red)) then (DT (item_rule node) []) else 
  (if (node \<in> dom red) then update_tree (build_tree (fst (the (pred node)))) (build_tree (fst (the (red node))))
       else update_tree (build_tree (fst (the (pred node)))) (Leaf (item_rhs 
  (fst (the (pred node))) ! (item_dot (fst (the (pred node))))))))"
   apply auto[1]
  by meson
termination proof (relation "measure pointer_measure", goal_cases)
case 1
  then show ?case (*why no measure?*) by auto
    (*by (auto simp add: pointer_measure_def pointer_wf)*)
next
  case (2 node)
  then show ?case
    by (simp add: pointer_wf pointer_wf'')
next
  case (3 node)
  then show ?case 
    using pointer_wf' by auto
next
  case (4 node)
  then show ?case 
    using pointer_wf by auto
qed

fun valid_tree::"('a, 'b) derivtree \<Rightarrow> bool" where
"valid_tree (Leaf a) = (a \<in> \<TT>)"|
"valid_tree (DT r b) = ((r \<in> \<RR>) \<and>  list_all valid_tree b \<and> (map (\<lambda> t. fst (DeriveFromTree t)) b)  = snd r) "|
"valid_tree _ = False"
fun valid_tree_k::"nat \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"valid_tree_k _ (Leaf a) = (a \<in> \<TT>)"|
"valid_tree_k k (DT r b) = ((r \<in> \<RR>) \<and> list_all valid_tree b \<and> (map (\<lambda> t. fst (DeriveFromTree t)) b)  = take k (snd r))"|
"valid_tree_k _  _ = False"


lemma valid_tree_k_implies_valid_tree:"valid_tree_k (length (snd r))  (DT r b) \<Longrightarrow> valid_tree (DT r b)"
  by simp

lemma valid_tree_k_implies_valid_tree':"k \<ge> length (snd r) \<Longrightarrow> valid_tree_k k  (DT r b) \<Longrightarrow> valid_tree (DT r b)"
  by simp


lemma update_valid_tree_k_tree:
  assumes "valid_tree_k k (DT r b)" "length b = k" " valid_tree T" "fst (DeriveFromTree T) = (snd r) ! k" "k < length (snd r)"
  shows "valid_tree_k (Suc k) (update_tree (DT r b) T)"
  
proof -
  from assms have 1:"r \<in> \<RR>" by simp
  from assms have 2:"(map (\<lambda> t. fst (DeriveFromTree t)) b)  = take k (snd r)" by simp
  from assms have "fst (DeriveFromTree T) = snd r ! k" by simp
  obtain bnew where 3:"bnew = b@[T]" by blast
  then have 4:"list_all valid_tree bnew" using assms by simp
  from 2 3 have "(map (\<lambda> t. fst (DeriveFromTree t)) bnew)  = (take k (snd r))@[fst (DeriveFromTree T)]" by simp
  with assms have 5:"(map (\<lambda> t. fst (DeriveFromTree t)) bnew)  = (take (Suc k) (snd r))" 
    using take_Suc_conv_app_nth by metis
  have "(update_tree (DT r b) T) = DT r bnew" using 3 by auto
  then show ?thesis using 1 4 5 by simp
qed

(*another proof \<Longrightarrow> complete trees can only be reduced too*)
definition easy_prec::"(('a, 'b) item  \<times> ('a, 'b) item) set" where
 "easy_prec = measure pointer_measure"

theorem easy_prec:"wf easy_prec"
  using pointer_measure_def easy_prec_def by simp

definition prec::"(('a, 'b) item  \<times> ('a, 'b) item) set" where
 "prec = {(i, j) | i j . pointer_measure i < pointer_measure j \<and> ((j \<in> (dom pred) \<and> i = fst (the (pred j))) \<or> 
  (j \<in> (dom red) \<and> i = fst (the (red j))))}"

theorem wf_prec:"wf prec"
proof -
  have "prec \<subseteq> easy_prec" by (auto simp add: prec_def easy_prec_def)
  then show ?thesis using easy_prec 
    by (meson wf_subset)
qed
lemma build_tree_rule:
  shows"i \<in> I \<Longrightarrow>\<exists> b .  build_tree i = (DT (item_rule i) b) \<and> fst (DeriveFromTree (build_tree i)) 
  = item_nonterminal i \<and> length b = item_dot i"
proof (induction "i"  rule: wf_induct [where ?r="prec"])
  case 1
  then show ?case using wf_prec by simp
next
  case (2 x)
  then have x_in_I:"x \<in> I" by blast
  { assume a:"x \<notin> dom pred \<union> dom red"
    then have 0:"item_dot x = 0" using dot0_if_no_pred x_in_I by blast 
    from a have 1:"build_tree x = (DT (item_rule x) [])" by auto
    then have "fst (DeriveFromTree (DT (item_rule x) [])) = (fst (item_rule x))" by simp
    with 1 have "fst (DeriveFromTree (build_tree x)) = item_nonterminal x \<and> build_tree x = (DT (item_rule x) [])" 
      by (metis item_nonterminal_def)
    then  have "\<exists> b . fst (DeriveFromTree (build_tree x)) = item_nonterminal x \<and> build_tree x = (DT (item_rule x) b) \<and> length b = item_dot x" 
      by (auto simp add: 0)
  }
  then have  case1:"x \<notin> dom pred \<union> dom red \<Longrightarrow>
    \<exists> b . fst (DeriveFromTree (build_tree x)) = item_nonterminal x 
  \<and> build_tree x = (DT (item_rule x) b) \<and> length b = item_dot x" by blast
  {
    assume 0:"x \<in> dom red"
    then have 1:"x \<in> dom pred" using pointer_wf'' by auto
    (*Predecessor Tree*)
    then obtain prednode where prednode:"prednode =  fst (the (pred x))" by blast
    with 1 have prednode':"(prednode, x) \<in> prec" using  pointer_wf 
      by (simp add: prec_def)
    from prednode 1 have prednode_in_I:"prednode \<in> I" 
      by (simp add: pred_in_Items) 
    obtain rednode where rednode:"rednode = fst (the (red x))" by blast
    with 0 have "(rednode, x) \<in> prec" using pointer_measure_def using pointer_wf' by (simp add: prec_def)
    from 0 1 prednode rednode have x:"build_tree x = update_tree (build_tree prednode) (build_tree rednode)" by auto
    from 2 prednode' prednode_in_I obtain 
        b where predtree:"build_tree prednode = (DT (item_rule prednode) b)" by blast
    then have x':"build_tree x = (DT (item_rule prednode) (b@[(build_tree rednode)]))" using x by simp
    from prednode 1 have eq:"item_rule x = item_rule prednode" using pred_rule by blast
    have "item_dot x = (Suc (item_dot prednode))" using pred_inc 1 prednode by blast
    then have length:"item_dot x = length (b@[(build_tree rednode)])" using 2 prednode' predtree prednode_in_I by auto
  
    from  x' eq have "build_tree x = (DT (item_rule x) (b@[(build_tree rednode)]))" by auto
    then have "fst (DeriveFromTree (build_tree x)) =(fst (item_rule x))" by simp
    then have "\<exists> b . fst (DeriveFromTree (build_tree x)) = item_nonterminal x \<and> 
      build_tree x = (DT (item_rule x) b) \<and> length b = item_dot x" using length x' item_nonterminal_def 
      by (metis eq)
  }
  then have case2:"x \<in> dom red \<Longrightarrow> \<exists>b. fst (DeriveFromTree (build_tree x)) 
  = item_nonterminal x \<and> build_tree x = DT (item_rule x) b \<and> length b = item_dot x" by blast
  {
    assume 0:"x \<in> dom pred \<and> x \<notin> dom red"
   (*Predecessor Tree*)
    then obtain prednode where prednode:"prednode =  fst (the (pred x))" by blast
    with 0 have prednode':"(prednode, x) \<in> prec" using pointer_measure_def pointer_wf by (simp add: prec_def)
    from 0 have prednode_in_I:"prednode \<in> I" 
      by (simp add: pred_in_Items prednode)
    obtain T where T_def:"T = Leaf ((item_rhs prednode) ! (item_dot prednode))" by blast
    
    then have match:"fst (DeriveFromTree T) = (item_rhs prednode) ! (item_dot prednode)" by simp
    with 0  prednode  have x:"build_tree x = update_tree (build_tree prednode) T" using T_def by auto 
    from 2 prednode' prednode_in_I obtain  b where predtree:"build_tree prednode = (DT (item_rule prednode) b)" by blast
    then have x':"build_tree x = (DT (item_rule prednode) (b@[T]))" using x by simp
    from prednode 0 have eq:"item_rule x = item_rule prednode" using pred_rule by blast
    have "item_dot x = (Suc (item_dot prednode))" using pred_inc 0 prednode by blast
    then have length:"item_dot x = length (b@[T])" using 2 prednode' predtree prednode_in_I by auto
  
    from  x' eq have "build_tree x = (DT (item_rule x) (b@[T]))" by auto
    then have "fst (DeriveFromTree (build_tree x)) =(fst (item_rule x))" by simp
    then have "\<exists> b . fst (DeriveFromTree (build_tree x)) = item_nonterminal x \<and> 
      build_tree x = (DT (item_rule x) b) \<and> length b = item_dot x" using length x' item_nonterminal_def 
      by (metis eq)
  }
  then show ?case using case1 case2 by blast
qed
 (*proved by induction on pred*)

lemma build_tree_rule':"i \<in> I \<Longrightarrow> fst (DeriveFromTree (build_tree i)) = item_nonterminal i"
  using build_tree_rule by blast


lemma complete_item_implies_valid_tree:
  assumes "is_complete i "" i \<in> I" "valid_tree_k (item_dot i) (build_tree i)"
  shows " valid_tree (build_tree i)"
proof -
  from build_tree_rule obtain b where 0:"build_tree i = (DT (item_rule i) b)" using assms by blast
  from assms have "item_dot i \<ge> length (snd (item_rule i))" using is_complete_def item_rhs_def by metis
  with 0 valid_tree_k_implies_valid_tree assms show ?thesis by auto
qed


theorem build_tree_valid:
  shows "node \<in> I \<Longrightarrow> valid_tree_k (item_dot node) (build_tree node)" 
proof (induction "node" rule: wf_induct [where ?r="prec"])
  case 1
then show ?case using wf_prec by simp
next
  case (2 x)
  then have x_in_I:"x \<in> I" by blast
  { assume a:"x \<notin> dom pred \<union> dom red"
    then have 0:"item_dot x = 0" using dot0_if_no_pred x_in_I by blast 
    from a have 1:"build_tree x = (DT (item_rule x) [])" by auto
    have 2:"item_rule x \<in> \<RR>" 
      using x_in_I  node_valid by auto
    have 3:"list_all valid_tree []" by simp
    have "(map (\<lambda> t. fst (DeriveFromTree t)) []) = take 0 (snd (item_rule node))" by simp
    then have "valid_tree_k (item_dot x) (build_tree x)" using 0 1 2 3 by simp 
  }
  then have case1:" x \<notin> dom pred \<union> dom red \<Longrightarrow> valid_tree_k (item_dot x) (build_tree x) " by blast
  {
    assume 0:"x \<in> dom red"
    then have 1:"x \<in> dom pred" using pointer_wf'' by auto
    (*Predecessor Tree*)
    then obtain prednode where prednode:"prednode =  fst (the (pred x))" by blast
    then have prednode_in_I:"prednode \<in> I" 
      by (simp add: 1 pred_in_Items)
    with 1 have "(prednode, x) \<in> prec" using pointer_wf 
      by (simp add: prec_def prednode)
    with 2  prednode_in_I have validk_pred:"valid_tree_k (item_dot prednode) (build_tree prednode)" by blast
    from 1 prednode have pred_assms:"prednode \<in> I \<and> (item_dot prednode) < length (item_rhs prednode)" 
      by (simp add: incomplete_implies_dot_le_rhs pred_in_Items pred_incomplete)(*one assumption to be proven, and incompleteness*)
    then obtain b where b:"build_tree prednode = (DT (item_rule prednode) b) 
      \<and> (item_dot prednode) = length b" using build_tree_rule by metis
    (*Reduction Tree*)
    obtain rednode where rednode:"rednode = fst (the (red x))" by blast
    then have rednode_in_I:"rednode \<in> I" by (simp add: 0 red_in_Items)
    with 0 have "(rednode, x) \<in> prec" using pointer_measure_def using pointer_wf' 
      using prec_def rednode by auto
    with 2 rednode_in_I have redval:"valid_tree_k (item_dot rednode) (build_tree rednode)" by blast
    
    have red_assms:"rednode \<in> I \<and> is_complete rednode 
    \<and> next_symbol prednode = Some (item_nonterminal rednode)" 
        by (simp add: 0 red_complete red_is_pred_next prednode rednode red_in_Items)   (*from reduction assumptions*)
    obtain T where T_def:"T = build_tree rednode" by blast
    with red_assms redval have T_valid:"valid_tree T" using complete_item_implies_valid_tree by blast
    from red_assms have match:"fst (DeriveFromTree T) = item_nonterminal rednode" 
      using T_def build_tree_rule' by blast
    from red_assms have match':"item_nonterminal rednode = item_rhs prednode ! (item_dot prednode)" 
      by (metis next_symbol_def next_symbol_not_complete option.inject)
    (*Compose trees*)
    have "build_tree x = update_tree (build_tree (fst (the (pred x)))) (build_tree (fst (the (red x))))" using 0 1 by simp
    then have "build_tree x = update_tree (build_tree prednode) T" using prednode T_def rednode by auto
    then have valid_x:"valid_tree_k (Suc (item_dot prednode)) (build_tree x)" using update_valid_tree_k_tree 
          b validk_pred  T_valid match
      by (metis match' item_rhs_def pred_assms)
    from 1 have "item_dot x = Suc (item_dot prednode)" using pred_inc prednode by blast
    with valid_x have "valid_tree_k (item_dot x) (build_tree x)" by simp 
  }
  then have case2:"x \<in> dom red \<Longrightarrow> valid_tree_k (item_dot x) (build_tree x)" by blast
  {
    assume 0:"x \<notin> dom red \<and> x \<in> dom pred"
       (*Predecessor Tree*)
    then obtain prednode where prednode:"prednode =  fst (the (pred x))" by blast
    with 0 have 1:"(prednode, x) \<in> prec" using pointer_measure_def pointer_wf 
      using prec_def by auto
    then have prednode_in_I:"prednode \<in> I" 
      by (simp add: 0 pred_in_Items prednode)
    with 2  1 have validk_pred:"valid_tree_k (item_dot prednode) (build_tree prednode)" by blast
    from 0 prednode have pred_assms:"prednode \<in> I \<and> (item_dot prednode) < length (item_rhs prednode)"
      using pred_in_Items pred_incomplete
      by (simp add: incomplete_implies_dot_le_rhs)  (*one assumption to be proven, and incompleteness*)
    then obtain b where b:"build_tree prednode = (DT (item_rule prednode) b) \<and> (item_dot prednode) = length b" using build_tree_rule by metis

    (*Leaf*)
    obtain T where T_def:"T = Leaf ((item_rhs prednode) ! (item_dot prednode))" by blast
    then have match:"fst (DeriveFromTree T) = (item_rhs prednode) ! (item_dot prednode)" by simp
    from 0 have "(item_rhs prednode) ! (item_dot prednode) \<in> \<TT>" using pred_terminal' prednode by auto
      
        (*Scan assumption*) 
    with T_def have valid_T:"valid_tree T" by auto 

        (*Compose trees*)
    from 0 have "x \<in> (dom red \<union> dom pred) \<and> x \<notin> (dom red)" by auto
    then have "build_tree x = update_tree (build_tree (fst (the (pred x)))) 
    (Leaf (item_rhs (fst (the (pred x))) ! (item_dot (fst (the (pred x))))))" by (auto simp del: build_tree.simps simp add: build_tree.simps [of x])  
    (*if else nesting gives issues*)
    then have "build_tree x = update_tree (build_tree prednode) T" using prednode T_def by auto
      
    then have valid_x:"valid_tree_k (Suc (item_dot prednode)) (build_tree x)" using update_valid_tree_k_tree 
          b validk_pred  valid_T match
      by (metis  item_rhs_def pred_assms)
    from 0 have "item_dot x = Suc (item_dot prednode)" using prednode pred_inc by blast
    with valid_x have "valid_tree_k (item_dot x) (build_tree x)" by simp 
  }
  then have case3:"x \<notin> dom red \<and> x \<in> dom pred \<Longrightarrow> valid_tree_k (item_dot x) (build_tree x)" by blast
  then show ?case using case1 case2 case3 by blast
qed 

theorem complete_implies_valid_tree:
  "node \<in> I \<Longrightarrow> is_complete node \<Longrightarrow> valid_tree (build_tree node)"
  using build_tree_valid complete_item_implies_valid_tree by blast


(*technically a lexer is only defined on the nats in the substring of doc*)

fun lexes'::"nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) symbol  \<Rightarrow> bool" where
"lexes' k l b =  ((l-k ) \<in> (Lex b Doc k))"

fun subdivision::"nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool" where
"subdivision k l b = ((k = fst (hd b )) \<and> (l = snd (last b )) \<and> (\<forall> (l, k) \<in> set b . l \<le> k )
  \<and> (tl (map fst b) = butlast (map snd b)))"

lemma subdivision_singleton:"k \<le> l \<Longrightarrow> subdivision k l [(k, l)]" by auto
lemma subdivision_append:
  assumes "l\<le> h" " subdivision k l sd" "sd \<noteq> []"
  shows "subdivision k h (sd@[(l, h)])" 
proof -
  have 1:"k = fst( hd (sd@[(l, h)]))" using assms by simp
  have 2:"h = snd (last (sd@[(l, h)]))" by simp
  have 3:"(\<forall> (l, k) \<in> set (sd@[(l, h)]) . l \<le> k )" using assms by simp
  have 4:"(tl (map fst (sd@[(l, h)]))) = (tl (map fst (sd)))@[l]" using assms by simp
  have "last (map snd sd) = snd (last sd)" using assms 
    by (meson last_map) 
  then have l_last:"last (map snd sd) = l" using assms by auto
  have 5:"butlast (map snd (sd@[(l, h)])) = map snd sd" by auto
  with assms have 6:"map snd sd = (butlast (map snd sd))@[l]"  using l_last
    by (metis Nil_is_map_conv append_butlast_last_id)
  with 4 5 have "(tl (map fst (sd@[(l, h)]))) = butlast (map snd (sd@[(l, h)]))" using assms by auto
  with 1 2 3 show ?thesis by auto
qed


fun tree_parses'::"nat \<times>  nat \<Rightarrow> ('a, 'b) derivtree \<Rightarrow> bool" where
"tree_parses' (k, l) (Leaf a) = lexes' k l a"|
"tree_parses' (k, l) (DT r []) =  (k = l)"|
"tree_parses' (k, l) (DT r b) = (\<exists> s . subdivision k l s \<and> list_all2 tree_parses' s b)"|
"tree_parses' _ _ = False"

(*Alternative proof based on subdivisions*)
theorem build_tree_valid_parse':
  shows "node \<in> I \<Longrightarrow> tree_parses' ((item_origin node), (item_end node)) (build_tree node) " (*might have to add an minimum*)
proof (induction "node" rule: wf_induct [where ?r="prec"])
  case 1
  then show ?case 
    using wf_prec by blast
next
  case (2 x)
  then have x_in_I:"x \<in> I" by simp
  { assume a:"x \<notin> dom pred \<union> dom red"
    then have 0:"item_end x = item_origin x" using no_scan_if_no_pred x_in_I by blast 
    from a have 1:"build_tree x = (DT (item_rule x) [])" by auto
    with 0 1 have "tree_parses' (item_origin x, item_end x) (build_tree x)" by simp
  }
  then have case1:"x \<notin> dom pred \<union> dom red \<Longrightarrow> ?case" by blast
  { (*reduction case*)
    assume 0:"x \<in> dom red"
    then have 1:"x \<in> dom pred" using pointer_wf'' by auto
    then obtain prednode where prednode:"prednode =  fst (the (pred x))" by blast
    then have prednode_in_I:"prednode \<in> I" 
      using 1 pred_in_Items by blast (*already proved*)
    with 1 have "(prednode, x) \<in> prec" using pointer_measure_def pointer_wf 
      using prec_def prednode by auto
    with 2 prednode_in_I have pred_parses:
        "tree_parses' (item_origin prednode, item_end prednode) (build_tree prednode) " by blast

    (*Reduction Tree*)
    obtain rednode where rednode:"rednode = fst (the (red x))" by blast
    then have rednode_in_I:"rednode \<in> I" using 0 red_in_Items by blast
    with 0 have "(rednode, x) \<in> prec" using pointer_measure_def  pointer_wf'
      using prec_def rednode by auto
    with 2 rednode_in_I have red_parses:"tree_parses' ((item_origin rednode), (item_end rednode))
      (build_tree rednode)" by blast
    
    have red_assms:"rednode \<in> I \<and> is_complete rednode 
    \<and> next_symbol prednode = Some (item_nonterminal rednode)" 
        by (simp add: 0 red_complete red_is_pred_next prednode rednode red_in_Items)   (*from reduction assumptions*)
    obtain T where T_def:"T = build_tree rednode" by blast
    (*obtain predecessor tree*)

    from 1 prednode have pred_assms:"prednode \<in> I \<and> (item_dot prednode) < length (item_rhs prednode)"
      by (simp add: incomplete_implies_dot_le_rhs pred_in_Items pred_incomplete)(*one assumption to be proven, and incompleteness*)
    then obtain b where b:"build_tree prednode = (DT (item_rule prednode) b) 
      \<and> (item_dot prednode) = length b" using build_tree_rule by metis

    (*Compose trees*) 
    have "build_tree x = update_tree (build_tree prednode) T" using prednode T_def 0
      using 1  rednode  by simp
    then have tree_def:"build_tree x = (DT (item_rule prednode) (b@[T]))" using b by auto

    (*case distinction on predecessor*)
    have ?case 
    proof (cases "b \<noteq> []")
      case True
        have "tree_parses' (item_origin prednode, item_end prednode) (DT (item_rule prednode) b) " 
          using pred_parses b by simp
        then have "(\<exists> s . subdivision (item_origin prednode) (item_end prednode) 
          s \<and> list_all2 tree_parses' s b)" using True  tree_parses'.elims(2) by fastforce
        then obtain sd where sd:"subdivision (item_origin prednode) (item_end prednode) sd
          \<and> list_all2 tree_parses' sd b" by blast
        have nonempty:"b@[T] \<noteq> []" by simp
    (*most important assumption*)
        from 0 1 prednode rednode have eq:"item_origin rednode = item_end prednode \<and> item_end rednode = item_end x
              \<and> item_origin x = item_origin prednode \<and> item_end x \<ge> item_end prednode"
          by (metis  pred_item_bounds red_item_bounds) 
        
        
        then have subdiv:"subdivision (item_origin prednode) (item_end rednode)
            (sd@[(item_origin rednode, item_end rednode)])" using subdivision_append sd 
          by (metis True  list_all2_Nil)
        have parses:"list_all2  tree_parses' (sd@[(item_origin rednode, item_end rednode)]) (b@[T])" 
          using red_parses T_def pred_parses 
            by (metis sd list.ctr_transfer(1) list_all2_Cons list_all2_appendI)
        with subdiv eq have "\<exists> s . subdivision (item_origin x) (item_end x) s \<and> list_all2 tree_parses' s (b@[T])" by metis
        with tree_def show ?thesis using nonempty
            by (metis neq_Nil_conv tree_parses'.simps(3))
    next
      case False
        have "tree_parses' (item_origin prednode, item_end prednode) (DT (item_rule prednode) b) " 
          using pred_parses b by simp
        then have eq':"item_origin prednode = item_end prednode" using False tree_parses'.elims(2) by simp
        (*most important assumption*)
        from 0  1 prednode rednode have eq:"item_origin rednode = item_end prednode \<and> item_end rednode = item_end x
          \<and> item_origin x = item_origin prednode \<and> item_end x \<ge> item_end prednode
          " by (metis pred_item_bounds red_item_bounds )
        then have eq'':"item_origin x \<le> item_end x"  using Item_bounds prednode prednode_in_I by auto
        obtain sd where sd:"sd = [(item_origin x, item_end x)]" by blast
        then have sd':"subdivision (item_origin x) (item_end x) sd" using eq eq'' using subdivision_singleton by blast 
        from eq eq' have "tree_parses' ((item_origin x) ,(item_end x)) T" using T_def red_parses by simp
        then have subtree_parses:"list_all2 tree_parses' sd [T]" using sd by simp        
        from False have "b@[T] = [T]" by simp
      then show ?thesis using tree_def sd' subtree_parses by auto
    qed
  }
  then have case2:"x \<in> dom red \<Longrightarrow> ?case" by blast
  {
    assume 0:"x \<notin> dom red \<and> x \<in> dom pred"
       (*Predecessor Tree*)
    then obtain prednode where prednode:"prednode =  fst (the (pred x))" by blast
    then have prednode_in_I:"prednode \<in> I" 
      by (simp add: 0 pred_in_Items)
    with 0 have "(prednode, x) \<in> prec" using pointer_wf prec_def prednode by auto
    with 2 prednode_in_I have pred_parses:
        "tree_parses' (item_origin prednode, item_end prednode) (build_tree prednode) " by blast
    (*Leaf*)
    obtain T where T_def:"T = Leaf ((item_rhs prednode) ! (item_dot prednode))" by blast
    then have match:"fst (DeriveFromTree T) = (item_rhs prednode) ! (item_dot prednode)" by simp
    from 0 have "(item_rhs prednode) ! (item_dot prednode) \<in> \<TT>" using pred_terminal' prednode by auto
      
    (*Scan assumption*)
    from 0 next_lexes have " x \<notin> dom red \<Longrightarrow> is_lexed (fst (the (pred x))) x" by simp
    with 0 next_lexes prednode have "is_lexed prednode x" by blast 
       (*assumption here*)
    then have T_parses:"lexes' (item_end prednode) 
        (item_end x) ((item_rhs prednode) ! (item_dot prednode))" using is_lexed_def by auto
    then have T_parses':"tree_parses' (item_end prednode, item_end x) T" using T_def by simp
    

(*obtain predecessor tree*)
    from 0 prednode have pred_assms:"prednode \<in> I \<and> (item_dot prednode) < length (item_rhs prednode)"
      by (simp add: incomplete_implies_dot_le_rhs pred_in_Items pred_incomplete)(*one assumption to be proven, and incompleteness*)
    then obtain b where b:"build_tree prednode = (DT (item_rule prednode) b) 
      \<and> (item_dot prednode) = length b" using build_tree_rule by metis
    have pred_parses':"tree_parses' (item_origin prednode, item_end prednode) (DT (item_rule prednode) b) " 
      using pred_parses b by simp
    from 0 have "x \<in> (dom red \<union> dom pred) \<and> x \<notin> (dom red)" by auto
    then have "build_tree x = update_tree (build_tree (fst (the (pred x)))) 
    (Leaf (item_rhs (fst (the (pred x))) ! (item_dot (fst (the (pred x))))))" 
      by (auto simp del: build_tree.simps simp add: build_tree.simps [of x])
    then have "build_tree x = update_tree (build_tree prednode) T" using prednode T_def by auto
    then have tree_x:"build_tree x = (DT (item_rule prednode) (b@[T]))" using T_def b by auto
    
    have ?case
    proof (cases "b \<noteq> []")
      case True
      then have "(\<exists> s . subdivision (item_origin prednode) (item_end prednode) 
        s \<and> list_all2 tree_parses' s b)" using pred_parses' tree_parses'.elims(2) by fastforce
      then  obtain sd where sd:"subdivision (item_origin prednode) (item_end prednode) sd
          \<and> list_all2 tree_parses' sd b" by blast
      from 0 prednode have eq:"item_origin x = item_origin prednode \<and> item_end prednode \<le> item_end x" 
        using pred_item_bounds by blast
      (*Compose trees*)
      have subtrees_nonempty:"b@[T] \<noteq> []" by blast
      have subdiv:"subdivision (item_origin x) (item_end x) (sd@[(item_end prednode, item_end x)])"
        using subdivision_append sd eq 
        by (metis True list_all2_Nil)
      then have "list_all2 tree_parses' (sd@[(item_end prednode, item_end x)]) (b@[T])" using sd T_parses' 
          by (simp add: list_all2_appendI)
      then show ?thesis  using subdiv tree_x subtrees_nonempty 
      by (metis list.exhaust tree_parses'.simps(3))
    next
      case False
      have "tree_parses' (item_origin prednode, item_end prednode) (DT (item_rule prednode) b) " 
          using pred_parses b by simp
        then have eq':"item_origin prednode = item_end prednode" using False tree_parses'.elims(2) by simp
        (*most important assumption*)
        from 0 prednode have eq:"item_origin x = item_origin prednode \<and> item_end x \<ge> item_end prednode
        \<and> item_origin x \<le> item_end x" 
          using Item_bounds pred_item_bounds x_in_I by blast 
        obtain sd where sd:"sd = [(item_origin x, item_end x)]" by blast
        then have sd':"subdivision (item_origin x) (item_end x) sd" using eq subdivision_singleton by blast
        from eq eq' have "tree_parses' ((item_origin x) ,(item_end x)) T" using T_def T_parses' by simp
        then have subtree_parses:"list_all2 tree_parses' sd [T]" using sd by simp        
(**)
        from False have "b@[T] = [T]" by simp
        then show ?thesis using sd' subtree_parses tree_x by auto
    qed
  }
  then show ?case using case1 case2 by blast
qed
term "is_finished"

definition select_item::"('a, 'b) item set \<Rightarrow> ('a, 'b) item option" where
"select_item r = (case csorted_list_of_set (Set.filter is_finished r) of [] \<Rightarrow> None | x#xs \<Rightarrow> Some x)"

lemma select_item_is_finished:
  assumes "select_item r = Some i " "finite r"
  shows "is_finished i \<and> i \<in> r" 
proof -
  from assms have 1:"finite (Set.filter is_finished r)" by simp
  from assms select_item_def obtain xs 
     where 2:"i#xs = csorted_list_of_set (Set.filter is_finished r)" 
    by (metis (no_types, lifting) list.exhaust list.simps(4) list.simps(5) option.distinct(1) option.inject)
  have "i \<in> (Set.filter is_finished r)" using csorted_set'' [OF 1] arg_cong [where ?f="set", OF 2]  by auto 
  then show ?thesis by simp
qed

definition T::"('a, 'b) derivtree option" where
"T = (case (\<I>' (length Doc)) of (I', p) \<Rightarrow> map_option build_tree (select_item I'))"

lemma 
  assumes "T = None "
  shows "\<not>earley_recognised" 
proof -
  have 1:"finite (\<I> (length Doc))" using item_equality I_finite by simp
  then have 1:"finite (Set.filter is_finished (\<I> (length Doc)))" by simp
  { 
    assume "earley_recognised"
    then have "\<exists> i \<in> (\<I> (length Doc)) . is_finished i" using earley_recognised_def \<II>_def by blast
    then have "(Set.filter is_finished (\<I> (length Doc))) \<noteq> {}" by auto
    then have "\<exists> x xs . x#xs=  csorted_list_of_set (Set.filter is_finished (\<I> (length Doc)))" using csorted_set'' [OF 1] 
      by (metis Collect_mem_eq empty_Collect_eq list.set_cases)
    then have "\<exists> t . select_item (\<I> (length Doc)) = Some t" by (auto simp add: select_item_def split: list.splits) 
    with item_equality I_def have "\<exists> t . T = map_option build_tree (Some t)"  
      by (auto simp del: build_tree.simps simp add: T_def split: prod.splits) 
    then have "T \<noteq> None" by auto
  }
  then show ?thesis using assms by blast
qed
lemma 
  assumes "T = (Some t) " 
  shows  "earley_recognised \<and> valid_tree t \<and> tree_parses' (0, (length Doc)) t"
proof -
  have 0:"finite I" by (simp add: I_finite)
  from assms have "T = map_option build_tree (select_item I)" apply (cases "(\<I>' (length Doc))") using T_def I_def by auto
  with assms have " (\<exists>i. select_item I = Some i \<and> build_tree i = t)" using map_option_eq_Some by simp
  then obtain i  where "Some i = select_item I" and t:"build_tree i = t" by fastforce
  then have 1:"is_finished i \<and> i \<in> I" using select_item_is_finished 0 by simp
  with t have valid:"valid_tree t" using complete_implies_valid_tree is_finished_def by blast 
  from build_tree_valid_parse' 1 have parse:"tree_parses' (0, (length Doc)) t" using is_finished_def t by metis
  from 1 have "earley_recognised" using earley_recognised_def \<II>_def item_equality by blast
  with valid parse show ?thesis by blast
qed
end

end