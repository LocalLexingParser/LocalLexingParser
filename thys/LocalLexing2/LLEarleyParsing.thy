theory LLEarleyParsing 
imports LocalLexing "HOL-Library.While_Combinator"
begin

datatype ('a, 'b) item = 
  Item 
    (item_rule: "('a,'b) rule") 
    (item_dot : nat) 
    (item_origin : nat)
    (item_end : nat)

(*derive comparator "('a::ccompare, 'b::ccompare) item"*)

type_synonym ('a, 'b) items = "('a, 'b) item set"

definition item_nonterminal :: "('a, 'b) item \<Rightarrow> ('a, 'b) symbol"
where
  "item_nonterminal x = fst (item_rule x)"

definition item_rhs :: "('a, 'b) item \<Rightarrow> ('a, 'b) sentence"
where
  "item_rhs x = snd (item_rule x)"

definition item_\<alpha> :: "('a, 'b) item \<Rightarrow> ('a, 'b) sentence"
where
  "item_\<alpha> x = take (item_dot x) (item_rhs x)"

definition item_\<beta> :: "('a, 'b) item \<Rightarrow> ('a, 'b) sentence"
where 
  "item_\<beta> x = drop (item_dot x) (item_rhs x)"

definition init_item :: "('a, 'b) rule \<Rightarrow> nat \<Rightarrow> ('a, 'b) item"
where
  "init_item r k = Item r 0 k k"

definition is_complete :: "('a, 'b) item \<Rightarrow> bool"
where
  "is_complete x = (item_dot x \<ge> length (item_rhs x))"

definition next_symbol :: "('a, 'b) item \<Rightarrow> ('a, 'b) symbol option"
where
  "next_symbol x = (if is_complete x then None else Some ((item_rhs x) ! (item_dot x)))"

definition inc_item :: "('a, 'b) item \<Rightarrow> nat \<Rightarrow> ('a, 'b) item"
where
  "inc_item x k = Item (item_rule x) (item_dot x + 1) (item_origin x) k"

definition bin :: "('a, 'b) items \<Rightarrow> nat \<Rightarrow> ('a, 'b) items"
where
  "bin I k = { x . x \<in> I \<and> item_end x = k }"
            
context LocalLexing begin

definition max_rhs::"nat" where
"max_rhs = (Inf {n | n.  (\<forall> r \<in> \<RR> . length (snd r) < n)})"

find_theorems "Inf ?X \<in> ?X "
lemma max_witness:"\<exists>x. \<forall>r\<in>\<RR>. length (snd r) < x"
proof (cases "\<RR> = {}")
  case True
  then show ?thesis by auto
next
  case False
  define x where "x = Suc (Max ((\<lambda> r . length (snd r))` \<RR>))" 
  show ?thesis apply(auto intro!: exI [of _ x] simp add: x_def) using finite_grammar False
    by (metis Max_ge finite_imageI image_iff le_imp_less_Suc snd_conv)
qed
  
lemma smaller_max_rhs:"(\<forall> r \<in> \<RR> . length (snd r) <  max_rhs)"
  using Conditionally_Complete_Lattices.Inf_nat_def1 
    [of "{n | n.  (\<forall> r \<in> \<RR> . length (snd r) < n)}"] apply(auto simp add:max_rhs_def)
    using max_witness by fastforce



definition All_top ::"('a, 'b) items" where 
"All_top =  (\<lambda> (r, orig, d, k). Item r orig d k) ` (\<RR> \<times>  {n | n. n \<le> max_rhs} \<times> {n | n. n \<le> (length Doc)} 
       \<times> {n | n. n \<le> (length Doc)})"

theorem All_top_fin:"finite All_top "
  using All_top_def finite_grammar by simp
definition Init :: "('a, 'b) items"
where
  "Init = { init_item r 0 | r. r \<in> \<RR> \<and> fst r = \<SS> }"

lemma Init_sub_All_top':"Init \<subseteq> All_top" 
proof -
  have 1:"\<forall>  i \<in> Init. (\<exists>  r \<in> \<RR> . i = Item r 0 0 0)" using Init_def init_item_def by fastforce
  have "\<forall> r \<in> \<RR> . (r, 0, 0, 0) \<in> (\<RR> \<times> {n |n. n \<le> length Doc} \<times> {n |n. n \<le> max_rhs} \<times> {n |n. n \<le> length Doc})" by blast
  then have "\<forall> r \<in> \<RR> . Item r 0 0 0 \<in> All_top" using All_top_def using Setcompr_eq_image by force
  then show ?thesis using 1 by fast
qed

(*adds items if next element of an item ending there is a nonterminal*)

(*only so many can be added because of nonterminal limits*)
definition Predict :: "nat \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b) items"
where
  "Predict k I = I \<union>  
     { init_item r k | r x. r \<in> \<RR> \<and> x \<in> bin I k \<and> 
       next_symbol x = Some(fst r) }" (*what can be said about added states here?*)


lemma Predict_All_top:
  assumes "I \<subseteq> All_top"  "(k \<le> length Doc)"
  shows "Predict k I \<subseteq> All_top"
proof -
  obtain new where new_def:"new = { init_item r k | r x. r \<in> \<RR> \<and> x \<in> bin I k \<and> 
       next_symbol x = Some(fst r) }" by blast
  then have 1:"new \<subseteq> {init_item r k | r . r \<in> \<RR>} " by blast
  then have 1:"\<forall>  i \<in> new. (\<exists>  r \<in> \<RR> . i = Item r  0 k k)" using  init_item_def by blast
  have "\<forall> r \<in> \<RR> . (r, 0, k, k) \<in>  (\<RR> \<times> {n |n. n \<le> max_rhs} \<times> {n |n. n \<le> length Doc} \<times> {n |n. n \<le> length Doc})" 
    using assms by auto
  then have "\<forall> r \<in> \<RR> . Item r 0 k k \<in> All_top" using All_top_def  Setcompr_eq_image by force
  with 1 have 2:"new \<subseteq> All_top" by fast
  have "Predict k I \<subseteq> I \<union> new" using new_def Predict_def by simp
  then show ?thesis using assms 2 by blast 
qed

lemma Predict_top:"Predict k I \<subseteq> I \<union> (\<lambda> r. init_item r k) `\<RR>"
proof - 
  obtain new where new_def:"new = { init_item r k | r x. r \<in> \<RR> \<and> x \<in> bin I k \<and> 
       next_symbol x = Some(fst r) }" by blast
  then have 1:"new \<subseteq> {init_item r k | r . r \<in> \<RR>} " by blast
  have "Predict k I \<subseteq> I \<union> new" using new_def Predict_def by simp
  with 1 show ?thesis by blast
qed

lemma bin_help:
  assumes "I = J \<union> H"
  shows"bin I k = (bin J k )\<union> (bin H k)"
proof -
  from assms have "bin I k = {i . i \<in> J \<and> item_end i = k} \<union> {i . i \<in> H \<and> item_end i = k}" using bin_def by auto
  then show ?thesis using bin_def by auto
qed

lemma bin_help':"I \<subseteq> J \<union> H \<Longrightarrow>bin I k \<subseteq> (bin J k )\<union> (bin H k)"
by (metis sup.absorb_iff2 bin_help)


lemma bin_help'':"I \<subseteq> J \<Longrightarrow> bin I k \<subseteq> (bin J k )"
  by (metis sup.absorb_iff2 bin_help)

lemma Predict_add:"bin (Predict k I) k \<subseteq> bin I k \<union> (\<lambda> r. init_item r k) `\<RR>"
proof -
  obtain new where new_def:"new = {init_item r k | r x. r \<in> \<RR> \<and> x \<in> bin I k \<and> 
       next_symbol x = Some(fst r) }" by blast
  then have 1:"new \<subseteq> {init_item r k | r x. r \<in> \<RR>}" by blast
  obtain newtop where 2:"newtop = (\<lambda> r. init_item r k) `\<RR>" by blast
  then have 3:"new \<subseteq> newtop" using 1 by auto
  have top:"\<forall> i \<in> newtop . item_end i = k" using 2 item_end_def init_item_def 
    by (simp add: init_item_def)
  then have 4:"bin new k = new" using 3 bin_def by blast
  from top have 5:"bin newtop k = newtop" using bin_def by blast
  have "Predict k I = I \<union> new" using new_def Predict_def by auto
  then have "bin (Predict k I) k \<subseteq> bin I k \<union> newtop" using 3 4 5 bin_help [where ?I = "Predict k I" 
        and ?J="I" and ?H="new"] by blast
  then show ?thesis using 2 by blast
qed
      
  
lemma Predict_inv:"k \<noteq> k' \<Longrightarrow> bin (Predict k I) k' = bin I k' "
proof - 
  assume assms:"k \<noteq> k'" 
  obtain new where new_def:"new = { init_item r k | r x. r \<in> \<RR> \<and> x \<in> bin I k \<and> 
       next_symbol x = Some(fst r) }" by blast
  then have "\<forall> i \<in> new .\<exists>r . i = init_item r k" using init_item_def by blast
  then have 1:"\<forall> i \<in> new . item_end i = k" using init_item_def by (metis item.sel(4))
  then have 2:"bin new k' = {}" using bin_def assms by fast
  have pred:"Predict k I = I \<union> new" using Predict_def new_def by auto
  have "bin (I \<union> new) k' = {x \<in>  (I \<union> new). item_end x = k'}" using bin_def by auto
  then have "bin (I \<union> new) k' = {x \<in>  (I). item_end x = k'} \<union> {x \<in>  new. item_end x = k'}" by auto
  then have "bin (Predict k I) k' = bin I k' \<union> bin new k'" using bin_def pred by auto
  then show ?thesis using 2 by auto
qed


(*an additional invariant for complete has to be \<Longrightarrow> item can only be incremented once ?*)

(*need an completion invariant \<Longrightarrow> i.e. from original set, only so many items can be incremented*)
definition Complete :: "nat \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b) items"
where
  "Complete k I = I \<union> { inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y)}"

(*the specific worrying ones would be items whose origin is k and whose end is k \<Longrightarrow> should not be possible under incrementing*)
(*for all added items in complete, are not in bin *)

(**)
definition All_top_incrementable::"('a, 'b) item \<Rightarrow> bool" where
"All_top_incrementable i = (item_rule i \<in> \<RR> \<and> item_end i  \<le> length (Doc) 
  \<and> item_origin i  \<le> length (Doc) \<and> item_dot i \<le> max_rhs \<and> length (snd (item_rule i)) < max_rhs)"

lemma All_top_implies:
  assumes "i \<in> All_top "
  shows"All_top_incrementable i"
proof -
  from assms have "item_rule i \<in> \<RR>" using All_top_def by auto
  then have "length (snd (item_rule i)) < max_rhs" using smaller_max_rhs by fast
  then show ?thesis using assms All_top_def All_top_incrementable_def by fastforce
qed

lemma All_top_sufficient:
  assumes "item_origin i \<le> length Doc \<and> item_end i \<le> length Doc \<and> item_rule i  \<in> \<RR> \<and> item_dot i \<le> max_rhs "
  shows " i \<in> All_top"
proof -
  from assms have "(item_rule i, item_dot i, item_origin i, item_end i) 
  \<in>  (\<RR> \<times> {n |n. n \<le> max_rhs} \<times> {n |n. n \<le> length Doc} \<times> {n |n. n \<le> length Doc})" by blast
  then show ?thesis  using All_top_def 
    by (metis (no_types, lifting) item.exhaust_sel old.prod.case rev_image_eqI)
qed

lemma All_top_incrementable:
  assumes "All_top_incrementable i" "k \<le> length Doc" " item_dot i \<le>   length (item_rhs i)"
  shows "inc_item i k \<in> All_top"
proof -
  from assms(1) have "item_dot i < max_rhs" by (metis assms(3) le_eq_less_or_eq not_le All_top_incrementable_def  item_rhs_def )
  then have 1:"item_dot (inc_item i k) \<le> max_rhs" by (simp add: inc_item_def)
  from assms have 2:"item_origin (inc_item i k) \<le> length Doc \<and> 
    item_end (inc_item i k) \<le> length Doc \<and> item_rule (inc_item i k) \<in> \<RR>" using 
    All_top_incrementable_def by (simp add:inc_item_def)
  show ?thesis using All_top_sufficient 1 2 by fast
qed


lemma next_implies_dot_le_rhs:"(\<exists> l . next_symbol  x= Some l) \<Longrightarrow> item_dot x \<le> length (item_rhs x)" 
  using next_symbol_def is_complete_def
  by (metis nat_le_linear option.distinct(1))


lemma Complete_All_top:
  assumes "I \<subseteq> All_top"  "(k \<le> length Doc)"
  shows "Complete k I \<subseteq> All_top"
proof -
  obtain new where new_def:"new = { inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y) }" by blast
  then have "\<forall> i \<in> new .\<exists>x \<in> I. i = inc_item x k \<and> (\<exists> l . next_symbol  x= Some l)" 
    using init_item_def bin_def by blast
  then have "\<forall> i \<in> new .\<exists>x \<in> I. i = inc_item x k \<and> item_dot x \<le> length (item_rhs x)"  
    using next_implies_dot_le_rhs by blast
  then have "\<forall> i \<in> new . \<exists>x \<in> I .  i = inc_item x k \<and> item_dot x \<le> length (item_rhs x) \<and> 
  All_top_incrementable x" using All_top_implies All_top_incrementable_def assms item_rhs_def by blast
  then have 1:"\<forall> i \<in> new . i \<in> All_top" using All_top_incrementable assms by fastforce
  have "(Complete k I) \<subseteq> I \<union> new" using new_def Complete_def by simp
  then show ?thesis using assms 1 by blast
qed

definition Complete_Add::"nat \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b) items" where
"Complete_Add k I = (\<lambda> x. inc_item x k) ` {x . \<exists>  k' \<le> k . x \<in> bin I k'}"

lemma Complete_Add_item_end:"\<forall> i \<in> Complete_Add k I . item_end i = k"
  by (simp add: Complete_Add_def inc_item_def)

lemma Complete_Add_bin:"bin (Complete_Add k I ) k= Complete_Add k I"
  using Complete_Add_item_end bin_def by blast

lemma Complete_Add_bin':"k' \<noteq> k \<Longrightarrow> bin (Complete_Add k I) k'= {}"
  by (simp add: bin_def Complete_Add_item_end) 

(*actually increases inc_item x k , but instead prove
no lower items get incremented*)

(*actual top*)

(*need a different closure on completion*)
(*rather replace Complete_top with something else*)


(*additional lemma, non of the smaller bins are increased*)
lemma Complete_inv:
  assumes "k' \<noteq> k"
  shows "bin (Complete k I) k' = bin I k'"
proof -
 obtain new where new_def:"new = {inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y) }" by blast
  then have  1:"\<forall> i \<in> new . \<exists> x y. inc_item x k = i" by blast
  then have "\<forall> i \<in> new . item_end i = k" using  inc_item_def
    by (metis item.sel(4) )
  with assms have "\<forall> i \<in> new . item_end i \<noteq> k'" by blast
  then have new_empty:"bin new k' = {}" using bin_def by blast
  have "bin (Complete k I) k'= {i . i \<in> (I \<union> new) \<and> item_end i  = k'}" using Complete_def new_def bin_def 
    by (simp add: bin_def) 
  then have "bin (Complete k I) k' = {i . i \<in> I \<and> item_end i  = k'} \<union> {i . i \<in> new \<and> item_end i  = k'}" by blast
  then show ?thesis using bin_def new_empty by blast
qed


definition TokensAt :: "nat \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b, 'c) token set"
where
  "TokensAt k I = { (t, s) | t s x l. x \<in> bin I k \<and> 
     next_symbol x = Some t \<and> is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc) }" (*from finiteness of Doc derive finiteness of tokens*)
(*if next symbol is terminal*)


(*Complete Top has to work a bit differently: \<le>?*)

lemma Complete_Predict_inv:
  assumes "k' \<noteq> k"
  shows "bin ((Complete k (Predict k I))) k' = bin I k'"
proof -
  from Predict_inv have "bin (Predict k I) k' = bin I k'" using assms by auto
  then show ?thesis using Complete_inv assms by force
qed

definition Predict_Add::"nat \<Rightarrow> ('a, 'b) items" 
  where
"Predict_Add k  =  (\<lambda> r. init_item r k) `\<RR>"

lemma Predict_Add_item_end:"\<forall> i \<in> Predict_Add k . item_end i = k"
  by (simp add: Predict_Add_def init_item_def)

lemma Predict_Add_bin:"bin (Predict_Add k) k= Predict_Add k"
  using Predict_Add_item_end bin_def by blast

lemma Predict_Add_bin':"k' \<noteq> k \<Longrightarrow> bin (Predict_Add k) k'= {}"
  by (simp add: bin_def Predict_Add_item_end) 


definition Tokens :: "nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b, 'c) token set"
where
  "Tokens k T I = Sel T (TokensAt k I)" (*selector application*)
                  
(*rewrite*)
(*should be easier to prove because of limited tokens*)
definition Scan :: "('a, 'b,'c) token set \<Rightarrow> nat \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b) items"
where
  "Scan T k I = I \<union>
     { inc_item x (k + length c) | x t c. x \<in> bin I k \<and> (t, c) \<in> T \<and>
       next_symbol x = Some t}"
(*scanning again does not produce items that can be used for subsequent steps*)

(*definitely true*)

lemma Scan_All_top:
  assumes "I \<subseteq> All_top"  "\<forall> (t, c) \<in> T . k + length c \<le> length Doc"
  shows "Scan T k I \<subseteq> All_top"
proof -
  obtain new where new_def:"new = 
     { inc_item x (k + length c) | x t c. x \<in> bin I k \<and> (t, c) \<in> T \<and>
       next_symbol x = Some t}" by blast
  then have "\<forall> i \<in> new .\<exists>x \<in> I. \<exists> (t, c) \<in> T . i = inc_item x (k + length c) \<and> (\<exists> l . next_symbol  x= Some l)" 
    using init_item_def bin_def by blast
  then have "\<forall> i \<in> new .\<exists>x \<in> I. \<exists> (t, c) \<in> T . i = inc_item x (k + length c) \<and> item_dot x \<le> length (item_rhs x)"    
    using next_implies_dot_le_rhs by blast
  then have "\<forall> i \<in> new . \<exists>x \<in> I .  \<exists> (t, c) \<in> T . i = inc_item x (k + length c) \<and> item_dot x \<le> length (item_rhs x) \<and> 
  All_top_incrementable x" using All_top_implies All_top_incrementable_def assms item_rhs_def by blast
  then have 1:"\<forall> i \<in> new . i \<in> All_top" using All_top_incrementable assms by fastforce
  have "(Scan T k I) \<subseteq> I \<union> new" using new_def Scan_def by simp
  then show ?thesis using assms 1 by blast
qed


definition Scan_Add::"nat \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items" where
"Scan_Add k I T = { inc_item x (k + length c) | x t c. x \<in> (bin I k \<union> Complete_Add k I \<union> Predict_Add k) \<and> (t, c) \<in> T}"

lemma Scan_top:"Scan T k I \<subseteq> I \<union>  
  Scan_Add k  I T"
  using Scan_Add_def Scan_def by auto


lemma Step_All_top:
   "I \<subseteq> All_top \<Longrightarrow> k \<le> length Doc \<Longrightarrow>\<forall> (t, c) \<in> T . (k + length c) \<le> length Doc
 \<Longrightarrow>Scan T k (Complete k (Predict k I)) \<subseteq> All_top"
using  Predict_All_top Complete_All_top   Scan_All_top by auto


lemma Scan_Add_help:
  assumes "\<forall> (t, c) \<in> T . length c > 0"
  shows "\<forall> i \<in> (Scan_Add k I T) .   item_end i > k"
proof -
   have "\<forall> i \<in> (Scan_Add k I T) . \<exists> x t c . (t, c) \<in> T \<and> inc_item x (k + length c) = i " using Scan_Add_def by auto
  then have "\<forall> i \<in> (Scan_Add k I T) .  \<exists> x c . length c > 0  \<and> inc_item x (k + length c) = i" using assms
    by (metis Ex_list_of_length case_prod_conv)
  then have "\<forall> i \<in> (Scan_Add k I T) .  \<exists> x c . c > k  \<and> inc_item x c = i" 
    by (meson less_add_same_cancel1)
  then show ?thesis by (metis inc_item_def item.sel(4))
qed



lemma Scan_Add_top':
  assumes "k' >  k" 
  shows " bin (Scan T k I) k' \<subseteq> bin I k' \<union>  (Scan_Add k I T)"
proof -
  have 1:"bin (Scan_Add k I T) k' \<subseteq> (Scan_Add k I T)" using bin_def by auto 
  have "Scan T k I \<subseteq> I \<union> Scan_Add k I T" using Scan_def using Scan_top by presburger
  then show ?thesis using  bin_help' 1  by blast
qed


section "Need combination of lemmatas regarding bins to construct overapproximation top, i.e.
    bin I k"

definition top_help::"nat \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b) items" where
"top_help k I= I \<union> Complete_Add k I \<union> Predict_Add k"


definition top_help2::"nat  \<Rightarrow> ('a, 'b) items \<Rightarrow>('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items" where
"top_help2 k I T = {inc_item x (k + length c) | x t c. x \<in> bin (top_help k I) k \<and> (t, c) \<in> T}"

definition top'::"nat  \<Rightarrow> ('a, 'b) items \<Rightarrow>('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items" where
"top' k I T = top_help k I \<union> top_help2 k I T"

definition step::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b) items" where
"step k T = (\<lambda> I. Scan T k (Complete k (Predict k I))) " (*union was unnecessary*)

definition invariant::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items \<Rightarrow>('a, 'b) items \<Rightarrow> bool" where
"invariant k  T init I = (\<exists> n . funpower (step k T) n  init   = I)" (*there exists a *)

section "Use those invariants to prove that top'  stays constant"
definition valid_bounds::"('a, 'b) item set \<Rightarrow> bool" where
"valid_bounds I = (\<forall> i \<in> I . item_origin i \<le> item_end i)"

(*has to be redefined*)
definition valid_rule::"('a, 'b) item set \<Rightarrow> bool" where
"valid_rule I = (\<forall> i \<in> I . item_rule i \<in> \<RR>)"
 (*Axiom of grammar*)
lemma Predict_Finite:"finite (Predict_Add k)"
  by (simp add: Predict_Add_def finite_grammar)

lemma Predict_Finite':"finite I  \<Longrightarrow> finite (Predict k I)" 
  by (metis finite_UnI Predict_Finite Predict_top Predict_Add_def finite_subset) 

lemma Predict_Add_bounds:"valid_bounds (Predict_Add k)"
  by (simp add: init_item_def valid_bounds_def Predict_Add_def)

lemma Predict_bounds:"valid_bounds I  \<Longrightarrow> valid_bounds (Predict k I)"
  using Predict_Add_bounds Predict_Add_def Predict_top subsetD valid_bounds_def by fastforce

lemma Predict_Add_rule:"valid_rule (Predict_Add k)"
  by (simp add: init_item_def valid_rule_def Predict_Add_def)

lemma Predict_rule:"valid_rule I \<Longrightarrow> valid_rule (Predict k I)"
  using Predict_Add_rule Predict_Add_def Predict_top subsetD valid_rule_def by fastforce


lemma Complete_Finite:"finite I \<Longrightarrow> finite (Complete_Add k I)"
  by (simp add: Complete_Add_def bin_def)

lemma Complete_Finite':
  assumes "finite I " 
  shows "finite (Complete k I)"
proof -
   obtain new where new_def:"new = {inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y) }" by blast
   then have  1:"new \<subseteq> {inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k}" by blast
   then have "new \<subseteq>  { inc_item x k   |x. x \<in> I }" using new_def bin_def 
     by (smt (verit, del_insts) Collect_mono_iff mem_Collect_eq)
   then have 1:"finite new" using assms(1) using finite_subset by fastforce
   have "Complete k I = I \<union> new" using Complete_def using new_def by presburger
   with 1 show ?thesis using assms(1)  by auto
qed

lemma Complete_Add_bounds:  
  assumes "valid_bounds I"
  shows "valid_bounds (Complete_Add k I)"
proof -
  have 1:"\<forall> i \<in> (Complete_Add k I) . item_end i = k" using Complete_Add_item_end by blast
  have "\<forall> i \<in> ({x . \<exists>  k' \<le> k . x \<in> bin I k'}) . item_origin i \<le> k" 
    by (smt (verit, ccfv_SIG) assms bin_def leD leI mem_Collect_eq order_trans valid_bounds_def)
  then have "\<forall> i \<in> (Complete_Add k I).  item_origin i \<le> k" 
    by (simp add: inc_item_def Complete_Add_def)
  then show ?thesis using 1 valid_bounds_def by auto
qed

lemma Complete_top':
  assumes "valid_bounds I " 
  shows "Complete k I \<subseteq> I \<union>  Complete_Add k I"
proof -
   obtain new where new_def:"new = {inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y) }" by blast
   then have  1:"new \<subseteq> {inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k}" by blast
   have "{x | x y. x \<in> bin I (item_origin y) \<and> y \<in> bin I k} \<subseteq> 
      {x . \<exists>  k' \<le> k . x \<in> bin I k'}" using assms(1) valid_bounds_def 
     by (smt (verit, ccfv_threshold) Collect_mono_iff bin_def mem_Collect_eq)
   then have "new \<subseteq>  { inc_item x k   |x. \<exists>  k' \<le> k . x \<in> bin I k'}" using new_def by auto
   then have 1:"new \<subseteq> Complete_Add k I" using Complete_Add_def by blast
   have "Complete k I = I \<union> new" using Complete_def using new_def by presburger
   with 1 show ?thesis by auto
qed


lemma Complete_bounds: "valid_bounds I \<Longrightarrow> valid_bounds (Complete k I)"
  by (meson Complete_Add_bounds Complete_top' UnE in_mono valid_bounds_def)


lemma Complete_Add_rule:
  assumes "valid_rule I"
  shows "valid_rule (Complete_Add k I)"
proof -
  from assms have "\<forall> i \<in> ({x . \<exists>  k' \<le> k . x \<in> bin I k'}) . item_rule i  \<in> \<RR>" 
    by(auto simp add:bin_def  valid_rule_def)
  then have "\<forall> i \<in> (Complete_Add k I).  item_rule i\<in> \<RR>" 
    by (auto simp add: inc_item_def Complete_Add_def)
  then show ?thesis using valid_rule_def by blast 
qed


lemma Complete_rule:
  assumes "valid_rule I " 
  shows "valid_rule (Complete k I)"
proof -
   obtain new where new_def:"new = {inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k \<and> is_complete y \<and> 
     next_symbol x = Some (item_nonterminal y) }" by blast
   then have  1:"new \<subseteq> {inc_item x k | x y. 
     x \<in> bin I (item_origin y) \<and> y \<in> bin I k}" by blast
   then have "new \<subseteq>  { inc_item x k   |x. \<exists>  k' . x \<in> bin I k'}" using new_def by auto
   then have "\<forall> i \<in> new. \<exists> x \<in> I. i = inc_item x k" using bin_def by blast
   then have "\<forall> i \<in> new. \<exists> x \<in> I. item_rule x = item_rule i" using inc_item_def  by (metis item.sel(1))
   then have 1:"\<forall> i \<in> new.  item_rule i \<in> \<RR>" using assms(1) valid_rule_def by force 
   have "Complete k I = I \<union> new" using Complete_def using new_def by presburger
   with 1 show ?thesis using assms(1) valid_rule_def by auto
qed


lemma tophelp_finite:"finite I  \<Longrightarrow> finite (top_help k I)"
  by (simp add: top_help_def Predict_Finite Complete_Finite)

lemma tophelp2_finite:
  assumes"finite I \<and> finite T "
  shows"finite (top_help2 k I T)"
proof -
  have sub:"bin (top_help k I ) k \<subseteq> top_help k I" using bin_def by auto
  have "finite (top_help k I )"  by (simp add: assms top_help2_def  tophelp_finite)
  then have 0:"finite (bin (top_help k I ) k)" using sub by (meson finite_subset)
  then have "finite (T \<times> (bin (top_help k I ) k))" using assms 
    by simp
  then have 1:"finite ((\<lambda> ((t, c), x) . inc_item x (k + length c)) ` (T \<times> (bin (top_help k I ) k)))" by simp
  from top_help2_def have "\<forall> i \<in>  (top_help2 k I T).  \<exists> x t c . (t, c) \<in> T \<and> x \<in>(bin (top_help k I ) k) \<and> inc_item x (k + length c) = i" by auto
  then have "\<forall> i \<in>  (top_help2 k I T).  \<exists> x t c . ((t, c), x) \<in> (T \<times> bin (top_help k I ) k) \<and> inc_item x (k + length c) = i" by simp
  then have "top_help2 k I T \<subseteq> (\<lambda> ((t, c), x) . inc_item x (k + length c)) ` (T \<times> (bin (top_help k I ) k))" by force
  then show ?thesis using 1 finite_subset by blast
qed
lemma top'_finite:"finite I \<Longrightarrow> finite T\<Longrightarrow> finite (top' k I T)"
  by (auto simp add: tophelp_finite tophelp2_finite top'_def)

lemma top_help2_eq_step_add:"top_help2 k I T = Scan_Add k I T"
proof -
  have "top_help k I = I \<union> Predict_Add k \<union> Complete_Add k I" using top_help_def by auto
  then have 1:"bin (top_help k I) k  = bin (I \<union> Predict_Add k \<union> Complete_Add k I) k" using bin_def by auto
  then have 2:"bin (I \<union> Predict_Add k \<union> Complete_Add k I) k = bin I k  \<union> Predict_Add k \<union> Complete_Add k I" using Predict_Add_bin Complete_Add_bin bin_help by metis 
      (*Predict and Complete Lemmas only produce k*)
  then show ?thesis using top_help2_def Scan_Add_def 1 by auto
qed

(*Scan_Finite has to be replaced by All_top*)
lemma Scan_Finite:"finite I \<and> finite T \<Longrightarrow> finite (Scan T k I)"
  by (metis finite_UnI Scan_top tophelp2_finite top_help2_eq_step_add finite_subset)

lemma Scan_Add_bounds:
  assumes "valid_bounds I"
  shows "valid_bounds (Scan_Add  k I T)"
proof -
  from assms have "\<forall> i \<in> bin I k . item_origin i \<le> k" using assms bin_def valid_bounds_def
    by (metis (mono_tags, lifting) mem_Collect_eq)
  have 1:"\<forall> x \<in> (Complete_Add k I \<union> Predict_Add k) .  item_end x  = k" 
    by (meson LocalLexing.Complete_Add_item_end LocalLexing.Predict_Add_item_end LocalLexing_axioms UnE)
  from assms Complete_Add_bounds Predict_Add_bounds have 
      2:"valid_bounds (Complete_Add k I \<union> Predict_Add k)" using valid_bounds_def by auto     
  have 3:"\<forall> i \<in> (Scan_Add k I T) . item_end i \<ge> k" by(auto simp add: Scan_Add_def inc_item_def)
  have 4:"\<forall> i \<in> (Scan_Add k I T) . item_origin i \<le> k" apply (auto simp add: Scan_Add_def assms inc_item_def bin_def)
    using assms valid_bounds_def  apply blast using 1 2 valid_bounds_def 
     apply auto[1] using 1 2 valid_bounds_def by  auto
  with 3 show ?thesis using valid_bounds_def by fastforce
qed

lemma Scan_bounds:"valid_bounds I \<Longrightarrow> valid_bounds (Scan T k I)"
  by (meson Scan_Add_bounds Scan_top UnE in_mono valid_bounds_def)

lemma Scan_Add_rule:
  assumes "valid_rule I"
  shows "valid_rule (Scan_Add k I T)"
proof -
  have 1:"\<forall> x \<in> (Complete_Add k I \<union> Predict_Add k) .  item_rule x \<in> \<RR>" using assms Complete_Add_rule 
  Predict_Add_rule valid_rule_def by blast
  from 1 assms have 3:"\<forall> i \<in> (Scan_Add k I T) . item_rule  i \<in> \<RR>" 
    by(auto simp add: Scan_Add_def inc_item_def bin_def valid_rule_def)
  then show ?thesis using valid_rule_def by blast
qed

lemma Scan_rule:"valid_rule I \<Longrightarrow> valid_rule (Scan T k I)"
  by (meson Scan_Add_rule Scan_top UnE in_mono valid_rule_def)


lemma step_inc:"I \<subseteq> step k T I"
  by (auto simp add: step_def Predict_def Complete_def Scan_def)


(*returns all (items i.e. trees ) generated from an existing item set *)
definition \<pi> :: "nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b) items"
where
  "\<pi> k T I = 
     limit (\<lambda> I. Scan T k (Complete k (Predict k I))) I"

lemma \<pi>_monotone:"I \<subseteq> \<pi> k T I "
proof -
  have 1:"I \<subseteq> funpower (step k T )  0 I" using step_inc by simp
  have " \<pi> k T I =  \<Union> {funpower (step k T )  n I | n . True}" using limit_def \<pi>_def step_def natUnion_def 
    by (metis)
  then show ?thesis using 1 by blast 
qed

lemma natUnion'_ind:"natUnion' (Suc n) f = (natUnion' n f) \<union> (f (Suc n))"
proof -
  have "{n' . n' \<le> Suc n} = {n' . n' \<le>  n} \<union> {Suc n}" by auto
  then have "{f n' | n' . n' \<le> Suc n} = {f n' | n' . n' \<le> n} \<union> {f (Suc n)}" by blast
  then have "\<Union> {f n' | n' . n' \<le> Suc n} = \<Union> ({f n' | n' . n' \<le> n} \<union> {f (Suc n)})" by auto
  then have "\<Union> {f n' | n' . n' \<le> Suc n} = (\<Union> ({f n' | n' . n' \<le> n}) \<union> (f (Suc n)))" by auto
  then show ?thesis using natUnion'_def by metis
qed
lemma step_natunion':"funpower (step k T) n I  = natUnion' n  (\<lambda> n. funpower (\<lambda> I. Scan T k (Complete k (Predict k I))) n I)"
proof (induction n)
  case 0
  then have 1:"funpower (step k T) 0 I = I" by simp
  have "natUnion' 0  (\<lambda> n. funpower (\<lambda> I. Scan T k (Complete k (Predict k I))) n I) =  
     I"  
    by (simp add: natUnion'_def)  
  then show ?case using 1 by simp 
next
  case (Suc n)
  have 0: "funpower (step k T) n I \<subseteq> funpower (step k T) (Suc n) I" using step_inc by simp 
  have 2:"natUnion' (Suc n)  (\<lambda> n. funpower  (step k T) n I) = 
    natUnion' n  (\<lambda> n. funpower (\<lambda> I. Scan T k (Complete k (Predict k I))) n I) \<union> (funpower  (step k T) (Suc n) I)" 
    using natUnion'_ind step_def by fastforce
  then have "natUnion' (Suc n)  (\<lambda> n. funpower  (step k T) n I) = (funpower (step k T) n I) \<union> (funpower  (step k T) (Suc n) I)" using Suc by blast
  then show ?case using 0 step_def by auto 
qed


lemma Union_cases:
  fixes f::"nat \<Rightarrow> 'd set"
  assumes "\<Union> {f n | n. n > k'} = a" "\<Union> {f n | n. n \<le> k'} = b"
  shows   "\<Union> {f n | n . True} = a \<union> b"
proof -
  have 1:"{f n | n. n > k'} \<union> {f n | n. n \<le> k'} \<subseteq> {f n | n . True}" by blast
  { fix x 
    assume " x \<in> {f n | n . True}"
    then obtain n where def:"f n = x" by blast
    have "f n \<in> {f n | n. n > k'} \<union> {f n | n. n \<le> k'}" 
    proof (cases "n > k'")
      case True
      then show ?thesis by blast
    next
      case False
      then have "n \<le> k'" by simp
      then show ?thesis by blast
    qed
    with def have "x \<in> {f n | n. n > k'} \<union> {f n | n. n \<le> k'}" by blast
  }
  with 1 show ?thesis using assms by fast
qed

lemma limit:
  assumes "invariant k T I s " " \<not> step k T s \<noteq> s"
  shows " \<pi> k T I = s"
proof -
  obtain new where new_def:"new = Scan T k (Complete k (Predict k s))" by simp
  have "step k T s = Scan T k (Complete k (Predict k s)) " using step_def by simp 
  with assms(2) new_def have "new \<subseteq> s" by blast (*how does it hold?*)
  from assms(1) have "(\<exists>n. funpower (step k T) n I = s)" using invariant_def by simp
  then obtain n where base:"funpower (step k T) n  I   = s"  by blast

  {   fix n'
      have  1:"funpower (step k T) (n' + n)  I = s"
  proof (induction n')
    case 0
    then show ?case using base by simp
  next
    case (Suc n')
    have "funpower (step k T) (Suc n' + n) I =  step k T (funpower  (step k T) (n' + n) I)"  by simp
    then have "funpower (step k T) (Suc n' + n) I =  step k T s" using Suc by blast
    then show ?case using assms by blast
  qed
}
  then  have l:"\<forall> n' \<ge> 1 . funpower (step k T) (n' + n)  I = s" by simp
  have l':"\<forall> n' > n . funpower (step k T) n'  I = s" apply (rule allI) subgoal for n' using l 
      by (auto dest: spec [of _ "n' -  n"]) done
  from base have natUnion':"natUnion' n (\<lambda> n. funpower (\<lambda> I. Scan T k (Complete k (Predict k I))) n I) = s" 
      using step_natunion' 
      by (simp add: add.commute) 
  
  from l have ge:"\<Union> {(\<lambda> n. funpower (\<lambda> I. Scan T k (Complete k (Predict k I))) n I) n' | n' .n' > n} = s" 
    apply(auto simp add: step_def) using l' by (auto simp add: step_def)
  
  from natUnion' have le:" \<Union> { (\<lambda>n. funpower (\<lambda>I. Scan T k (Complete k (Predict k I))) n I) n' | n'. n' \<le> n } = s"
    by (simp add: natUnion'_def)
  then have "natUnion (\<lambda> n. funpower (\<lambda> I. Scan T k (Complete k (Predict k I))) n I) = s" 
    apply(auto simp add:natUnion_def) using le  Union_cases 
      [OF ge le] by auto 
      
  then show ?thesis by (simp add: \<pi>_def limit_def ) 
qed


definition invariant'::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items \<Rightarrow>('a, 'b) items \<Rightarrow> bool" where
"invariant' k  T init I = (invariant k  T init I \<and> step k T I \<noteq> I)" (*there exists a *)


(*set size increases, but it should be something alongside increasing we*)
definition meas::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b) items  \<Rightarrow> nat" where
"meas k T init I = card {s . s \<in> top' k init T \<and>   s \<notin> I}" 


(*Alternative measure \<longrightarrow> better measure using All_top*)
definition invariant_All_top::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) items \<Rightarrow> ('a, 'b) items \<Rightarrow> bool" where
"invariant_All_top  k  T init I = (I \<subseteq> All_top \<and> k \<le> length Doc \<and> (\<forall> (t, c) \<in> T . k + length c \<le> length Doc) 
   \<and> (\<exists> n . funpower (step k T) n  init   = I))" (*there exists a *)

definition meas_All_top::"('a, 'b) items  \<Rightarrow> nat" where
"meas_All_top I  = card {s . s \<in> All_top \<and>   s \<notin> I}"

lemma  meas_All_top_decreasing:
  assumes "invariant_All_top  k  T init  x \<and> step k T x \<noteq> x"
  shows "meas_All_top  (step k T x) < meas_All_top x "
proof -
  from assms have top:"x \<subseteq> All_top" using invariant_All_top_def  by simp
  then have top':"step k T x \<subseteq> All_top" using assms invariant_All_top_def Step_All_top step_def by simp
  from assms have "x \<subset> step k T x" using   step_inc by blast
   with top top' have sub:"{s . s \<in> All_top \<and>   s \<notin>  step k T x} \<subset> {s . s \<in> All_top \<and>   s \<notin>   x}" 
    by (smt (verit, best) Collect_mono_iff subset_iff subset_not_subset_eq)
  from All_top_fin have fin:"finite  {s . s \<in> All_top \<and>   s \<notin>   x}" by simp
  show ?thesis apply(simp add: meas_All_top_def) using sub fin  psubset_card_mono by auto
qed


lemma wf_All_top:"wf {(t, s). invariant_All_top k T init  s \<and>step k T s \<noteq> s \<and> t = step k T s}"
  using wf_if_measure [where ?P="\<lambda> x . invariant_All_top k T init x \<and> step k T x \<noteq> x" and 
   ?g="(\<lambda> I .  step k T I)"and ?f = "meas_All_top"]
  meas_All_top_decreasing by force

lemma invariant_step:
  assumes "invariant_All_top k T I s " " step k T s \<noteq> s "
  shows "invariant_All_top k T I (step k T s)"
proof -
  from invariant_All_top_def obtain n where "( funpower (step k T) n  I   = s)"
    using assms by auto
  then have 1:"funpower (step k T) (Suc n)  I   = step k T s" by simp
  with assms invariant_All_top_def have "step k T s \<subseteq> All_top" using step_def Step_All_top by simp
  with assms invariant_All_top_def 1 show ?thesis by metis
qed

lemma limit':"invariant_All_top k T I s \<Longrightarrow> \<not> step k T s \<noteq> s \<Longrightarrow> \<pi> k T I = s \<and> s \<subseteq> All_top \<and> step k T s = s"
  using limit invariant_All_top_def
  by (simp add: invariant_def)

lemma \<pi>_termination_All_top:
  assumes "k \<le> length Doc"  "\<forall> (t, c) \<in> T. k + length c \<le> length Doc" "I \<subseteq> All_top"
  shows "\<pi> k T I = while (\<lambda> I .  step k T I  \<noteq> I) (step k T) I \<and> while (\<lambda> I .  step k T I  \<noteq> I) (step k T) I \<subseteq> All_top
  \<and> (step k T (while (\<lambda> I .  step k T I  \<noteq> I) (step k T) I) = while (\<lambda> I .  step k T I  \<noteq> I) (step k T) I) "
 proof - 
 
  have "funpower (step k T) 0 I = I" by simp
  then have 1:"invariant_All_top  k T I I" using invariant_All_top_def assms by blast
  show ?thesis  apply (rule while_rule_lemma [where   ?s =  "I" and ?Q = "(\<lambda> f . 
        (\<pi> k T I = f \<and> f \<subseteq> All_top \<and> step k T f = f))" and ?b="(\<lambda> s. step k T s \<noteq> s)" and ?P="invariant_All_top k T I"])
    using invariant_step apply simp
    using limit' apply simp
    (*have to show that the relation on sets is wellformed according to some measure*)
    using wf_All_top using assms apply simp
    using 1 by simp
qed

thm while_rule_lemma [where   ?s =  "I" and ?Q = "\<lambda> f . 
        (\<pi> k T I = f \<and> f \<subseteq> All_top \<and> step k T f = f)" and ?b="(\<lambda> s. step k T s \<noteq> s)" and ?c="(step k T)" and ?P="invariant_All_top k T I"]
(*
(*prove that there always exists a minimal element*)
lemma wf:"(\<forall> (t, c) \<in> T . length c > 0) \<Longrightarrow>finite T \<Longrightarrow> finite I \<Longrightarrow> wf {(t, s). invariant k T I s \<and> step k T s \<noteq> s \<and> t = step k T s}"
  using wf_if_measure [where ?P="\<lambda> x . invariant' k T I x" and ?g="(\<lambda> I .  step k T I)"and ?f = "meas k T I"]
  measure_dec [where ?k="k" and  ?T="T" and ?I = "I" ]
  using invariant'_def by auto

lemma \<pi>_termination:
  assumes "(\<forall> (t, c) \<in> T . length c > 0)"  "finite T \<and> finite I "
  shows "\<pi> k T I = while (\<lambda> I .  step k T I  \<noteq> I) (step k T) I "
 proof - 
 
  have "funpower (step k T) 0 I = I" by simp
  then have 1:"invariant k T I I" using invariant_def by blast
  show ?thesis  apply (rule while_rule_lemma [where   ?s =  "I" and ?Q = "\<lambda> f . \<pi> k T I = f" and ?P="invariant k T I"])
    apply (metis funpower.simps(2) invariant_def)
    using limit apply simp
    (*have to show that the relation on sets is wellformed according to some measure*)
    using wf using assms apply simp
    using 1 by simp
qed
*)
fun \<J> :: "nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) items"
and \<I> :: "nat \<Rightarrow> ('a, 'b) items"
and \<T> :: "nat \<Rightarrow> nat \<Rightarrow> ('a, 'b, 'c) token set"
where
  "\<J> 0 0 = \<pi> 0 {} Init" (*Initial Element*)
| "\<J> k (Suc u) = \<pi> k (\<T> k (Suc u)) (\<J> k u)" (*Early parsing*)
| "\<J> (Suc k) 0 = \<pi> (Suc k) {} (\<I> k)" 
| "\<T> k 0 = {}"
| "\<T> k (Suc u) = Tokens k (\<T> k u) (\<J> k u)" (*selector step*)
| "\<I> k = natUnion (\<J> k)" (*upperbound at least Doc length \<Longrightarrow> no proper upperground here*)

definition TokensAt_top::"nat \<Rightarrow> ('a, 'b, 'c) token set" where
 "TokensAt_top k =  \<TT> \<times> (\<lambda> l .  take l (drop k Doc)) ` {n | n. n \<le> length Doc}"

lemma finite_TokensAt_top:"finite (TokensAt_top k)"
  by (simp add: finite_terminals \<TT>_def TokensAt_top_def)

lemma terminal_in_\<TT>:"is_terminal t \<Longrightarrow> t \<in> \<TT>"
  by (metis \<TT>_def image_iff is_terminal_def old.sum.exhaust old.sum.simps(5) old.sum.simps(6))

lemma lexing_limit:"\<forall> t \<in> \<TT>. \<forall> l \<in> Lex t Doc k . l + k \<le> length Doc"
proof (cases "k \<le> length Doc")
  case True
    then show ?thesis using Lex_is_lexer is_lexer_def 
    by (metis add.commute True)
  next
  case False
    then show ?thesis using Lex_is_lexer is_lexer_def by (metis empty_iff not_le)
qed
lemma terminal_max:"\<forall> t \<in> \<TT>. \<forall> l \<in> Lex t Doc k . l  \<le> length Doc"
  using lexing_limit by fastforce

theorem TokensAt_top:"TokensAt k I \<subseteq> TokensAt_top k"
proof -
  have "\<forall> (t, s) \<in> TokensAt k I .  \<exists> l.  is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc)" using TokensAt_def by blast
  then have "\<forall> (t, s) \<in> TokensAt k I .  \<exists> l.   t \<in> \<TT> \<and> 
     l \<le> length Doc \<and> s = take l (drop k Doc)" using terminal_in_\<TT> terminal_max by blast
  then have "\<forall> (t, s) \<in> TokensAt k I . s \<in> (\<lambda> l .  take l (drop k Doc)) ` {n | n. n \<le> length Doc}
  \<and> t \<in> \<TT>" by blast
  then show ?thesis using TokensAt_top_def by fast
qed

theorem TokensAt_monotonicity:
  assumes "I' \<subseteq> I"
  shows "TokensAt  k I' \<subseteq> TokensAt k I"
proof -
  have 1:"bin I' k \<subseteq> bin I k"  by (meson bin_help'' assms)
  have "\<forall> (t, s) \<in> (TokensAt k I') .   \<exists> l x .  x \<in> bin I' k \<and>  
     next_symbol x = Some t \<and> is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc)" using TokensAt_def by blast
  then have "\<forall> (t, s) \<in> (TokensAt k I') .   \<exists> l x .  x \<in> bin I k \<and>  
     next_symbol x = Some t \<and> is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> s = take l (drop k Doc)" using 1 by fast
  then show ?thesis using TokensAt_def by blast
qed

lemma take_length_less:"c = take n s \<Longrightarrow> length c \<le> n"
  by simp


lemma Tokens_add_valid:
  shows " \<forall> (t, c) \<in> TokensAt k I . k + length c \<le> length Doc"
proof -
  have "\<forall> (t, c) \<in> TokensAt k I . (\<exists>  l. is_terminal t \<and> 
     l \<in> Lex t Doc k \<and> c = take l (drop k Doc))" using TokensAt_def by blast
  then have 1:"\<forall> (t, c) \<in> TokensAt k I . (\<exists>  l. t \<in> \<TT> \<and>
     l \<in> Lex t Doc k \<and> (length c) \<le> l)" using take_length_less terminal_in_\<TT> by blast
  have 2:"\<forall> t \<in> \<TT>.  (\<forall> l \<in> Lex t Doc k . l + k \<le> length Doc )"
  proof (cases "k \<le> length Doc")
  case True
    then show ?thesis using Lex_is_lexer is_lexer_def 
    by (metis add.commute True)
  next
  case False
    then show ?thesis using Lex_is_lexer is_lexer_def by (metis empty_iff not_le)
  qed
  with 1 show ?thesis by fastforce    
qed



fun step_I::"nat \<Rightarrow> (('a, 'b, 'c) token set \<times> ('a, 'b) items) \<Rightarrow> (('a, 'b, 'c) token set \<times> ('a, 'b) items)" where
"step_I k (T, I) = (Tokens k T I , \<pi> k (Tokens k T I) I)"



(*those other step are needed to prove that subsequent KI are the same \<longrightarrow> *)
(*possible invariant cases needed*)
definition invariant_T_top::"nat \<Rightarrow> (('a, 'b, 'c) token set \<times> ('a, 'b) items) \<Rightarrow> bool" where
"invariant_T_top k T = ((snd T = step k (fst T) (snd T)) \<and>  (\<exists> k' . (\<J> k k' = snd T) \<and> (\<T> k k' = fst T)) 
    \<and> (fst T) \<subseteq> TokensAt k (snd T) \<and> fst T \<subseteq> TokensAt_top k \<and> snd T \<subseteq> All_top )"

(*monotonicity on items is already proven \<longrightarrow> reuse this*)
lemma \<J>_step:
  assumes "invariant_T_top k s " "fst (step_I k s) \<noteq> fst s" "k \<le> length Doc"
  shows "invariant_T_top k (step_I k s)"
proof -
  obtain I T where def:"(T, I) = s" apply(cases s) by blast
  with assms have 1:"((I = step k T I) \<and>  (\<exists> k' . (\<J> k k' = I) \<and> (\<T> k k' = T))) \<and>
      T \<subseteq> TokensAt k I \<and> T \<subseteq> TokensAt_top k" and I_top:"I \<subseteq> All_top" 
    using invariant_T_top_def apply force using invariant_T_top_def assms def by auto
  then obtain k' where 2:"\<J> k k' = I \<and> (\<T> k k' = T)" by blast
  from 2 have "\<T> k (Suc k') = Sel T  (TokensAt k I)" using Tokens_def by simp  
  with 1 have  T_top':"(\<T> k (Suc k') \<subseteq> TokensAt k I)" using Sel_is_selector is_selector_def by blast 
  then have T_top:"(\<T> k (Suc k')) \<subseteq> TokensAt_top k" using TokensAt_top by blast
  have "\<forall> (t, c) \<in> (TokensAt k I) . k + length c \<le> length Doc" 
    using Tokens_add_valid by presburger
  with T_top' have 4:"\<forall> (t, c) \<in> (\<T> k (Suc k')). k + length c \<le> length Doc" by blast
  from 2 have "\<J> k (Suc k') = \<pi> k (\<T> k (Suc k')) I" by simp
  then have eq_and_top:"\<J> k (Suc k') \<subseteq> All_top \<and> step k ((\<T> k (Suc k'))) (\<J> k (Suc k')) = \<J> k (Suc k')" 
    using \<pi>_termination_All_top [OF assms(3) 4 I_top] by argo 
  have "\<J> k k'\<subseteq> \<J> k (Suc k')" by (simp add: \<pi>_monotone)
  then have "TokensAt k I \<subseteq> TokensAt k (\<J> k (Suc k'))" using TokensAt_monotonicity 2 by blast
  with T_top' have fin:"(\<T> k (Suc k')) \<subseteq> TokensAt k (\<J> k (Suc k'))" by blast
  obtain I' where step_I:"I' = step_I k (T, I)" by simp
  with 2 have fin2:"((\<T> k (Suc k')),  \<J> k (Suc k')) = I'" by simp
  then have helper:"\<T> k (Suc k') = fst I' \<and> \<J> k (Suc k') = snd I'" by force
  then have "(\<exists> k' . (\<J> k k' = snd I' ) \<and> (\<T> k k' = fst I'))" by blast
  
  then have "invariant_T_top k I'" using helper fin eq_and_top invariant_T_top_def [where ?k = "k" and ?T="I'"] T_top by presburger
  then show ?thesis using step_I def by fast 
   
qed

lemma \<pi>_static: 
  assumes "I = step k T I"
  shows  "I = \<pi> k T I"
proof - 
  { 
  fix n
  have "funpower (step k T) n I = I"
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then show ?case using assms by simp
  qed
}
  then have "natUnion (\<lambda> n. funpower (step k T) n I) = I" 
    using natUnion_def [where ?f="(\<lambda> n. funpower (step k T) n I)"] by simp
  then show ?thesis using \<pi>_def step_def limit_def by fastforce
qed

lemma step:
  assumes "\<T> k (Suc k') = \<T> k k'" "\<J> k k' = step k (\<T> k k') (\<J> k k')"
  shows  "\<J> k (Suc k') = \<J> k k' \<and> \<T> k (Suc (Suc k')) = \<T> k k' \<and> \<J> k (Suc k') = step k (\<T> k (Suc k')) (\<J> k (Suc k'))"
proof -  
  from assms have "\<J> k (Suc k') = \<pi> k (\<T> k k') (\<J> k k')" by simp
  with assms(2) have 1:"\<J> k (Suc k') = (\<J> k k')" using assms(2) 
        \<pi>_static [where ?I="(\<J> k k')" and ?k="k" and ?T="(\<T> k k')"] by blast (*has to use the while con*)
  then have "\<T> k (Suc (Suc k')) = Tokens k (\<T> k  k') (\<J> k k')" using assms(1) by simp
  then show ?thesis using assms 1 by force
qed

(*
lemma step_I': (*use strong induction*)
 "\<T> k (Suc k') = \<T> k k' \<Longrightarrow> \<J> k k' = step k (\<T> k k') (\<J> k k') 
  \<Longrightarrow>\<T> k (k' + (Suc (Suc n))) = \<T> k k' \<and> \<J> k (k' + (Suc n)) = \<J> k k' 
  \<and> \<J> k (k' + (Suc n)) = step k (\<T> k (Suc k')) (\<J> k ( k' + n))"
proof (induction n rule: nat_less_induct)
  case (1 n)
  then have "\<T> k (k' + Suc n) = \<T> k k' \<and> \<T> k (k' +  n) = \<T> k k'" 
  then show ?case using step 
qed
*)
(*additional lemma denotin monotonicity of \<J> in those cases*)
lemma step_I: (*use strong induction*)
  assumes "\<T> k (Suc k') = \<T> k k'" "\<J> k k' = step k (\<T> k k') (\<J> k k')" 
  shows  "\<T> k (k' + (Suc n)) = \<T> k k' \<and> \<J> k (k' + n) = \<J> k k'"
proof (induction n rule: nat_less_induct)
  case (1 n)
  then show ?case 
  proof (cases n)
    case 0
    then show ?thesis using assms by simp
  next
    case (Suc nat)
    with 1 have 2:"\<T> k (k' + (Suc nat)) = \<T> k k' \<and> \<J> k (k' + nat) = \<J> k k'" by auto
    from Suc 1 have 3:"\<T> k (k' + nat) = \<T> k k'" 
      by (metis add.right_neutral less_Suc_eq_0_disj less_add_Suc2 plus_1_eq_Suc)
    from 2 3 have 4:"\<T> k (k' + (Suc nat)) = \<T> k (k' + nat) " by blast 
    from 2 3 assms have "\<J> k (k' + nat) = step k (\<T> k (k' + nat)) (\<J> k (k' + nat))" by simp
    with 4 have "\<T> k (k' + Suc (Suc nat)) = \<T> k (k' + (Suc nat))  
      \<and> \<J> k (k' + (Suc nat)) = \<J> k (k' + nat)" using step by simp
    with 2 have "\<T> k (k' + Suc (Suc nat)) = \<T> k k' \<and> \<J> k (k' + (Suc nat)) = \<J> k k'" by blast
    then  show ?thesis using Suc by blast
  qed
qed

(*easily holds*)


lemma \<J>_monotonicity:"n \<le> n' \<Longrightarrow> \<J> k n \<subseteq> \<J> k n'"
  apply(induct "n' - n") apply simp
  by (simp add: \<pi>_monotone lift_Suc_mono_le) 



lemma \<J>_final:
  assumes "invariant_T_top k s " " \<not>fst (step_I k s) \<noteq> fst s " "k \<le> length Doc" 
  shows "\<I> k = snd s \<and> \<I> k \<subseteq> All_top"
proof -
  obtain I T where def:"(T, I) = s" apply(cases s) by blast
  with assms have 1:"((I = step k T I) \<and>  (\<exists> k' . (\<J> k k' = I) \<and> (\<T> k k' = T))) \<and>
      T \<subseteq> TokensAt k I \<and> T \<subseteq> TokensAt_top k" and I_top:"I \<subseteq> All_top" 
    using invariant_T_top_def apply force using invariant_T_top_def assms def by auto
  then obtain k' where 2:"\<J> k k' = I \<and> (\<T> k k' = T)" by blast
  have "fst (step_I k s) = Tokens k T I" using def by force
  with assms(2) 2 have 3:"\<T> k (Suc k') = \<T> k k'" using def by force
  
  from 1 have 4:"\<J> k k' = step k (\<T> k k') (\<J> k k')" using 2 by simp
  { fix n
  from  step_I [OF 3 4] have "\<J> k (k' + n) = \<J> k k'" by blast
}
  then have "\<forall> n \<ge> k' . \<J> k n = \<J> k k'" 
    using nat_le_iff_add by auto
  then have "\<Union> { \<J> k n | n. n > k'} = \<Union> { \<J> k k' | n. n > k'}" 
    using le_eq_less_or_eq by blast
  then have 5:"\<Union> { \<J> k n | n. n > k'} = \<J> k k'" by auto
  have 6:"\<Union> { \<J> k n | n. n \<le> k'} = \<J> k k'" using \<J>_monotonicity by auto
  have "natUnion (\<J> k) = \<J> k k'" using  Union_cases [OF 5 6] 
    by (simp add: natUnion_def)
  with 5 show ?thesis using def 2 I_top  by force 
qed


fun meas_T_I::"nat \<Rightarrow> (('a, 'b, 'c) token set \<times> ('a, 'b) items)  \<Rightarrow> nat " where
"meas_T_I k (T, I)  = card {s . s \<in> TokensAt_top k \<and>   s \<notin> T}"

lemma meas_T_I_decreases:
  assumes "invariant_T_top k s" "fst (step_I k s) \<noteq> fst s" 
  shows "meas_T_I k (step_I k s) < meas_T_I k s"
proof -
  obtain T I where def:"(T, I) = s" apply(cases s) by blast
  with  assms(1) have "((I = step k T I) \<and>  (\<exists> k' . (\<J> k k' = I) \<and> (\<T> k k' = T)) 
    \<and> T \<subseteq> TokensAt k I \<and> T \<subseteq> TokensAt_top k \<and> I \<subseteq> All_top)" using invariant_T_top_def by force
  then obtain k' where  1:"\<T> k k'  \<subseteq> TokensAt k (\<J> k k')" and 2:"(\<J> k k' = I) \<and> (\<T> k k' = T)" 
      and top:"\<T> k k' \<subseteq> TokensAt_top k"by auto
  have step_def:"(\<T> k (Suc k')) =  Sel (\<T> k k') (TokensAt  k (\<J> k k'))" using Tokens_def by simp
  then have sub_set:"\<T> k k' \<subseteq> \<T> k (Suc k')" using 1 Sel_is_selector is_selector_def by blast

  have fin:"finite {s . s \<in> TokensAt_top k \<and>   s \<notin> (\<T> k k')}" using finite_TokensAt_top by simp
  have step_T:"(\<T> k (Suc k')) = fst (step_I k (T, I))" using 2 by auto
  with assms(2) have neq:"(\<T> k (Suc k')) \<noteq> (\<T> k k')" using 2 def by force
  from step_def have top':"(\<T> k (Suc k')) \<subseteq> TokensAt_top k" using TokensAt_top [where ?I="(\<J> k k')"] 
      Sel_is_selector is_selector_def 1 by blast
  then    have "(\<T> k k') \<subset> (\<T> k (Suc k'))" using sub_set neq by blast
  with top top' have sub:"{s . s \<in> TokensAt_top k \<and>   s \<notin> (\<T> k (Suc k'))} 
     \<subset>  {s . s \<in> TokensAt_top k \<and>   s \<notin> (\<T> k k')}" 
    by (smt (verit, best) Collect_mono_iff subset_iff subset_not_subset_eq)
  then have smaller:"card {s . s \<in> TokensAt_top k \<and>   s \<notin> (\<T> k (Suc k'))} 
     <  card{s . s \<in> TokensAt_top k \<and>   s \<notin> (\<T> k k')}" 
   using psubset_card_mono [OF fin sub] by blast
  have 3:"card {s . s \<in> TokensAt_top k \<and>   s \<notin> (\<T> k (Suc k'))} = meas_T_I k (step_I k s)"  
    using step_T def  by auto
  have 4:"card {s . s \<in> TokensAt_top k \<and>   s \<notin> (\<T> k k')} = meas_T_I k s" using 2 def by force
  from smaller show  ?thesis  using 3 4  by(simp del: \<T>.simps)
qed

lemma wf_T_I:"wf {(t, s). invariant_T_top k s \<and> fst (step_I k s) \<noteq> fst s \<and> t = step_I k s}"
  using wf_if_measure [where ?P="\<lambda> s . invariant_T_top k s \<and> fst (step_I k s) \<noteq> fst s" and ?g="step_I k" 
        and ?f= "meas_T_I k"] meas_T_I_decreases by simp

(*Initial*)
lemma init:
  assumes "Suc k \<le> length Doc " " \<I> k \<subseteq> All_top "
  shows " invariant_T_top (Suc k) ({}, \<J> (Suc k) 0)"
proof -
  have 1:"((\<exists> k' . (\<J> (Suc k) k' = \<J> (Suc k) 0) \<and> (\<T> (Suc k) k' = {})) 
    \<and> {} \<subseteq> TokensAt (Suc k) (\<J> (Suc k) 0) \<and> {}  \<subseteq> TokensAt_top (Suc k))" by fastforce
  have t:"\<forall>(t, c)\<in> {}. Suc k + length c \<le> length Doc" by blast
  have step:"\<J> (Suc k) 0  = \<pi> (Suc k) {} (\<I> k)" by simp
  then have 2:"\<J> (Suc k) 0  \<subseteq> All_top" using \<pi>_termination_All_top [OF assms(1) t assms(2)] by blast
  
  from step have  3:"(\<J> (Suc k) 0 = step (Suc k) {}  (\<J> (Suc k) 0))" 
      using \<pi>_termination_All_top [OF assms(1) t assms(2)] by simp
  from 1 2 3 show ?thesis using invariant_T_top_def by simp

qed
(*better use lex_prod I guess*)
lemma \<I>_k_step:"\<I> k \<subseteq> All_top \<Longrightarrow> (Suc k) \<le> length Doc \<Longrightarrow>\<I> (Suc k) = 
  snd (while (\<lambda> T.  fst (step_I  (Suc k) T) \<noteq> (fst T)) (step_I (Suc k)) ({}, \<J> (Suc k) 0)) \<and> \<I> (Suc k) \<subseteq> All_top"
  apply (rule while_rule_lemma [where   ?s =  "({}, \<J> (Suc k) 0)" and ?c="step_I (Suc k)" 
          and ?b="(\<lambda> TI.  fst (step_I  (Suc k) TI) \<noteq> fst TI)" and ?Q = "\<lambda> f . \<I> (Suc k)  = snd f 
    \<and> \<I> (Suc k) \<subseteq> All_top" and ?P="invariant_T_top (Suc k) "])
  using \<J>_step apply blast
  using \<J>_final apply blast
  using wf_T_I apply blast
  using init by blast

lemma \<I>_0_start:"invariant_T_top 0 ({}, \<J> 0 0)"
proof -
  have 1:"((\<exists> k' . (\<J> 0 k' = \<J> 0 0) \<and> (\<T> 0 k' = {})) 
    \<and> {} \<subseteq> TokensAt 0 (\<J> 0 0) \<and> {}  \<subseteq> TokensAt_top 0)" by fastforce
  have k:"0 \<le> length Doc" by simp
  have t:"\<forall>(t, c)\<in> {}. 0  + length c \<le> length Doc" by blast
  have step:"\<J> 0 0  = \<pi> 0 {} Init" by simp
  then have 2:"\<J> 0 0  \<subseteq> All_top" using \<pi>_termination_All_top [OF k t Init_sub_All_top'] by blast 
  from step have  3:"(\<J> 0 0 = step 0 {}  (\<J> 0 0))" 
      using \<pi>_termination_All_top [OF k t Init_sub_All_top'] by simp
  from 1 2 3 show ?thesis using invariant_T_top_def by simp
qed

lemma \<I>_0_code:"\<I> 0 = 
  snd (while (\<lambda> T.  fst (step_I 0  T) \<noteq> (fst T)) (step_I 0) ({}, \<J> 0 0)) \<and> \<I> 0 \<subseteq> All_top"
   apply (rule while_rule_lemma [where   ?s =  "({}, \<J> 0 0)" and ?c="step_I 0" 
          and ?b="(\<lambda> TI.  fst (step_I  0 TI) \<noteq> fst TI)" and ?Q = "\<lambda> f . \<I> 0  = snd f 
  \<and> \<I> 0 \<subseteq> All_top" and ?P="invariant_T_top 0 "])
  using \<J>_step apply blast
  using \<J>_final apply blast
  using wf_T_I apply blast
  using \<I>_0_start by blast
  thm  while_rule_lemma [where   ?s =  "({}, Init)" and ?c="step_I 0"
      and ?b="(\<lambda> TI.  fst (step_I  k TI) \<noteq> fst TI)" and ?Q = "\<lambda> f . \<I> k  = snd f " and ?P="invariant_T_top k "]

lemma \<I>_k_sub_All_top:"k \<le> length Doc \<Longrightarrow> \<I> k \<subseteq> All_top"
  apply(induct k) using \<I>_0_code apply blast using \<I>_k_step by auto

lemma \<J>_k_sub_\<I>_k:"\<J> k u \<subseteq> \<I> k"
  apply(simp add: natUnion_def) by blast


theorem final_code_equation:"k \<le> length Doc \<Longrightarrow>\<I> k = 
  snd (while (\<lambda> T.  fst (step_I k T) \<noteq> (fst T)) (step_I k) ({}, \<J> k 0)) \<and> \<I>  k \<subseteq> All_top"
  apply(induct k)  using \<I>_k_step \<I>_0_code by auto

theorem final_code_equation':"k \<le> length Doc \<Longrightarrow>\<I> k = 
  snd (while (\<lambda> T.  fst (step_I k T) \<noteq> (fst T)) (step_I k) ({}, \<J> k 0))"
  using final_code_equation by simp

(*non_empty: assumption \<longrightarrow> *)
(*have to keep \<I> there*)
(*assumption no nonempty strings should be more than enough 
  \<Longrightarrow> expand upon this*)

(*Base final proof on ll*)

(*what is the second nat about ? \<Longrightarrow> determinies termination*)
(*\<I> k all items at position k*)
(*by monotonicity of \<J> , monotonicity of \<T> is actually derived*)
theorem no_nonempty_tokens:"\<forall> (t, c ) \<in> Tokens k T I . length c > 0 "
  using Tokens_def Sel_is_nonempty non_empty_selector_def by metis

definition invariant_bin::"nat \<Rightarrow> ('a, 'b, 'c) token set \<Rightarrow> ('a, 'b) item set \<Rightarrow> ('a, 'b) item set \<Rightarrow> bool" where
"invariant_bin k T init I = (bin I k = bin init k \<and> bin (step k T I) k = bin I k)"

(*
theorem monotonicity:
  assumes "\<forall> A B . \<forall> (t, c) \<in> (Sel A B) . length c > 0"
  shows "TokensAt  k (\<J> k u) = TokensAt k (\<J> k 0)"
proof (induction u)
  case 0
  then show ?case by auto
next
  case (Suc u)
  then have "\<T> k (Suc u) = Sel (\<T> k u) (TokensAt  k (\<J> k u))" using Tokens_def by simp
  then have 1:"\<forall> (t, c) \<in> (\<T> k (Suc u)) . length c > 0" using assms by auto
  have "Suc u > 0" by simp 
  then have "TokensAt  k (\<J> k (u))  = TokensAt k (\<J> k (Suc u))" using 1 upper_tokens by fastforce  
  with Suc show ?case by simp
qed
*)
(*
theorem Token_monotonicity:
  assumes "u > 1" "\<forall> (t, c) \<in> \<T> k u. length c > 0"
  shows "\<T> k u = \<T> k (Suc u)"
proof -
  obtain u' where u_pred:"Suc u' = u" using assms 
    by (metis less_imp_Suc_add)  
  then have "bin (\<J> k u') k = bin (\<J> k  u) k" using non_empty_tokens assms by blast
  then have eq:"TokensAt  k (\<J> k u')  = TokensAt k (\<J> k u) " using TokensAt_def by auto
  have "\<T> k u = Sel (\<T> k u') (TokensAt  k (\<J> k u'))" using u_pred Tokens_def by auto
  have "\<T> k (Suc u) = Sel (\<T> k u) (TokensAt  k (\<J> k u'))" using eq Tokens_def by auto
  from Sel_is_selector is_selector_def have "(\<forall> A B. A \<subseteq> B \<longrightarrow> (A \<subseteq> Sel A B \<and> Sel A B \<subseteq> B))" 
  show ?thesis 
qed
*)
lemma no_string:
  assumes "t \<in> \<TT> " "l > length Doc"
  shows " Lex t Doc l  = {}"
proof - 
  have "is_lexer (Lex t)" using Lex_is_lexer assms by simp 
  then show ?thesis using is_lexer_def assms by auto
qed

lemma empty_symbols: 
  assumes "t \<in> \<TT> " 
  shows "Lex t Doc (length Doc)  = {} \<or> Lex t Doc (length Doc)  = {0}" 
proof - 
  have "is_lexer (Lex t)" using Lex_is_lexer assms by simp 
  then have "l \<in> Lex t Doc (length Doc) \<Longrightarrow> (length Doc) + l \<le> length Doc" using is_lexer_def by blast
  then show ?thesis using is_lexer_def assms 
    by (smt (verit, ccfv_SIG) \<open>is_lexer (Lex t)\<close> add_eq_self_zero 
        empty_subsetI le_eq_less_or_eq not_add_less1 psubsetE psubset_eq singleton_iff subset_eq)
qed



lemma is_terminal_':"is_terminal t \<Longrightarrow>t \<in> \<TT>"
  using \<TT>_def is_terminal_def
  by (metis imageI obj_sumE old.sum.simps(5) old.sum.simps(6))

lemma TokensAt_empty:"k' > length Doc \<Longrightarrow> TokensAt k' I = {}"
  using TokensAt_def is_terminal_' no_string by blast 

lemma Scan_top':"Scan {}  k  I =I" 
  using Scan_def by simp

(*Now prove that Scanning only goes so far*)
(*Tokens At should be rewritten*)

definition \<II> :: "('a, 'b) items"
where
  "\<II> = \<I> (length Doc)"

definition is_finished :: "('a, 'b) item \<Rightarrow> bool" where
  "is_finished x = (item_nonterminal x = \<SS> \<and> item_origin x = 0 \<and> item_end x = length Doc \<and> 
    is_complete x)"

(*can get item sets, but not the same for reconstruction*)
definition earley_recognised :: "bool"
where
  "earley_recognised = (\<exists> x \<in> \<II>. is_finished x)"

end

end 
