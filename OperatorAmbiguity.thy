

theory OperatorAmbiguity
  imports "LocalLexing2.Derivations" Containers.Containers

begin
locale OperatorAmbiguity = CFG +
  fixes Priority :: "(('a, 'b) rule \<times> ('a, 'b) rule) set"
  fixes Left :: "(('a, 'b) rule \<times> ('a, 'b) rule) set"
  fixes Right:: "(('a, 'b) rule \<times> ('a, 'b) rule) set"
  assumes Priority_between_alternates: "\<forall>((N1, r1), (N2, r2)) \<in> Priority. (N1 = N2)"
  assumes Priority_valid: "\<forall>((N1, r1), (N2, r2)) \<in> Priority.  ((N1 = hd r1 \<and>hd r1 = last r2) \<or> ((N1 = hd r1 \<and> last r1 = hd r2)))"
  assumes Priority_is_strictpart: "antisym Priority \<and> trans Priority \<and> irrefl Priority"
  assumes Left_between_alternates: "\<forall>((N1, r1), (N2, r2)) \<in> Left. (N1 = N2)"
  assumes Left_valid: "\<forall>((N1, r1), (N2, r2)) \<in> Left.  (N1 = hd r1\<and>hd r2 = hd r1 \<and>hd r1 = last r1  \<and>hd r2 = last r2)"
  assumes Right_between_alternates: "\<forall>((N1, r1), (N2, r2)) \<in> Right. (N1 = N2)"
  assumes Right_valid: "\<forall>((N1, r1), (N2, r2)) \<in> Right.  (N1 = hd r1\<and>hd r2 = hd r1 \<and>hd r1 = last r1  \<and>hd r2 = last r2)"
  assumes Relation_safety: "(Left \<inter> Right = {}) \<and> (Priority \<inter> Right = {}) \<and> (Left \<inter> Priority = {})"
begin

(*how to best define those kind of derivations? \<longrightarrow> need derivation sequence*)
(*how do I define a precedence left derivation?
 
! !precedencederivations have to be defined on their subtrees specifically*)
(*actual way it works is all subtrees are precedenceleft derivations and root does not have any of the other*)
(*along right/left spine?*)


fun "derive"::"('a, 'b) sentence \<Rightarrow> nat \<Rightarrow> ('a, 'b) rule \<Rightarrow> ('a, 'b)sentence" where
"derive a n (N, r) = (take (n-1) a)@r@(drop n a) "

fun valid::" ('a, 'b) sentence \<Rightarrow> ('a, 'b) rule \<Rightarrow> bool" where
"valid s (N, r) =  ((last r = N) \<and>(\<exists>w . is_word w \<and> s = w@[N]@r))"

(*one level for associativity, all others along, right/left spine*)

(*this happens until \<Longrightarrow> remember position of any other nonterminal and iterate all get applied to it*)
(*splits derivation such that all children in leftmost expansion of leading rule are in left*)
fun left_children::"('a, 'b) rule \<Rightarrow> ('a, 'b) derivation \<Rightarrow> ('a, 'b) derivation \<times> ('a, 'b) derivation" where
"left_children (_, r) D = (if \<not> is_nonterminal (hd r) then ([],  D) 
                      else 
                        snd (foldr 
    (\<lambda>(n, S, R) (N, left, right). if (n \<le> N) then (n+ length R,left@[(n,S, R)], right) else  (n ,left, right@[(n,S, R)])) D (0, [], [])))"

(*drop all until one derivation gets applied to the rightmost terminal*)
(*potential bug length r*)
(*splits derivatioin such that all children in rightmost expansion of leading rule are in right*)
fun right_children::"('a, 'b) rule \<Rightarrow> ('a, 'b) derivation \<Rightarrow> ('a, 'b) derivation \<times> ('a, 'b) derivation" where
"right_children (_, r) D = (if \<not> is_nonterminal (last r) then ([],  D) 
                      else 
                        snd (foldr 
    (\<lambda>(n, S, R) (N, left, right). if (n < N) then (n+ length R,left@[(n,S, R)], right) else  (n ,left, right@[(n,S, R)])) D (length r, [], [])))"

lemma left_children_safe: "fst (left_children r D)@(snd (left_children r D)) = D"
  apply(induct D)
   apply(auto)
  sorry

lemma right_children_safe: "fst (right_children r D)@(snd (right_children r D)) = D"
  apply(induct D)
   apply(auto)
  sorry


fun rightspine::"('a, 'b) rule \<Rightarrow> ('a, 'b) derivation \<Rightarrow> ('a, 'b) rule set" where 
"rightspine (S, r) D = set (map snd (filter (\<lambda>(_, N, _). N = S)(takeWhile (\<lambda>(n, N, r). is_nonterminal (hd r)) (snd (right_children (S, r) D)))))"

(*
fun leftspine::"sentence \<Rightarrow> rule \<Rightarrow> derivation \<Rightarrow> rule set" where
"leftspine s (S, r) D = set (snd (foldr (\<lambda>(n, rule) (a, d). let s = derive a n rule in (s, if valid s (S, r) then rule#d else d))  D (s@[S]@r ,[]))) "
*)

fun rightexpansion::"('a, 'b) derivation \<Rightarrow> ('a, 'b) derivation" where
"rightexpansion [] = []" |
"rightexpansion ((n, H, r)#D) = (if \<not> is_nonterminal (last r) then [] else 
      snd (foldr (\<lambda>(n1, H1, r1) (N, s). if n1 = N then 
          (if  is_nonterminal (last r1) then ((N + length r1), (n1, H1, r1)#s) else (N -1, (n1, H1, r1)#s))
          else (N, s)) D (n + length r, [])))" 

fun leftspine::"('a, 'b) rule \<Rightarrow> ('a, 'b) derivation \<Rightarrow> ('a, 'b) rule set" where
"leftspine (S, r) D = (if \<not> is_nonterminal (hd r) then {}  else set  (map snd (rightexpansion D)))"

fun PrecedenceLeftDerivation :: "('a, 'b) sentence \<Rightarrow> ('a, 'b) derivation \<Rightarrow> ('a, 'b) sentence \<Rightarrow> bool"
where
  "PrecedenceLeftDerivation a [] b = (a = b)"
| "PrecedenceLeftDerivation a (d#D) b = (\<exists> x. LeftDerives1 a (fst d) (snd d) x \<and> PrecedenceLeftDerivation x D b \<and> 
   (leftspine (snd d) D  \<inter> ((Priority) `` {snd d}) = {}) \<and>  (rightspine (snd d) D  \<inter> ((Priority) `` {snd d}) = {}))"
(*rotations are not as easy \<Longrightarrow> have to show that no new conflicts arise*)
(*or can we prove safety in another way?*)
(*E\<alpha> > \<beta>E*)
fun ambiguous1::"('a, 'b) symbol \<Rightarrow> ('a, 'b) rule \<Rightarrow>('a, 'b)  rule \<Rightarrow> bool" where
"ambiguous1 s (N1, r1) (N2, r2)  = ((s = N1) \<and>(N1 = N2) \<and> (N1 = hd r1 \<and>hd r1 = last r2))"
(*\<beta>E > E\<alpha>*)
fun ambiguous2::"('a, 'b) symbol \<Rightarrow> ('a, 'b) rule \<Rightarrow> ('a, 'b) rule \<Rightarrow> bool" where
"ambiguous2 s (N1, r1) (N2, r2)  = ( (s = N1) \<and>(N1 = N2) \<and> (N1 = hd r2 \<and>hd r2 = last r1))"

(*need additional lemma for derivation shift*)
(*have to prove that left most holds*)
(*direction of application should not *)
(*keep a look at derivation_swap in derivation
*)
(*prove this by induction on D*)
(*is_Word append*)
lemma nth_append':"(a@l) ! (n + length a) = l ! n  "
  apply(induct a, auto)
  done

lemma Derives1_append:"is_sentence u \<Longrightarrow> Derives1 a n r b \<Longrightarrow> Derives1 (u@a) (n + length u) r (u@b)"
  apply(auto simp add: Derives1_def)
  apply(rule_tac x="u@x" in exI)
  apply(rule_tac x="y" in exI)
  apply(auto simp add: is_sentence_concat)
  done
lemma LeftDerives1_append_word:"LeftDerives1 a i r b \<Longrightarrow> is_word u \<Longrightarrow> LeftDerives1 (u@a) (i + (length u)) r (u@b)"
  apply(auto simp add: Derives1_append  LeftDerives1_def nth_append leftmost_def)
done
(*possible take rules used: first subgoal is on shifting on operator*)
lemma LeftDerivation_append_word:"is_word u \<Longrightarrow> LeftDerivation a D b \<Longrightarrow> LeftDerivation (u@a) (derivation_shift D 0 (length u)) (u@b)"
  apply(auto simp add: derivation_shift_def Derivation_take)
  apply(induct D arbitrary:u a b)
  apply(auto )
  apply(rule_tac x="u@x" in exI)
  apply(simp add:  LeftDerives1_append_word)
  done

lemma nth_take:"n < n1 \<Longrightarrow>  (take n1 l) ! n =  l ! n  "
  apply(induct l, auto)
  done

lemma nth_concat:"n < length l \<Longrightarrow>   (take (length l) (l@a)) ! n = (l@a) ! n"
  by(rule nth_take)
 
 
lemma Derives1_concat:"is_sentence d \<Longrightarrow> Derives1 a i r b \<Longrightarrow> Derives1 (a@d) i r (b@d)"
  apply(auto simp add: Derives1_def)
  apply(rule_tac x="x" in exI)
  apply(rule_tac x="y@d" in exI)
  apply(auto simp add: is_sentence_concat)
  done

lemma LeftDerives1_concat:"is_sentence d \<Longrightarrow> LeftDerives1 a i r b \<Longrightarrow> LeftDerives1 (a@d) i r (b@d)"
  apply(auto simp add: LeftDerives1_def leftmost_def Derives1_concat nth_append)
done

lemma LeftDerivation_concat: "is_sentence d \<Longrightarrow> LeftDerivation a D b \<Longrightarrow> LeftDerivation (a@d) D (b@d)"
  apply(induct D arbitrary: a b d)
   apply(auto )
  apply(rule_tac x="x@d" in exI)
  apply(simp add: LeftDerives1_concat)
 done

theorem type1_derivation:
  assumes E:"is_nonterminal E" and "(E, \<alpha>@[E]) \<in> \<RR>" and "(E, E#\<beta>)  \<in> \<RR>"  
    and v:"is_word v" and 
mu:"is_word \<mu>" and root:"LeftDerivation [E]  D1 (\<mu>@[E])" and first_word:"LeftDerivation \<alpha> D2 v" and tail:"LeftDerivation [E] D3 (E#\<gamma>)"
  and gamma:"is_sentence \<gamma>"
  shows "LeftDerivation [E]  (D1@[((length \<mu>), (E, \<alpha>@[E]))]@(derivation_shift D2 0 (length \<mu>))@(derivation_shift D3 0 (length (\<mu>@v)))@[((length (\<mu>@v)), (E, E#\<beta>))]) (\<mu>@v@E#\<beta>@\<gamma>)"
proof -
  from assms have alphaE:"LeftDerives1 [E] (0) (E, \<alpha>@[E]) (\<alpha>@[E])" by (simp add: LeftDerives1_def leftmost_def Derives1_def)
  from assms have Ebeta:"LeftDerives1 [E] (0) (E, E#\<beta>) (E#\<beta>)" by (simp add: LeftDerives1_def leftmost_def Derives1_def)
  from mu and v have muv:"is_word (\<mu>@v)" by simp
  from alphaE and mu have "LeftDerives1 (\<mu>@[E]) (length \<mu>) (E, \<alpha>@[E])  (\<mu>@\<alpha>@[E])" using LeftDerives1_append_word by fastforce
  from this and root have seq1: "LeftDerivation [E] (D1@[((length \<mu>), (E, \<alpha>@[E]))])  (\<mu>@\<alpha>@[E])" by (auto simp add: LeftDerivation_LeftDerives1 )
  from first_word and mu have "LeftDerivation  (\<mu>@\<alpha>) (derivation_shift D2 0 (length \<mu>)) (\<mu>@v)" by (auto simp add: LeftDerivation_append_word)
  from this and E have "LeftDerivation  (\<mu>@\<alpha>@[E]) (derivation_shift D2 0 (length \<mu>)) (\<mu>@v@[E])" using  LeftDerivation_concat apply(force simp: is_sentence_def is_symbol_def) done
  from seq1 and this have seq2:"LeftDerivation [E] (D1@[((length \<mu>), (E, \<alpha>@[E]))]@(derivation_shift D2 0 (length \<mu>)))  (\<mu>@v@[E])" using LeftDerivation_implies_append apply(force) done
  from tail and muv have "LeftDerivation (\<mu>@v@[E]) (derivation_shift D3 0 (length (\<mu>@v))) (\<mu>@v@(E#\<gamma>))" using LeftDerivation_append_word by fastforce
  from this and seq2 have seq3:"LeftDerivation [E]  (D1@[((length \<mu>), (E, \<alpha>@[E]))]@(derivation_shift D2 0 (length \<mu>))@(derivation_shift D3 0 (length (\<mu>@v))))(\<mu>@v@(E#\<gamma>))" using LeftDerivation_append  by fastforce
  from Ebeta and gamma have "LeftDerives1 (E#\<gamma>) 0 (E, E#\<beta>)  (E#\<beta>@\<gamma>)" using LeftDerives1_concat by fastforce
  from this and muv have  "LeftDerives1 (\<mu>@v@E#\<gamma>) (length (\<mu>@v)) (E, E#\<beta>)  (\<mu>@v@E#\<beta>@\<gamma>)" using LeftDerives1_append_word by fastforce
  from this and seq3 have "LeftDerivation [E]  (D1@[((length \<mu>), (E, \<alpha>@[E]))]@(derivation_shift D2 0 (length \<mu>))@(derivation_shift D3 0 (length (\<mu>@v)))@[((length (\<mu>@v)), (E, E#\<beta>))]) (\<mu>@v@E#\<beta>@\<gamma>)" using LeftDerivation_append by auto
  from this show ?thesis by auto
qed


theorem type2_derivation:
  assumes E:"is_nonterminal E" and "(E, \<alpha>@[E]) \<in> \<RR>" and beta:"(E, E#\<beta>)  \<in> \<RR>"  
    and v:"is_word v" and 
mu:"is_word \<mu>" and root:"LeftDerivation [E]  D1 (\<mu>@[E])" and first_word:"LeftDerivation \<alpha> D2 v" and tail:"LeftDerivation [E] D3 (E#\<gamma>)"
  and gamma:"is_sentence \<gamma>"
shows  "LeftDerivation [E] (D3@[(0, (E, E#\<beta>))]@D1@[( (length \<mu>),(E, \<alpha>@[E]))]@(derivation_shift D2 0 (length \<mu>)))  (\<mu>@v@[E]@\<beta>@\<gamma>)"
proof -
  from assms have alphaE:"LeftDerives1 [E] (0) (E, \<alpha>@[E]) (\<alpha>@[E])" by (simp add: LeftDerives1_def leftmost_def Derives1_def)
  from assms have Ebeta:"LeftDerives1 [E] (0) (E, E#\<beta>) (E#\<beta>)" by (simp add: LeftDerives1_def leftmost_def Derives1_def)
  from mu and v have muv:"is_word (\<mu>@v)" by simp
  from beta have "is_sentence (E#\<beta>)" by (simp)
  from this have "is_sentence \<beta>" by (simp add: is_sentence_def)
  from this and gamma have betagamma:"is_sentence (\<beta>@\<gamma>)" by (simp add: is_sentence_concat)
  from betagamma and E have Ebetagamma:"is_sentence ([E]@\<beta>@\<gamma>)" by (simp add: is_sentence_def)
  from Ebeta and gamma have "LeftDerives1 (E#\<gamma>) 0 (E, E#\<beta>)  (E#\<beta>@\<gamma>)" using LeftDerives1_concat by fastforce
  from this and tail have  seq1:"LeftDerivation [E] (D3@[(0, (E, E#\<beta>))]) (E#\<beta>@\<gamma>)" by (auto simp add: LeftDerivation_LeftDerives1)
  from betagamma and root have "LeftDerivation (E#\<beta>@\<gamma>) D1 (\<mu>@E#\<beta>@\<gamma>)" using LeftDerivation_concat by fastforce
  from this and seq1 have seq2:"LeftDerivation  [E] (D3@[(0, (E, E#\<beta>))]@D1)  (\<mu>@E#\<beta>@\<gamma>)" using LeftDerivation_implies_append by fastforce
  from mu and alphaE have "LeftDerives1 (\<mu>@[E]) (length \<mu>) (E, \<alpha>@[E]) (\<mu>@\<alpha>@[E])" using LeftDerives1_append_word by fastforce
  from betagamma and this  have "LeftDerives1 (\<mu>@[E]@\<beta>@\<gamma>) (length \<mu>) (E, \<alpha>@[E]) (\<mu>@\<alpha>@[E]@\<beta>@\<gamma>)" using LeftDerives1_concat by fastforce
  from this and seq2 have seq3:"LeftDerivation  [E] (D3@[(0, (E, E#\<beta>))]@D1@[( (length \<mu>),(E, \<alpha>@[E]))])  (\<mu>@\<alpha>@[E]@\<beta>@\<gamma>)" using LeftDerivation_LeftDerives1 by fastforce
  from first_word and mu have "LeftDerivation (\<mu>@\<alpha>) (derivation_shift D2 0 (length \<mu>)) (\<mu>@v)" using LeftDerivation_append_word by fastforce
  from this and Ebetagamma have "LeftDerivation (\<mu>@\<alpha>@[E]@\<beta>@\<gamma>) (derivation_shift D2 0 (length \<mu>))  (\<mu>@v@[E]@\<beta>@\<gamma>)" using LeftDerivation_concat by fastforce
  from this and seq3 have "LeftDerivation [E] (D3@[(0, (E, E#\<beta>))]@D1@[( (length \<mu>),(E, \<alpha>@[E]))]@(derivation_shift D2 0 (length \<mu>)))  (\<mu>@v@[E]@\<beta>@\<gamma>)" using LeftDerivation_implies_append by fastforce
  from this show ?thesis by auto
qed

definition leftrecursive::"('a, 'b) symbol \<Rightarrow> ('a, 'b) rule \<Rightarrow> bool" where
"leftrecursive s R =  (snd R \<noteq> [] \<and> is_nonterminal s \<and> ((fst R) = s) \<and> (last (snd R) = s))"

(*separation of sequence using LeftDerivation_append?*)
(*imply existence of other rotation*)
(*might have to fix E as start symbol \<Longrightarrow> any other way to enable rotation(?)*)
(*maybe not additional condition for splitting?*)
fun split_derivation::"('a, 'b) derivation \<Rightarrow> (nat \<times> ('a, 'b) rule) \<Rightarrow> (('a, 'b)derivation \<times>  ('a, 'b)derivation)" where
"split_derivation D d = (takeWhile (\<lambda> s. s \<noteq> d) D , dropWhile (\<lambda> s. s \<noteq> d) D)"


lemma is_sentence_drop:
  assumes "is_sentence s"
  shows "is_sentence (drop i s)"
proof -
  have l:"set (drop i s) \<subseteq> set s" using set_drop_subset by fast
  from assms have "\<forall> x \<in> set s . is_symbol x" using list_all_def is_sentence_def by metis
  with l have "\<forall> x \<in> set (drop i s) . is_symbol x" by blast
  then  show ?thesis using list_all_def is_sentence_def by metis
qed

lemma takedrop1: " take (i-j) (drop j n) = drop j (take i n)"
  apply(auto simp add: set_def drop_take )
  done

lemma list_all_tl:"list_all a p \<Longrightarrow> list_all a (tl p)"
  apply(induct p)
   apply(auto simp: tl_def)
  done
lemma is_word_drop:"is_word u \<Longrightarrow>  is_word ( drop j u)"
  apply(auto simp add: is_word_def)
  apply(induct j arbitrary: u)
   apply(auto simp add: drop_0)
  apply(auto simp add: drop_Suc )
  apply(simp add: list_all_tl)
  done
lemma take_invar: "take i u = take (i+j-j) u"
  apply(induct i)
   apply(auto simp add:  take_Cons )
  done
lemma is_word_drop1: "j \<le> i \<Longrightarrow>is_word (take i  u) \<Longrightarrow>  is_word (take (i - j) (drop j u))"
  apply(auto simp: take_drop ) 
  using is_word_drop by simp

lemma wordsmallerleftmost:
  assumes  word:"is_word (take i u)"  and left:" leftmost j u"  and valid:"i \<le> length u"
  shows "i \<le> j"
proof (rule ccontr)
  assume "\<not> i \<le> j"
  from this have greater:"j < i" by auto
  from left have nonterm:"is_word (take j u) \<and> is_nonterminal (u ! j) \<and> (j < length u)"apply(auto simp: leftmost_def) done
  from this and greater have "(take i u) ! j = u ! j" by auto
  from this and nonterm have non_terminal:"is_nonterminal ((take i u) ! j)" by auto
  from greater and valid have "(length (take i u)) > j" by auto
  from this and word and greater have terminal:"is_terminal ((take i u) ! j)" by (auto simp add: is_word_def list_all_length)
  from this and non_terminal show "False"  using is_terminal_nonterminal by fastforce
qed
lemma LeftDerives1_take:
  assumes "LeftDerives1 u n r v \<and> is_word (take j u) \<and> j \<le> length u "
  shows "LeftDerives1 (drop j  u) (n-j) r (drop j v)"
proof -
  from assms have leftmost:"leftmost n u" by (simp add: LeftDerives1_def)
  from this and assms have less:"j \<le> n" using wordsmallerleftmost by fastforce
  from assms obtain x y N \<alpha> where 
         deriv1:"u = x @ [N] @ y \<and> v = x @ \<alpha> @ y \<and> is_sentence x \<and> is_sentence y \<and>(N, \<alpha>) \<in> \<RR> \<and> r = (N, \<alpha>) \<and> n = length x" apply(simp add:  LeftDerives1_def Derives1_def) by blast
  from this and less have "j \<le> length x" by auto
  from  this and deriv1 have lem:"Derives1 (drop j u) (n -j) r (drop j v)" apply (simp add:Derives1_def leftmost_def) apply(rule_tac x="drop j x" in exI)
    apply(rule_tac x="y" in exI) apply(auto) apply(simp add: is_sentence_drop) done
  from leftmost have smallerlength:"n < length u" by (simp add: leftmost_def)
  from deriv1 have c:"length x <= length v" by auto
  from leftmost and less have "leftmost (n -j) (drop j u)" apply (auto simp add: leftmost_def is_word_drop)  using is_word_drop1 by fastforce
  from lem  and this  have head:"LeftDerives1 (drop j u) (n -j) r (drop j v)" by (auto simp add: LeftDerives1_def)
  from this show ?thesis by auto
  qed
lemma LeftDerivation_take:
  shows "LeftDerivation u D  v \<Longrightarrow> is_word(take j u) \<and> j \<le> length u\<Longrightarrow> LeftDerivation (drop j  u) (derivation_shift D j 0) (drop j v)" 
proof (induction D arbitrary: u v)
  case Nil 
  
  with Nil have " u = v" by auto
  with this show ?case by (auto simp add: derivation_shift_def)
next
  case (Cons d D)
  from Cons have "(\<exists> x. LeftDerives1 u (fst d) (snd d) x \<and> LeftDerivation x D v)" by auto
  from this obtain c where first:"LeftDerives1 u (fst d) (snd d) c" and tail:"LeftDerivation c D v" by blast
  from this have fst:"leftmost (fst d) u" by (simp add: LeftDerives1_def)
  from fst and Cons have less:"j \<le> fst d" using wordsmallerleftmost by fastforce 
  from first obtain x y N \<alpha> where 
         deriv1:"u = x @ [N] @ y \<and> c = x @ \<alpha> @ y \<and> is_sentence x \<and> is_sentence y \<and>(N, \<alpha>) \<in> \<RR> \<and> (snd d) = (N, \<alpha>) \<and> (fst d) = length x" apply(simp add:  LeftDerives1_def Derives1_def) by blast
  from this and less have smaller_word:"j \<le> length x" by auto
  from  this and deriv1 have lem:"Derives1 (drop j u) ((fst d) -j) (snd d) (drop j c)" apply (simp add:Derives1_def leftmost_def) apply(rule_tac x="drop j x" in exI)
    apply(rule_tac x="y" in exI) apply(auto) apply(simp add: is_sentence_drop) done
  from fst have smallerlength:"(fst d) < length u" by (simp add: leftmost_def)
  from deriv1 have c:"length x <= length c" by auto
  from fst and less have "leftmost ((fst d) -j) (drop j u)" apply (auto simp add: leftmost_def is_word_drop)  using is_word_drop1 by fastforce
  from lem  and this  have head:"LeftDerives1 (drop j u) ((fst d) -j) (snd d) (drop j c)" by (auto simp add: LeftDerives1_def) 
  from first and deriv1 have "is_word x" by (auto simp: LeftDerives1_def)
  from smaller_word and deriv1 have " take j  c = take j u" by auto
  from this  and smaller_word and Cons and c have "is_word (take j c) \<and> j \<le> length c" by auto
  from this and tail and Cons have INH:"LeftDerivation  (drop j c) (derivation_shift D j 0) (drop j v)" by fastforce
  from this and head show ?case by fastforce
qed

lemma split_preserves:"(fst(split_derivation D d))@(snd(split_derivation D d)) = D"
  apply(auto)
  done

  
(*s look to be leftrecursive anyways*)

lemma rotatetype1_type2_0:
  assumes valid:"is_leftderivation s" and s_deriv:"s=\<mu>@[E] \<and> is_word \<mu>" and 
    leftrecursive:"leftrecursive E (snd d)" and deriv:"LeftDerivation s (d#D) s1" and 
    conflict:"\<exists>r1. r1 \<in> rightspine (snd d) D " 
  shows head:"\<exists> D1 .LeftDerivation [E]  D1 (\<mu>@[E])" and "LeftDerivation \<mu> D2 v \<and> is_word v" and tail:"LeftDerivation [E] D3 (E#\<gamma>)" 
proof - 
  from valid have "\<exists> D0 . LeftDerivation [\<SS>] D0 s" apply (simp add: is_leftderivation_def) using  leftderives_implies_LeftDerivation by fastforce 
  from this obtain D0 where "LeftDerivation [\<SS>] D0 s" by blast
  from deriv have " \<exists> x.(LeftDerives1 s (fst d) (snd d) x \<and> LeftDerivation x D s1)" by auto
  obtain \<alpha> where "\<alpha> = (snd (snd d))" by blast
  from s_deriv have l1:"drop (length \<mu>) s = [E]" by auto
  from s_deriv have l2:"is_word (take (length \<mu>) s) \<and> length \<mu> < length s" by auto
  from l1 and l2 and deriv have lderiv:"LeftDerivation (drop (length \<mu>) s) (derivation_shift (d#D) (length \<mu>) 0) (drop (length \<mu>) s1)" using LeftDerivation_take by fastforce
  (*prove that we have a follow up derivation with \<alpha>@[E]*)
  from this have "LeftDerivation (drop (length \<mu>) s) ((fst d - (length \<mu>), snd d)#(derivation_shift D (length \<mu>) 0)) (drop (length \<mu>) s1)" by simp
  from this have " \<exists> x.(LeftDerives1  (drop (length \<mu>) s) (fst d - (length \<mu>)) (snd d) x \<and> LeftDerivation x  (derivation_shift (D) (length \<mu>) 0) (drop (length \<mu>)s1))" by auto
  then obtain x1 where x1':"LeftDerives1 (drop (length \<mu>) s) (fst d - (length \<mu>)) (snd d) x1" and x2':"LeftDerivation x1  (derivation_shift (D) (length \<mu>) 0) (drop (length \<mu>) s1)" by blast
  from l1 and l2 and x1' have l3': "LeftDerives1 [E] (fst d - (length \<mu>)) (snd d) x1" using LeftDerives1_take by fastforce
  from x1' have "snd d \<in> \<RR>" by (auto simp: LeftDerives1_def)
  from this and  leftrecursive have l4:"LeftDerives1 [E] 0 (snd d) (snd (snd d))" apply(auto simp add: LeftDerives1_def Derives1_def leftmost_def leftrecursive_def) apply(rule_tac x="[]" in exI) apply(rule_tac x="[]" in exI) apply(rule_tac x="fst (snd d)" in exI)
    apply(auto)    done
  from l3' and l4 have "0 = fst d- (length \<mu>)" apply (auto simp add: LeftDerives1_def) using leftmost_unique by fastforce
  from this and l4 and l3' have eq:"x1 = (snd (snd d))" apply(auto simp: LeftDerives1_def) using Derives1_unique_dest by fastforce
  obtain \<alpha>E where aE:"\<alpha>E = (snd (snd d))" by blast
  from this and leftrecursive have last:"last (\<alpha>E)= E" by (auto simp add: leftrecursive_def)
  from aE and  leftrecursive have nonempty:"\<alpha>E \<noteq> []" by (auto simp add: leftrecursive_def last_def)
  from aE  obtain \<alpha> where "\<alpha>  = butlast \<alpha>E"  by blast
  from this and last and nonempty  have "\<alpha>@[E] = \<alpha>E" by auto
  from this and aE and eq have aE1:"x1 = (\<alpha>@[E])" by auto
  from this and l4 and eq have "LeftDerives1 [E] 0 (snd d) (\<alpha>@[E])" by auto  
  from aE1 and x2' have "LeftDerivation (\<alpha>@[E]) (derivation_shift D (length \<mu>) 0) (drop (length \<mu>) s1)" by auto
  obtain D' where "D' = derivation_shift D (length \<mu>) 0" by blast

  show  "\<exists>D1. LeftDerivation [E] D1 (\<mu> @ [E])" sorry
  show "LeftDerivation \<mu> D2 v \<and> is_word v" sorry
  show "LeftDerivation [E] D3 (E # \<gamma>)" sorry
qed


lemma rotatetype1_type2:
  assumes valid:"is_leftderivation s" and s_deriv:"is_word (take (length s -1) s) \<and> is_nonterminal (last s)  "and leftrecursive:"leftrecursive E (snd d)" and deriv:"LeftDerivation s (d#D) s1" and " \<exists>r1. r1 \<in> leftspine (snd d) D " 
  shows "\<exists> D1 .LeftDerivation [E]  D1 (\<mu>@[E]) \<and> is_word \<mu>" and "LeftDerivation \<alpha> D2 v" and tail':"LeftDerivation [E] D3 (E#\<gamma>)" 
proof - 

  show  "\<exists>D1. LeftDerivation [E] D1 (\<mu> @ [E]) \<and> is_word \<mu>" sorry
  show "LeftDerivation \<alpha> D2 v" sorry
  show "LeftDerivation [E] D3 (E # \<gamma>)" sorry
qed
(*prove theorems that enable a swap given an ambiguous rule pairing \<Longrightarrow> i.e. this left spine, right spine thing*)
(*transitivity *)
theorem soundness: 
  shows  "LeftDerivation s D s1 \<Longrightarrow>\<exists> D1. PrecedenceLeftDerivation s D1  s1"
proof (induction D arbitrary: s s1)
  case Nil
  from Nil  have "s = s1" by auto
  with this show ?case apply (rule_tac x="[]" in exI) by auto
next
  case (Cons d D)
  then show ?case sorry
qed
(*alternative formulation of safety, formalize removal scheme*)

(*theorem safety:
  sorry
  *)
(*by induction on length of derivation sequences*)

(*completeness relies on total order though*)
theorem completeness:"PrecedenceLeftDerivation s D1 s1 \<Longrightarrow> PrecedenceLeftDerivation s D2 s2 \<Longrightarrow> D1 = D2" 
  sorry
end

end