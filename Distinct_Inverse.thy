theory Distinct_Inverse
imports FreeGroupMain Cancellation  UniversalProperty
begin

text \<open>In this file, we prove that a non-trivial element of a free group does not equal 
its inverse\<close>

lemma cancels_transfer:
assumes "i > 0"
 and "cancels_to_1_at i (a#b#x) (a#y)"
 and "b \<noteq> inverse a"
shows "cancels_to_1_at (i - 1) (b#x) y"
  using assms
 proof(cases x)
   case Nil
   with assms show ?thesis unfolding cancels_to_1_at_def cancel_at_def by force
 next
   case (Cons c list)
   have i:"i - 1 \<ge> 0" by auto
   moreover then have "1 + (i - 1) < length (b # x)" using assms unfolding cancels_to_1_at_def
     by simp
   moreover then have "inverse ((b # x) ! (i - 1)) = (b # x) ! (1 + (i - 1))" 
     using i  assms unfolding cancels_to_1_at_def cancel_at_def by simp
   moreover then have "y = take (i - 1) (b # x) @ drop (2 + (i - 1)) (b # x)"
     using i assms Cons unfolding cancels_to_1_at_def cancel_at_def 
     by (metis One_nat_def Suc_pred append_Cons drop_Suc_Cons drop_drop gr_implies_not_zero list.sel(3) take_Cons')
   ultimately show ?thesis  unfolding cancels_to_1_at_def cancel_at_def by argo
 qed

lemma non_reduced_words_cancel:
  "\<not>(reduced wrd) \<longleftrightarrow> (\<exists>x. cancels_to_1 wrd x)"
proof
  assume asm:"\<not> (reduced wrd)"
  show "(\<exists>x. cancels_to_1 wrd x)"
    using asm
  proof(induction wrd rule:reduced.induct)
  case (3 g h wrd)
  then show ?case
  proof(cases "inverse g = h")
    case True
    then have "cancels_to_1_at 0 (g#h#wrd) wrd" using  Cons
        unfolding  cancels_to_1_at_def[of 0 "g#h#wrd" wrd]
        unfolding cancel_at_def take.simps(1) by simp
    then show ?thesis unfolding cancels_to_1_def by blast 
  next
    case False
    then have "g \<noteq> inverse h" using False 
      by (metis inverse_of_inverse)
    then obtain x i where "cancels_to_1_at i (h#wrd) x" using 3 unfolding cancels_to_1_def by fastforce
    then have "cancels_to_1_at (i+1) (g#h#wrd) (g#x)" unfolding cancels_to_1_at_def
      by (metis Suc_eq_plus1 add.assoc add_less_cancel_left append.simps(2) cancel_at_def drop_Suc_Cons length_Cons nth_Cons_Suc plus_1_eq_Suc take_Suc_Cons zero_le)
    then show ?thesis using cancels_transfer unfolding cancels_to_1_def by blast 
  qed
  qed (auto)+
next
  assume asm:"\<exists>x. cancels_to_1 wrd x"
  show "\<not>(reduced wrd)"
    using asm
  proof(induction wrd rule:reduced.induct)
    case 1
    then show ?case unfolding cancels_to_1_def cancels_to_1_at_def by simp
  next
    case (2 g)
    then show ?case unfolding cancels_to_1_def cancels_to_1_at_def by simp
  next
    case (3 g h wrd)
    then show ?case 
    proof(cases "g = inverse h")
      case False
      then have False':"h \<noteq> inverse g" 
        using inverse_of_inverse by blast
      obtain x i where x_i:"cancels_to_1_at i (g#h#wrd) x"  using 3(2) unfolding cancels_to_1_def
        by fast
      then have i:"i > 0" using False 
        by (metis cancels_to_1_at_def gr0I inverse_of_inverse nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc)
      obtain y where y:"x = g # y" 
        using x_i i  unfolding cancels_to_1_at_def 
        cancel_at_def 
        by (simp add: take_Cons')
      then have "cancels_to_1_at (i - 1) (h#wrd) y" using x_i cancels_transfer[of i g h wrd y] False'
        i by fastforce
      then have "\<not>(reduced (h#wrd))" using 3(1)[OF False] unfolding cancels_to_1_def by fast
      then show ?thesis by simp
    qed(auto)
  qed
qed

lemma not_reduced_sublist:
  assumes "\<not> (reduced ys)"
  shows "\<not> (reduced (xs@ys))"
  using assms 
proof(induction xs rule:reduced.induct)
  case (2 g)
  then show ?case 
    by (metis append_Cons append_Nil list.exhaust reduced.simps(1) reduced.simps(3))  
next
  case (3 g h wrd)
  then show ?case by (cases "g = inverse h", simp, simp add:3)
qed (simp)


lemma reduced_reverse:
  assumes "reduced (xs@[x])" 
      and "reduced (y#ys)"
      and "x \<noteq> inverse y" 
    shows "reduced (xs@[x]@(y#ys))"
proof(rule ccontr)
  assume asm:"\<not> (reduced (xs@[x]@(y#ys)))"
  then obtain wrd where wrd:"cancels_to_1 (xs@[x]@(y#ys)) wrd"
    using  non_reduced_words_cancel by blast
  then obtain i where i:"cancels_to_1_at i (xs@[x]@(y#ys)) wrd"
    unfolding cancels_to_1_def by blast
  then show False
  proof(cases "i < length (xs)")
    case True
    hence "((xs@[x]) ! i) =  (xs@[x]@(y#ys))!i" using i unfolding cancels_to_1_at_def 
      by (simp add: nth_append)
    moreover have "(xs @[x])! (i+ 1) =  (xs@[x]@(y#ys))!(i+1)"  using i unfolding cancels_to_1_at_def 
      by (metis True append_Cons discrete le_neq_implies_less nth_append nth_append_length)
    ultimately have "inverse ((xs@[x])!i) = (xs@[x])!(i+1)" using  i True unfolding cancels_to_1_at_def 
      by (metis Suc_eq_plus1  plus_1_eq_Suc)    
    then have  inv:"((xs@[x])!i) = inverse ((xs@[x])!(i+1))" using inverse_of_inverse by metis
    then have "drop i (xs@[x]) = ((xs@[x])!i)#((xs@[x])!(i+1))#(drop (i + 2) (xs@[x]))"
      using True 
      by (metis Cons_nth_drop_Suc Suc_eq_plus1 add_Suc_right discrete le_imp_less_Suc length_append_singleton less_imp_le_nat nat_1_add_1)
    then have nr_drop_i: "\<not> reduced (drop i (xs@[x]))" 
      using inv 
      by simp
    moreover have "(xs@[x]) = (take i (xs@[x]))@(drop i (xs@[x]))" 
      using True by simp
    then have "\<not> reduced (xs@[x])" using nr_drop_i not_reduced_sublist by metis 
    then show ?thesis using assms(1) by argo 
  next
    case False
    then have i_len:"i \<ge> length xs" by auto
    then show ?thesis 
    proof(cases "i = length xs")
      case True
      hence "x =  (xs@[x]@(y#ys))!i" using i unfolding cancels_to_1_at_def 
       by (simp add: nth_append)
      moreover have "y =  (xs@[x]@(y#ys))!(i+1)"  using i unfolding cancels_to_1_at_def 
        by (metis length_Cons True add_cancel_right_left list.size(3) nth_append_length nth_append_length_plus)
      ultimately have "inverse x = y" using  i True unfolding cancels_to_1_at_def
       by (metis Suc_eq_plus1  plus_1_eq_Suc)    
      then have  inv:"x = inverse y" using inverse_of_inverse by metis
      then show False using assms(3) by argo
    next
      case False
      define j where "j = i - length xs - 1"
      have i_len:"i > length xs" using i_len False by linarith
      hence "([y]@ys) !(i - length xs - 1) =  (xs@[x]@(y#ys))!i" using i 
        unfolding cancels_to_1_at_def 
        by (smt (verit, ccfv_threshold) One_nat_def Suc_pred add.commute append_Cons append_Nil le_add_diff_inverse less_imp_le_nat list.size(3) list.size(4) nth_append_length_plus plus_1_eq_Suc zero_less_diff)
      moreover have "([y]@ys)! (i - length xs) =  (xs@[x]@(y#ys))!(i+1)"  using i i_len
        unfolding cancels_to_1_at_def 
        by (smt (z3) Nat.le_imp_diff_is_add add_diff_cancel_left' append_Cons append_self_conv2 diff_commute diff_is_0_eq' diffs0_imp_equal le_add1 nat_less_le nth_Cons' nth_append)
      ultimately have "inverse (([y]@ys)!j) = ([y]@ys)!(j+1)" using  i False  unfolding cancels_to_1_at_def 
      j_def 
        by (metis One_nat_def Suc_eq_plus1 Suc_pred i_len plus_1_eq_Suc zero_less_diff)
     then have  inv:"(([y]@ys)!j) = inverse (([y]@ys)!(j+1))" using inverse_of_inverse by metis
    then have "drop j ([y]@ys) = (([y]@ys)!j)#(([y]@ys)!(j+1))#(drop (j + 2) ([y]@ys))"
      using False i unfolding j_def cancels_to_1_at_def
      by (smt (verit, ccfv_threshold) Cons_nth_drop_Suc add.commute add_Suc_right add_lessD1 add_less_cancel_left discrete i_len le_add_diff_inverse length_Cons length_append linorder_not_less nat_1_add_1 plus_1_eq_Suc)
    then have nr_drop_i: "\<not> reduced (drop j ([y]@ys))" 
      using inv 
      by simp
    moreover have "([y]@ys) = (take j ([y]@ys))@(drop j ([y]@ys))" 
      using False unfolding j_def by simp
    then have "\<not> reduced ([y]@ys)" using nr_drop_i not_reduced_sublist by metis 
    then show ?thesis using assms(2) by force
    qed
  qed  
qed

lemma reduced_wordinverses:
  assumes "reduced x"
  shows "reduced (wordinverse x)"
  using assms
proof(induction x rule: reduced.induct)
  case 1
  then show ?case by auto 
next
  case (2 g)
then show ?case by simp 
next
  case (3 g h wrd)
  then have "reduced (wordinverse (h#wrd))"by force
  then have "reduced ((wordinverse wrd)@[inverse h])" by fastforce
  moreover have "reduced ((inverse g)#[])" by auto
  moreover have "inverse h \<noteq> inverse (inverse g)" using inverse_of_inverse 3(2) 
    by (metis reduced.simps(3))
  ultimately show ?case using reduced_reverse by fastforce
qed

lemma eq_wordinv_imp: 
  assumes "xs = wordinverse xs"
   "reduced xs"
  shows "xs = []"
proof(cases xs)
  case (Cons y ys)
  then show ?thesis
  proof(cases "even (length xs)")
    case True
    obtain n where n:"length xs = 2*n" using True by auto
    then have "xs ! (n-1) = inverse (xs! n)" using True Cons
         assms(1) wordinverse_redef2[of xs] 
      by (smt (z3) One_nat_def Suc_pred add_diff_cancel_right' discrete length_greater_0_conv length_rev less_add_same_cancel2 less_imp_le_nat list.simps(3) mult_2 neq0_conv nth_map rev_nth)
    then have "cancels_to_1  xs ((take (n-1) xs)@(drop (n+1) xs))"
      unfolding cancels_to_1_def cancels_to_1_at_def using n Cons
      by (metis Cons_nth_drop_Suc One_nat_def Suc_eq_plus1 add_lessD1 assms(2) discrete id_take_nth_drop le_add_diff_inverse2 length_greater_0_conv less_add_same_cancel2 list.simps(3) mult_2 nat_0_less_mult_iff not_reduced_sublist reduced.simps(3))
    then have "\<not> (reduced xs)" using non_reduced_words_cancel by auto
    then show ?thesis using assms(2) by blast
  next
    case False
    obtain n where n:"length xs = 2*n + 1" using Cons False by auto
    then have "xs ! n = inverse (xs ! n)" using  Cons
         assms(1) wordinverse_redef2[of xs] 
      by (metis (no_types, lifting) Suc_eq_plus1 add_diff_cancel_right' combine_common_factor discrete le_add2 length_rev mult.left_neutral nth_map one_add_one rev_nth)
    then have " True = False"  
      apply (cases "snd (xs!n)") 
      apply(simp) 
      apply (metis inverse.simps(1) prod.collapse snd_conv)      
      by (metis inverse.simps(2) sndI surjective_pairing)
    then show ?thesis using Cons by simp
  qed
qed (auto)

lemma red_repelem:
  assumes "w \<in> (\<langle>S\<rangle> // (reln_tuple \<langle>S\<rangle>))"
  shows "\<exists>x \<in> w. reduced x \<and> ((reln_tuple \<langle>S\<rangle>)`` {x} = w)"
proof-
  obtain c where c: "w = (reln_tuple \<langle>S\<rangle>) `` {c}" by (meson assms quotientE)
  then have cs: "c \<in> \<langle>S\<rangle>" using assms by (metis proj_def proj_in_iff reln_equiv)
  obtain rc where rc: "rc = ((reduce^^(length c)) c)" by simp
  then have "reduced rc" by (simp add: reduced_iter_length)
  then have "c ~ rc" using rc cancels_imp_rel iter_cancels_to by auto
  moreover then have "rc \<in> \<langle>S\<rangle>" using cs rc using cancels_to_preserves iter_cancels_to by blast
  ultimately have crc: "(c, rc) \<in> reln_tuple \<langle>S\<rangle>" using cs reln_tuple_def by auto
  then have "((reln_tuple \<langle>S\<rangle>)`` {rc} = w)"using c by (smt (verit, ccfv_SIG) equiv_class_eq_iff reln_equiv)
  moreover then have "rc \<in> w" using c crc by simp
  ultimately show ?thesis using \<open>reduced rc\<close> by auto
qed

lemma(in group) not_eq_id:
  assumes  "x \<in> carrier (freegroup S)"
    and "x \<noteq> \<one>\<^bsub>(freegroup S)\<^esub>" 
  shows "[] \<notin> x"
  using assms unfolding freegroup_def reln_tuple_def quotient_def
  apply (simp) 
proof(rule ccontr)
  assume " \<not> [] \<notin> x"
  then have in_x:"[] \<in> x" by auto
  moreover have in_S:"[] \<in> \<langle>S\<rangle>"  unfolding freewords_on_def 
    by (simp add: words_on.empty)
  obtain xa where xa:"x = {y. xa ~ y \<and> y \<in> \<langle>S\<rangle>}" "xa \<in>  \<langle>S\<rangle>"
    using assms unfolding freegroup_def reln_tuple_def quotient_def 
    by (simp, blast)
  then have eq_xa:" xa ~ []" using in_x in_S by simp
  then have "x = \<one>\<^bsub>(freegroup S)\<^esub>" 
    unfolding freegroup_def reln_tuple_def quotient_def apply (simp)
  proof
    {fix a
     assume asm:"a \<in> x"
     then have a_prop:"xa ~ a" "a \<in> \<langle>S\<rangle>" using xa by simp+
     then have "a ~ []" using eq_xa 
       using reln.sym reln.trans by blast
     then have "a \<in> {y. [] ~ y \<and> [] \<in> \<langle>S\<rangle> \<and> y \<in> \<langle>S\<rangle>}"
       using in_S a_prop(2) reln.sym by force}
   then show " x \<subseteq> {y. [] ~ y \<and> [] \<in> \<langle>S\<rangle> \<and> y \<in> \<langle>S\<rangle>}" by blast
 next
    {fix a
     assume asm:"a \<in> {y. [] ~ y \<and> [] \<in> \<langle>S\<rangle> \<and> y \<in> \<langle>S\<rangle>}"
     then have a_prop:"[] ~ a" "a \<in> \<langle>S\<rangle>" using xa by simp+
     then have "a ~ xa" using eq_xa 
       using reln.sym reln.trans by blast
     then have "a \<in> x" 
       using in_S a_prop(2) xa reln.sym by force}
   then show " {y. [] ~ y \<and> [] \<in> \<langle>S\<rangle> \<and> y \<in> \<langle>S\<rangle>} \<subseteq> x" by blast
 qed
  then show False using assms(2) by simp
qed


lemma(in group) not_eq_inv:
  assumes "x \<in> carrier (freegroup S)" "x \<noteq> \<one>\<^bsub>(freegroup S)\<^esub>"
  shows "x \<noteq> inv\<^bsub>(freegroup S)\<^esub> x"
proof
  assume asm:"x = inv\<^bsub>F\<^bsub>S\<^esub>\<^esub> x"
  obtain g where g:"x =  (reln_tuple \<langle>S\<rangle>) `` {g}" "g \<in> \<langle>S\<rangle>" "reduced g"
    using assms red_repelem unfolding freegroup_def reln_tuple_def apply simp
    by auto
  moreover have g_inv:"inv\<^bsub>F\<^bsub>S\<^esub>\<^esub> x = (reln_tuple \<langle>S\<rangle>) `` {wordinverse g}"
    using wordinverse_inv[OF assms(1) g(1)] .
  moreover have red_g_inv:"reduced (wordinverse g)" 
    using assms(1) g(1,3) wordinverse_inv sledgehammer
    by (simp add:  reduced_wordinverses)
  have " g \<in> (reln_tuple \<langle>S\<rangle>) `` {g}" using asm g(1,2) 
    unfolding reln_tuple_def Image_def apply(simp)
    by auto
  moreover then  have "g \<in> (reln_tuple \<langle>S\<rangle>) `` {wordinverse g}"
    using asm g_inv g g(2) by auto
  then have "wordinverse g ~ g"  using g(1) unfolding reln_tuple_def Image_def
    by simp
  then have "g ~ wordinverse g" using reln.simps by auto
  then have "cancels_eq g (wordinverse g)" using reln_imp_cancels by auto
  then have "g = wordinverse g" using g(3) red_g_inv reduced_cancel_eq by auto
  then have "g = []" using eq_wordinv_imp g(3) red_g_inv by blast
  show False using assms not_eq_id g 
    using \<open>g = []\<close> \<open>g \<in> reln_tuple \<langle>S\<rangle> `` {wordinverse g}\<close> by auto
qed

    
end