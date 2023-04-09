theory NielsenSchreier
imports N_Properties Minimal Main Freegroup_with_Basis
begin   

text \<open>This file contains the formalisation of Nielsen Schreier\<close>

text \<open>We define N reduced set as follows\<close>

definition N_reduced ("N")
  where
"N_reduced A S = ((\<forall>xs \<in> (red_rep S) ` (union_inv A S). N0 xs) \<and>
                  (\<forall>xs \<in> (red_rep S) ` (union_inv A S). 
                      \<forall>ys \<in> (red_rep S) ` (union_inv A S). N1 xs ys) \<and> 
                  (\<forall>xs \<in> (red_rep S) ` (union_inv A S). 
                      \<forall>ys \<in> (red_rep S) ` (union_inv A S). 
                         \<forall> zs \<in> (red_rep S) ` (union_inv A S).
                             N2 xs ys zs))"



lemma N_reduced_X: assumes "G \<le> freegroup S"
  shows "N_reduced (X' (SG (freegroup S) G) S) S"
proof-
  have N0: "((\<forall>x \<in> (red_rep S) ` (union_inv  (X' (SG (freegroup S) G) S) S). N0 x))"
    using assms N0 by blast
  moreover have N1: "\<forall>x \<in> (red_rep S) ` (union_inv (X' (SG (freegroup S) G) S) S).
                      \<forall>y \<in> (red_rep S) ` (union_inv (X' (SG (freegroup S) G) S) S).
                               N1 x y"
    using assms N1 by blast
  moreover have "\<forall>x \<in> (red_rep S) ` (union_inv (X' (SG (freegroup S) G) S) S).
                    \<forall>y \<in> (red_rep S) ` (union_inv (X' (SG (freegroup S) G) S) S).
                      \<forall>z \<in> (red_rep S) ` (union_inv (X' (SG (freegroup S) G) S) S).
                        N2 x y z"
    using N0 N1 N2 assms by blast
  ultimately show ?thesis unfolding N_reduced_def by blast
qed

lemma id_notin_union_inv_X:
  assumes "G \<le> (freegroup S)"
  shows "\<forall>x \<in>  (union_inv  (X' (SG (freegroup S) G) S) S). x \<noteq> \<one>\<^bsub>freegroup S\<^esub>"
proof(rule ccontr)
  assume "\<not> (\<forall>x\<in>union_inv (X' (SG F\<^bsub>S\<^esub> G) S) S. x \<noteq> \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>)"
  then obtain x where x:"x \<in> union_inv (X' (SG F\<^bsub>S\<^esub> G) S) S" "x = \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" by simp
  hence "x = reln_tuple \<langle>S\<rangle> `` {[]}" using freegroup_def[of S] by simp
  moreover have "reduced []" by auto
  ultimately have "red_rep S x = []"
    unfolding red_rep_def using red_repI[of x S "[]"]
    x unfolding freegroup_def[of "S"] union_inv_def X'_def SG_def 
    by (simp add: freewords_on_def quotientI red_rep_def words_on.intros(1))
  thus False using x N_reduced_X[OF assms] unfolding N_reduced_def 
    using N0_def by blast
qed


lemma min_set_exists:
  assumes "G \<le> (freegroup S)"
  shows "\<exists>A. A = minimal_set (X' (SG (freegroup S) G) S) S" 
  by simp

lemma union_inv_eq_minimal: 
  assumes "G \<le> (freegroup S)"
  shows "union_inv (X' (SG (freegroup S) G) S) S 
                  = union_inv (minimal_set (X' (SG (freegroup S) G) S) S) S"
proof-
  let ?Q =  "\<lambda> Y . (Y \<subseteq>   (X' (SG (freegroup S) G) S) 
        \<and>  Y \<inter> (m_inv (freegroup S) ` Y) = {} 
        \<and> union_inv Y S = union_inv (X' (SG (freegroup S) G) S) S)" 
  obtain A where S:"A \<subseteq>  (X' (SG (freegroup S) G) S) " 
                   "A \<inter> (m_inv (freegroup S) ` A) = {}"
          "union_inv (X' (SG (freegroup S) G) S) S  = union_inv A S"
    using group.existence_of_minimal[OF freegroup_is_group] 
    by (smt (verit, del_insts) G'_def UnCI X'_def assms dual_order.trans gen_span.intros(1) mem_Collect_eq one_SG subgroup.mem_carrier subset_eq union_inv_def union_inv_sub_H) 
  hence Q_S:"?Q A" by argo
  hence "?Q (minimal_set (X' (SG (freegroup S) G) S) S)" unfolding minimal_set_def using someI
    by (metis (mono_tags, lifting))
  then show ?thesis by argo
qed

lemma minimal_set_empty_intersection: 
  assumes "G \<le> (freegroup S)"
  shows "(minimal_set (X' (SG (freegroup S) G) S) S)
      \<inter>(m_inv (freegroup S) ` (minimal_set (X' (SG (freegroup S) G) S) S)) = {}"
proof-
  let ?Q =  "\<lambda> Y . (Y \<subseteq>   (X' (SG (freegroup S) G) S) 
        \<and>  Y \<inter> (m_inv (freegroup S) ` Y) = {} 
        \<and> union_inv Y S = union_inv (X' (SG (freegroup S) G) S)  S)" 
  obtain A where S:" A \<subseteq>  (X' (SG (freegroup S) G) S) " "A \<inter> (m_inv (freegroup S) ` A) = {}"
          "union_inv (X' (SG (freegroup S) G) S) S  = union_inv A S"
    using group.existence_of_minimal[OF freegroup_is_group] 
    by (smt (verit, del_insts) G'_def UnCI X'_def assms dual_order.trans gen_span.intros(1) 
          mem_Collect_eq one_SG subgroup.mem_carrier subset_eq union_inv_def union_inv_sub_H) 
  hence Q_S:"?Q A" by argo
  hence "?Q (minimal_set (X' (SG (freegroup S) G) S) S)" unfolding minimal_set_def using someI
    by (metis (mono_tags, lifting))
  then show ?thesis by argo
qed

lemma minimal_set_in_carrier: 
  assumes "G \<le> (freegroup S)"
  shows "(minimal_set (X' (SG (freegroup S) G) S) S) \<subseteq> carrier (freegroup S)"
proof-
  let ?Q =  "\<lambda> Y . (Y \<subseteq>   (X' (SG (freegroup S) G) S) 
        \<and>  Y \<inter> (m_inv (freegroup S) ` Y) = {} 
        \<and> union_inv Y S = union_inv (X' (SG (freegroup S) G) S)  S)" 
  obtain A where S:" A \<subseteq>  (X' (SG (freegroup S) G) S)" "A \<inter> (m_inv (freegroup S) ` A) = {}"
          "union_inv (X' (SG (freegroup S) G) S) S  = union_inv A S"
    using group.existence_of_minimal[OF freegroup_is_group] 
    by (smt (verit, del_insts) G'_def UnCI X'_def assms dual_order.trans gen_span.intros(1) 
          mem_Collect_eq one_SG subgroup.mem_carrier subset_eq union_inv_def union_inv_sub_H) 
  hence Q_S:"?Q A" by argo
  hence "?Q (minimal_set (X' (SG (freegroup S) G) S) S)" unfolding minimal_set_def using someI
    by (metis (mono_tags, lifting))
  hence "(minimal_set (X' (SG (freegroup S) G) S) S) \<subseteq>  (X' (SG (freegroup S) G) S)" by argo
  thus ?thesis using assms unfolding X'_def SG_def 
    using subgroup.subset by fastforce
qed

lemma N_reduced_minimal:
  assumes "G \<le> (freegroup S)"
  shows "N_reduced (minimal_set (X' (SG (freegroup S) G) S) S) S" 
  using union_inv_eq_minimal  unfolding N_reduced_def 
    using N_reduced_X N_reduced_def assms by blast 

lemma union_inv_eq_span:
  assumes "union_inv A S = union_inv B S"
  shows "\<langle>A\<rangle>\<^bsub>freegroup S\<^esub> = \<langle>B\<rangle>\<^bsub>freegroup S\<^esub>"
proof(rule equalityI)
  show " \<langle>A\<rangle>\<^bsub>freegroup S\<^esub> \<subseteq> \<langle>B\<rangle>\<^bsub>freegroup S\<^esub>" unfolding union_inv_def
  proof
    fix x
    assume x:"x \<in> \<langle>A\<rangle>\<^bsub>freegroup S\<^esub>"
    show "x \<in>  \<langle>B\<rangle>\<^bsub>freegroup S\<^esub>" using x
    proof(induction rule:gen_span.induct)
      case gen_one
      then show ?case by auto 
    next
      case (gen_gens x)
      then show ?case using assms unfolding union_inv_def 
        by (metis (mono_tags, opaque_lifting) Un_iff gen_span.gen_gens gen_span.gen_inv imageE)
    next
      case (gen_inv x)
      then show ?case 
        by (simp add: gen_span.gen_inv)
    next
      case (gen_mult x y)
      then show ?case 
        by (simp add: gen_span.gen_mult) 
    qed
  qed
next
 show " \<langle>B\<rangle>\<^bsub>freegroup S\<^esub> \<subseteq> \<langle>A\<rangle>\<^bsub>freegroup S\<^esub>" unfolding union_inv_def
  proof
    fix x
    assume x:"x \<in> \<langle>B\<rangle>\<^bsub>freegroup S\<^esub>"
    show "x \<in>  \<langle>A\<rangle>\<^bsub>freegroup S\<^esub>" using x
    proof(induction rule:gen_span.induct) 
      case gen_one
      then show ?case by auto 
    next
      case (gen_gens x)
      then show ?case using assms unfolding union_inv_def 
        by (metis (mono_tags, opaque_lifting) Un_iff gen_span.gen_gens gen_span.gen_inv imageE)
    next
      case (gen_inv x)
      then show ?case 
        by (simp add: gen_span.gen_inv)
    next
      case (gen_mult x y)
      then show ?case 
        by (simp add: gen_span.gen_mult) 
    qed
  qed
qed

lemma min_set_eq_span:
  assumes "G \<le> (freegroup S)"
  shows "\<langle>(minimal_set (X' (SG (freegroup S) G) S) S)\<rangle>\<^bsub>(freegroup S)\<^esub> 
    =  \<langle>(X' (SG (freegroup S) G) S)\<rangle>\<^bsub>(freegroup S)\<^esub>"
  using N_reduced_minimal union_inv_eq_span union_inv_eq_minimal 
  using assms by blast
 
lemma (in group) carrier_eq_minimal:
  assumes "H \<le> freegroup S"
  shows "\<langle>(minimal_set (X' (SG (freegroup S) H) S) S)\<rangle>\<^bsub>freegroup S\<^esub> = H"
proof-
  let ?Y = "(X' (SG (freegroup S) H) S)"
  have 1:"\<langle>?Y\<rangle>\<^bsub>(SG (freegroup S) H)\<^esub> = carrier (SG (freegroup S) H)"
    using span_X_SG_eq_SG assms 
    by (simp add: span_X_SG_eq_SG assms)  
   have carr:"carrier (SG (freegroup S) H) = H" unfolding SG_def 
      by simp
   have 2:"\<langle>?Y\<rangle>\<^bsub>(SG (freegroup S) H)\<^esub> = \<langle>?Y\<rangle>\<^bsub>(freegroup S)\<^esub>"
  proof
      show  "\<langle>?Y\<rangle>\<^bsub>(SG (freegroup S) H)\<^esub> \<subseteq> \<langle>?Y\<rangle> \<^bsub>(freegroup S)\<^esub>" 
      proof(rule subsetI)
        fix x
        assume x:"x \<in> \<langle>X' (SG F\<^bsub>S\<^esub> H) S\<rangle>\<^bsub>SG F\<^bsub>S\<^esub> H\<^esub>"
        show "x \<in> \<langle>X' (SG F\<^bsub>S\<^esub> H) S\<rangle>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" using x
        proof(induction x rule:gen_span.induct)
          case gen_one
          then show ?case 
            by (metis gen_span.gen_one one_SG)  
        next
          case (gen_gens x)
          then show ?case 
            by (simp add: gen_span.gen_gens)  
        next
          case (gen_inv x)
          then show ?case 
            by (metis "1" assms carr freegroup_is_group gen_span.gen_inv inv_SG)  
        next
          case (gen_mult x y)
          then show ?case 
            by (metis gen_span.gen_mult mult_SG) 
        qed
      qed
    next
      show  "\<langle>?Y\<rangle>\<^bsub>(freegroup S)\<^esub> \<subseteq> \<langle>?Y\<rangle>\<^bsub>(SG (freegroup S) H)\<^esub>" 
      proof
        fix x
        assume "x \<in> \<langle>?Y\<rangle>\<^bsub>(freegroup S)\<^esub>"
        thus "x \<in> \<langle>?Y\<rangle>\<^bsub>(SG (freegroup S) H)\<^esub>"
        proof(induction x rule:gen_span.induct)
          case gen_one
          then show ?case using assms
            unfolding SG_def X'_def 
            by (metis (mono_tags, lifting) SG_def gen_span.gen_one one_SG)
        next
          case (gen_gens x)
          then show ?case 
            by (simp add: gen_span.gen_gens)  
        next
          case (gen_inv x)
          then show ?case using  gen_span.gen_inv[OF gen_inv(2)]  
                group.m_inv_consistent[OF "freegroup_is_group" assms] carr unfolding X'_def 
            by (metis (mono_tags, lifting) SG_def 1 gen_inv.IH)
        next
          case (gen_mult x y)
          then show ?case using gen_span.gen_mult[OF gen_mult(3,4)] 
             group.subgroup_mult_equality[OF "freegroup_is_group" assms] carr unfolding X'_def SG_def
            by simp
        qed 
      qed
    qed
  show ?thesis using 1  HOL.sym[OF 2] min_set_eq_span[OF assms] carr by argo
qed

lemma(in group) minimal_implies_non_id:
  assumes "H \<le> freegroup S"
  shows "\<forall>ws \<in> \<langle>(minimal_set (X' (SG (freegroup S) H) S) S)\<rangle>\<^bsub>freegroup S\<^esub>. 
       non_reducible (freegroup S) (minimal_set (X' (SG (freegroup S) H) S) S) ws 
                  \<longrightarrow> ws \<noteq> \<one>\<^bsub>freegroup S\<^esub>"
proof
  fix w
  assume w_in:"w \<in> \<langle>minimal_set (X' (SG F\<^bsub>S\<^esub> H) S) S\<rangle>\<^bsub>freegroup S\<^esub>"
  show "non_reducible (freegroup S) (minimal_set (X' (SG (freegroup S) H) S) S) w 
                  \<longrightarrow> w \<noteq> \<one>\<^bsub>freegroup S\<^esub>"
  proof
    assume asm:"non_reducible F\<^bsub>S\<^esub> (minimal_set (X' (SG (freegroup S) H) S) S) w"
    define Y where "Y = (minimal_set (X' (SG (freegroup S) H) S) S)"
    hence "non_reducible (freegroup S) Y w" using asm by auto      
    then obtain ls where ls:"w = monoid.m_concat (freegroup S) ls" "(ls \<noteq> [])" 
                          "\<forall>x \<in> set ls. x \<in> Y \<union> m_inv (freegroup S) ` Y" 
                 "(length ls = 1) \<or>(\<forall>i \<le> (length ls)-2 . ls!i \<noteq> inv\<^bsub>freegroup S\<^esub> (ls!(i+1)))"
      unfolding non_reducible_def by auto
    from ls have ls_in:"set ls \<subseteq> carrier (freegroup S)" unfolding Y_def 
      using minimal_set_in_carrier[OF assms] 
      by (metis (no_types, lifting) assms subgroup.subset subset_eq union_inv_def union_inv_eq_minimal union_inv_sub_H)
    define ls0 where "ls0 =  (map (red_rep S) ls)"  
    hence w_eq:"w = reln_tuple \<langle>S\<rangle> `` {l_concat ls0}" 
      using ls(1) ls_in 
      by (simp add: m_concat_to_l_concat)
    then show "w \<noteq> \<one>\<^bsub>freegroup S\<^esub>"
    proof(cases "length ls = 1")
      case True
      then obtain s where s:"ls = [s]" "s \<in> union_inv Y S"  unfolding ls0_def 
        using one_list unfolding union_inv_def
        by (metis list.set_intros(1) ls(3))
      hence "s \<noteq> \<one> \<^bsub>freegroup S\<^esub>"  using id_notin_union_inv_X[OF assms]
        unfolding Y_def 
        by (simp add: assms union_inv_eq_minimal)
      thus ?thesis using ls(1) s(1) 
        using ls_in m_concat_singleton by force  
    next
      case False
      define B where "B = (red_rep S) ` union_inv Y S" 
      have subs_B:"B \<subseteq> (red_rep S) ` (carrier (freegroup S))" unfolding B_def
        Y_def using  minimal_set_in_carrier[OF assms] 
        by (metis assms image_mono union_inv_clos union_inv_eq_minimal)
      moreover have "\<forall>x \<in> B. N0 x" unfolding B_def Y_def using N_reduced_minimal[OF assms]
        unfolding N_reduced_def by argo
      moreover have "\<forall>x \<in> B. \<forall>y \<in> B. N1 x y"
        unfolding B_def Y_def using N_reduced_minimal[OF assms]
        unfolding N_reduced_def by argo
      moreover have "\<forall>x \<in> B. \<forall>y \<in> B. \<forall>z \<in> B. N2 x y z" 
        unfolding B_def Y_def using N_reduced_minimal[OF assms]
        unfolding N_reduced_def by argo
      moreover have "ls0 \<noteq> []" unfolding ls0_def using ls(2) by simp
      moreover have set_ls0:"set ls0 \<subseteq> B" unfolding B_def ls0_def using ls(3) unfolding union_inv_def
        by force
      moreover have "\<forall>i < (length ls0 - 1). (ls0!i) \<noteq> (wordinverse (ls0!(i+1)))"
      proof(rule ccontr)
        assume "\<not> (\<forall>i < (length ls0 - 1). (ls0!i) \<noteq> (wordinverse (ls0!(i+1))))"
        then obtain i where i:"i < length ls0 -1" "ls0!i = (wordinverse (ls0!(i+1)))"
          by fastforce
        moreover have len:"length ls0 \<ge> 2" using False ls(2) unfolding ls0_def 
          by (metis One_nat_def le_less_linear length_greater_0_conv length_map less_2_cases_iff neq0_conv)
        ultimately have i_leq:"i \<le> length ls0 - 2" by auto
        from i(2) have rel:"((ls0!i)@(ls0!(i+1))) ~ []" using i(2) 
          using FreeGroupMain.inverse_wordinverse by auto
        have in_carri:"ls!i \<in> carrier (freegroup S)" using i_leq len ls0_def len False ls_in
          by (metis add_lessD1 i(1) length_map less_diff_conv nth_mem subset_iff)
        have red_rep_i:"ls0!i = red_rep S (ls!i)" using ls0_def i_leq len False ls_in
          by auto
        hence ls_i_ls0_i:"ls!i = reln_tuple \<langle>S\<rangle> `` {ls0!i}" using red_rep_the
          in_carri unfolding freegroup_def apply simp 
          by blast
        have 1:"ls0!i \<in> \<langle>S\<rangle>" using  redrep_in[OF in_carri] red_rep_i by auto     
        have in_carrSi:"ls!(i+1) \<in> carrier (freegroup S)" 
          using i_leq len ls0_def len False ls_in
          by (metis add_lessD1 i(1) length_map less_diff_conv nth_mem subset_iff)
        have red_rep_Si:"ls0!(i+1) = red_rep S (ls!(i+1))" 
          using ls0_def i_leq len False ls_in
          by auto
        hence ls_Si_ls0_Si:"ls!(i+1) = reln_tuple \<langle>S\<rangle> `` {ls0!(i+1)}" 
          using red_rep_the in_carrSi unfolding freegroup_def by (simp, blast)
        have 2:"ls0!(i+1) \<in> \<langle>S\<rangle>" using  redrep_in[OF in_carri] red_rep_i 
          using in_carrSi red_rep_Si redrep_in by auto 
        have "(ls!i)\<otimes>\<^bsub>freegroup S\<^esub>(ls!(i+1)) = reln_tuple \<langle>S\<rangle> `` ({((ls0!i)@(ls0!(i+1)))})"
          unfolding ls0_def unfolding red_rep_def using ls_i_ls0_i ls_Si_ls0_Si freegroup_def[of A] proj_append_wd[OF 1 2]
          by (metis (no_types, lifting) False i(2) i_leq in_carrSi length_map ls(4) ls0_def wordinverse_inv)
        hence id_eq:"(ls!i)\<otimes>\<^bsub>freegroup S\<^esub>(ls!(i+1)) = \<one>\<^bsub>freegroup S\<^esub>" using rel freegroup_def
          by (metis False i(2) i_leq in_carrSi length_map ls(4) ls0_def ls_Si_ls0_Si ls_i_ls0_i wordinverse_inv)
        hence "(ls!i) = inv\<^bsub>freegroup S\<^esub>(ls!(i+1))" 
          using group.inv_equality[OF "freegroup_is_group" id_eq in_carrSi in_carri]
          by simp
        then show False using False ls(4) i_leq 
          using ls0_def by force  
      qed
      ultimately have "\<not> (l_concat ls0 ~ [])" using n_reduced_cancel by blast
      thus ?thesis unfolding w_eq 
      by (simp add: append_equivred_span ls0_def ls_in word_problem_not_eq_id)    
    qed
    qed
qed
 
      
lemma(in group) subgp_of_freegroup_is_fg_with_basis:
  assumes "H \<le> (freegroup S)"
  shows "fg_with_basis (SG (freegroup S) H) (minimal_set (X' (SG (freegroup S) H) S) S)"
proof-
  define Y where  "Y = (minimal_set (X' (SG (freegroup S) H) S) S)"
  hence 1:"Y \<inter> (m_inv (freegroup S) ` Y) = {}" using minimal_set_empty_intersection[OF assms] by auto
  have 2:"Y \<subseteq> carrier (freegroup S)" using minimal_set_in_carrier[OF assms] unfolding Y_def
    by auto
  have 3:"\<forall>w \<in> \<langle>Y\<rangle>\<^bsub>freegroup S\<^esub>. non_reducible (freegroup S) Y w \<longrightarrow> w \<noteq> \<one>\<^bsub>freegroup S\<^esub>"
    using minimal_implies_non_id[OF assms] unfolding Y_def .
  thus "fg_with_basis (SG (freegroup S) H) (minimal_set (X' (SG (freegroup S) H) S) S)"
   using group.fg_with_basis_eq_cond 1 2  freegroup_is_group[of "S"]
   unfolding Y_def using carrier_eq_minimal[OF assms] unfolding SG_def 
   by metis
qed

lemma(in group) assumes "x \<in> carrier G" "y \<in> carrier G"
  "x \<otimes>\<^bsub>G\<^esub> y= \<one>" 
shows "x = inv\<^bsub>G\<^esub> y"
  using assms 
  using inv_equality by blast


text\<open>The Nielsen Schreier Theorem is formalised as follows. The notation 
for a subgroup, is on the lines of formalisation of group theory in HOL-Algebra 
library.\<close>

theorem(in group) Nielsen_Schreier:
  assumes "H \<le> (freegroup S)"
  shows "is_freegroup ((freegroup S)\<lparr>carrier := H\<rparr>)"
  using subgp_of_freegroup_is_fg_with_basis[OF assms] fg_with_basis_is_free 
  unfolding SG_def 
  by blast

end