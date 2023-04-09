theory Minimal
imports FreeGroupMain Distinct_Inverse 
begin

text \<open>This file contains of the lemma, which states that given a subset X of the
group such that identity does not belong to X, there exists a subset Y of X, such that union of Y with its set of inverses
 equals the union of X with its set of inverses, but Y does not contain any
common elements with its set of inverses. It relies on Zorn's lemma, and is used in 
the proof of Nielsen-Achreier, to find the subset of N-reduced set of a subgroup, 
which generates the subgroup. 
\<close>
 
definition union_inv
  where
"union_inv A S \<equiv> A \<union> (m_inv (freegroup S) ` A)"

lemma inv_inv_G:
  assumes "group G" "x \<in> carrier G"
   shows "inv\<^bsub>G\<^esub> (inv\<^bsub>G\<^esub> x) = x"
  using assms 
  by simp

lemma inv_in_A:
  assumes "x \<in> (m_inv G ` A)" "x \<in> carrier G" "A \<subseteq> carrier G" "group G"
  shows "inv\<^bsub>G\<^esub> x \<in> A"
proof-
 obtain y where y:"x = m_inv G y" "y \<in> A" using assms(1) by force
 have "y = m_inv  G x" using inv_inv_G assms(2,4) unfolding y 
   by (metis assms(3) in_mono y(2))
  then show ?thesis using y(2) by blast
qed

lemma intersection_lemma:
  assumes "S \<inter> (f ` S) = {}"
      and "x \<notin> S"
      and "f x \<notin> S"
      and "x \<notin> f ` S"
      and "x \<noteq> f x"
    shows "(S \<union> {x}) \<inter> (f ` (S \<union> { x})) = {}"
  using assms 
proof-
  have "(S \<union> {x}) \<inter> (f ` (S \<union> { x})) = (S \<union> {x}) \<inter> ((f  ` S) \<union> {f x})"
    by force
  moreover then have "... =  (S  \<inter> ((f  ` S) \<union> {f x})) \<union> ({x} \<inter> ((f  ` S) \<union> {f x}))"
    by blast
  moreover then have "... = (S  \<inter> (f  ` S)) \<union> (S  \<inter> {f x})  \<union> ({x} \<inter> ((f  ` S)) \<union> ({x} \<inter> {f x}))" 
    by fast
  moreover then have "... =  ({x} \<inter> ((f  ` S)) \<union> ({x} \<inter> {f x}))" 
    using assms by simp
  moreover then have "... = {}" using assms by blast
  ultimately show ?thesis by simp
qed

definition minimal_set
  where
"minimal_set A S = (SOME X. X \<subseteq> A \<and>  X \<inter> (m_inv (freegroup S) ` X) = {} 
                       \<and> union_inv A S = union_inv X S)"

lemma (in group) one_not_in_inv:
assumes "A \<subseteq> carrier (freegroup S)"
          "\<one>\<^bsub>freegroup S\<^esub> \<notin> A"
shows  "\<one>\<^bsub>freegroup S\<^esub> \<notin>  m_inv (freegroup S) `A"
proof(rule ccontr)
  assume asm:"\<not> \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub> \<notin> m_inv F\<^bsub>S\<^esub> ` A"
  then have "\<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub> \<in> m_inv F\<^bsub>S\<^esub> ` A" by auto
  then obtain x where x:"\<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub> \<otimes>\<^bsub>F\<^bsub>S\<^esub>\<^esub> x = \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" "x \<in> A"
    unfolding m_inv_def image_def apply simp 
    by (meson \<open>\<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub> \<in> m_inv F\<^bsub>S\<^esub> ` A\<close> assms(1) freegroup_is_group group.r_inv group.subgroup_self inv_in_A subgroup.one_closed)
  have "x = \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" using  x(1) x(2) assms(2) 
    by (meson assms(1) freegroup_is_group gen_span.gen_one group.l_cancel_one span_liftgen subsetD)
  then show False using x(2) assms(2) by argo
qed

lemma (in group) existence_of_minimal:
  assumes "A \<subseteq> carrier (freegroup S)"
          "\<one>\<^bsub>freegroup S\<^esub> \<notin> A"
        shows "\<exists>X. X \<subseteq> A \<and> X \<inter> (m_inv (freegroup S) ` X) = {} 
                \<and> union_inv A S = union_inv X S"
proof-
  have one_notin:"\<one>\<^bsub>freegroup S\<^esub> \<notin>  m_inv (freegroup S) `A" using one_not_in_inv[OF assms]  .
  define Y where "Y = {X. X \<subseteq> A \<and>  X \<inter> (m_inv (freegroup S) ` X) = {}}"
   {fix C
    assume C:"subset.chain Y C"
    then have 1:"(\<Union> C) \<subseteq> A" using C unfolding Y_def subset.chain_def by blast
     have 11:"(\<Union> C)  \<inter> (m_inv (freegroup S) ` (\<Union> C) ) = {}" 
     proof(rule ccontr)
       assume asm:"\<Union> C \<inter> m_inv (freegroup S) ` \<Union> C \<noteq> {}"
       then obtain x where x:"x \<in> \<Union> C \<inter> m_inv (freegroup S) ` \<Union> C" by blast
       then have x_in:"x \<in> m_inv (freegroup S) ` \<Union> C" using IntD2 by blast
       then have 2:"inv\<^bsub>(freegroup S)\<^esub> x \<in>  \<Union> C" using inv_in_A[OF x_in]
           freegroup_is_group[of S] 1 assms by fastforce
       moreover have "x \<in> \<Union> C" using x IntD1 by blast
       then obtain P Q where P_Q:"P \<in> C" "Q \<in> C" "x \<in> P" "inv\<^bsub>(freegroup S)\<^esub> x \<in> Q"
         using 2 by blast
       then have Or:"P \<subseteq> Q \<or>  Q \<subseteq> P" using C unfolding subset.chain_def 
         by (meson C subset_chain_def)
       have "P \<subseteq> Q \<Longrightarrow> x \<in> Q \<and> m_inv (freegroup S) x \<in> Q" using P_Q by blast
       hence F1:"P \<subseteq> Q \<Longrightarrow> False" using C P_Q(2) Y_def
         unfolding subset.chain_def[of Y C] 
         by blast
       have "Q \<subseteq> P \<Longrightarrow> x \<in> P \<and> m_inv (freegroup S) x \<in> P"
         using P_Q by blast
       hence F2:"Q \<subseteq> P \<Longrightarrow> False" 
          using C P_Q(1) Y_def
         unfolding subset.chain_def[of Y C] 
         by blast
       show False using F1 F2 Or by argo
     qed
     then have "\<Union>C \<in> Y" using C 1 11 unfolding Y_def by force
   } note inter = this
   obtain M where M:"M \<in> Y" "\<forall>X\<in>Y. M \<subseteq> X \<longrightarrow> X = M" "M \<in> Y" 
     using subset_Zorn'[OF inter] by fast
   then have M_sub:"M \<subseteq> A" unfolding Y_def by blast
   then have inv_M_sub:
         "m_inv (freegroup S) `M \<subseteq> m_inv (freegroup S) ` A" by blast
   have a:"M \<inter> m_inv (freegroup S) `M = {}" using M 
     using Y_def by fastforce
   have "union_inv M S = union_inv A S"
     unfolding union_inv_def
   proof(rule ccontr)
     assume asm:"M \<union> m_inv (freegroup S) ` M \<noteq> A \<union> m_inv (freegroup S) ` A"
     have "M \<union> m_inv (freegroup S) ` M \<subseteq> A  \<union> m_inv (freegroup S) ` A"
       using M_sub inv_M_sub  by blast
     then obtain x where x:"x \<in> A  \<union> m_inv (freegroup S) ` A"
           "x \<notin> M \<union> m_inv (freegroup S) ` M " using asm
       by auto
     then have "x \<noteq> \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" using one_notin assms(2) by fastforce
     then have not_eq_inv:"x \<noteq> m_inv (freegroup S) x" using not_eq_inv[of x S] x(1) assms(1) 
       by (smt (verit) Un_iff gen_span.gen_inv image_iff liftgen_span span_liftgen subsetD)
     then show False
     proof (cases "x \<in> A")
       case True
       have x_not_in:"x \<notin> m_inv (freegroup S) ` M" using x(2) by blast
       then have "m_inv (freegroup S) x \<notin> M" using x 
        by (smt (verit, ccfv_threshold) UnE assms freegroup_is_group group.inv_inv imageE imageI in_mono)
       define M1 where "M1 = M \<union> {x}"  
       then have "M1 \<subseteq> A" using x M_sub True by fast
       moreover have "M1 \<inter> (m_inv (freegroup S) ` M1) = {}" using x(2) M(1)
         unfolding Y_def 
         using intersection_lemma[of M "\<lambda>x. (m_inv (freegroup S) x)" x] not_eq_inv
         unfolding M1_def 
         using \<open>inv\<^bsub>F\<^bsub>S\<^esub>\<^esub> x \<notin> M\<close> by fastforce  
       ultimately have "M1 \<in> Y" unfolding Y_def by force
       then have "M1 = M" using M(2) M1_def by fast
       then show False using M1_def x by blast
     next
       case False
       then obtain y where y:"y \<in> A" "x = m_inv (freegroup S) y"
         using x by blast
       then have y_inv:"y = m_inv (freegroup S) x" 
         by (metis assms(1) freegroup_is_group group.inv_inv subsetD)
       define M1 where M1:"M1 = M \<union> {y}"
       then have "M1 \<subseteq> A" using y M_sub  by fast
       then have "y \<notin> M" using y y_inv x  by blast
       moreover have " inv\<^bsub>F\<^bsub>S\<^esub>\<^esub> y \<notin> M" using y y_inv x by blast
       moreover have "y \<notin>  m_inv F\<^bsub>S\<^esub> ` M"  using y y_inv x 
         by (meson M_sub assms(1) calculation(2) freegroup_is_group in_mono inv_in_A subsetI)
       moreover have "y \<noteq> inv\<^bsub>F\<^bsub>S\<^esub>\<^esub> y" using y y_inv not_eq_inv by presburger
       ultimately have "M1 \<inter> (m_inv (freegroup S) ` M1) = {}" using y x(2) M(1)
         unfolding Y_def 
         using intersection_lemma[of M "\<lambda>x. (m_inv (freegroup S) x)" y] y y_inv not_eq_inv
         unfolding M1  by fast
       then have "M1 \<in> Y" unfolding Y_def 
         using \<open>M1 \<subseteq> A\<close> 
         using \<open>M1 \<inter> m_inv F\<^bsub>S\<^esub> ` M1 = {}\<close> by blast
       then have "M1 = M" using M(2) M1 by fast
       then show False using M1 y x by blast   
     qed
   qed
  then show ?thesis using M(1) M_sub exI unfolding Y_def 
    using CollectD by blast
qed


end
