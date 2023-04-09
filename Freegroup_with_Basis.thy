theory Freegroup_with_Basis
imports UniversalProperty  Word_Problem Generators Cancellation
begin    

text \<open>In this file, we provide a formalisation of a 'freegroup with basis', which 
is a group with a subset such that the group is isomorphic to a free group, and the 
isomorphism carrier the subset to the generating set of the free group. 
This distinction about carrying subsets, is useful to provide a neccessary and sufficient
condition for a subgroup of a group to be free. This condition is formalised in 
the lemma fg_with_basis_eq_cond, and is cruicial to the proof of Nielson Schreier.\<close>


definition fg_with_basis
  where
"fg_with_basis (G::('a,'b) monoid_scheme) A 
    \<equiv> (\<exists>(S::(unit \<times> 'a) set) \<phi>. (\<phi> \<in> iso G (freegroup S)) 
              \<and> (\<langle>A\<rangle>\<^bsub>G\<^esub> = carrier G) \<and>(\<phi> ` A = (liftgen S)))"


lemma fg_with_basis_is_free:
  fixes G 
  fixes A
  assumes "(fg_with_basis G A)"
  shows "is_freegroup G" using assms unfolding fg_with_basis_def is_iso_def   
        is_freegroup_def by auto



lemma m_concat_in_span:
  assumes "group G"
  and  "\<forall>x \<in> set l. x \<in> S"
shows "monoid.m_concat G l \<in> \<langle>S\<rangle>\<^bsub>G\<^esub>" using assms
proof(induction l)
  case (Cons a l)
  have "monoid.m_concat G (a#l) = a \<otimes>\<^bsub>G\<^esub> (monoid.m_concat G l)" by auto
  hence "(monoid.m_concat G l) \<in> \<langle>S\<rangle>\<^bsub>G\<^esub>" using Cons by force
  moreover have "a \<in> \<langle>S\<rangle>\<^bsub>G\<^esub>" using Cons(3) 
    by (simp add: gen_span.gen_gens)
  thus ?case 
    by (simp add: calculation gen_span.gen_mult)  
qed (simp)


text\<open>We define a non-empty word w in a monoid G with a subset A to be non_reducible, if it 
if the word w is obtained as a product of elements of A and their inverses,the word is either
of length 1, or any successive elements from A occuring in the word are not inverses of each 
other. \<close>

definition non_reducible::"('a,'b) monoid_scheme \<Rightarrow> 'a set => 'a \<Rightarrow> bool"
  where
"non_reducible G A w \<equiv> (\<exists>l. w = monoid.m_concat G l \<and> (l \<noteq> []) 
                          \<and> (\<forall>x \<in> set l. x \<in> A \<union> m_inv G ` A) 
                          \<and> ((length l = 1) \<or> (\<forall>i \<le> (length l)-2 .
                            l!i \<noteq> inv\<^bsub>G\<^esub> (l!(i+1)))))"

lemma hom_preserves_m_concat:
  assumes "group G" and "group H"
 and  "\<phi> \<in> hom G H"
  and "w = monoid.m_concat G l"
  and "\<forall>x \<in> set l. x \<in> carrier G"
shows "\<phi> w = monoid.m_concat H (map \<phi> l)"
  using assms 
proof(induction l arbitrary: w)
  case Nil
  then show ?case using hom_one by force
next
  case (Cons a l)
  let ?w = "monoid.m_concat G l"
  have x_in:"\<forall> x \<in> set l. x \<in> carrier G" using Cons(6) by simp
  hence w_in:"?w \<in> carrier G" 
    by (simp add: assms(1) group.is_monoid monoid.m_concat_closed subsetI)
  moreover have "a \<in> carrier G" using Cons(6) by simp
  moreover have "w = a \<otimes>\<^bsub>G\<^esub> ?w"  using Cons(5) by simp
  ultimately have "\<phi> w = \<phi> a  \<otimes>\<^bsub>H\<^esub> (\<phi> ?w)" using w_in Cons(4) unfolding hom_def by blast
  moreover have " \<phi> ?w = foldr (\<otimes>\<^bsub>H\<^esub>) (map \<phi> l) \<one>\<^bsub>H\<^esub>" using  Cons(1)[OF Cons(2,3,4)] x_in 
    by blast
  ultimately show ?case by simp
qed

lemma liftgen_subset:"liftgen S \<subseteq> carrier (freegroup S)" 
  by (simp add: freegroup_def liftgen_subset_quotient)

definition liftgen_inv
  where
"liftgen_inv S = m_inv (freegroup S) ` (liftgen S)" 

lemma liftgen_inv_in_carrier:
  "liftgen_inv S \<subseteq> carrier (freegroup S)"
  using liftgen_inv_def 
  by (metis (no_types, lifting) freegroup_is_group group.inv_closed image_subset_iff liftgen_subset subset_iff)


lemma inj_on_invset:
  assumes "group G" "group H"
   and "\<phi> \<in> hom G H"
   and "A \<subseteq> carrier G"
   and "inj_on \<phi> A"
 shows "inj_on \<phi> (m_inv G ` A)"
proof
  fix x
  fix y
  assume x:"x \<in> m_inv G ` A"
  assume y:"y \<in>  m_inv G ` A"
  assume eq:"\<phi> x = \<phi> y"
  obtain x' where x':"x = inv\<^bsub>G\<^esub> x'" "x' \<in> A" using x by blast
  obtain y' where y':"y = inv\<^bsub>G\<^esub> y'" "y' \<in> A"  using y by blast
  from x' have "x \<in> carrier G" using x' assms(1,4) by auto
  moreover have "x' = inv\<^bsub>G\<^esub> x" using x' assms(1,4) by fastforce
  ultimately have map_x':"\<phi> (x') = inv\<^bsub>H\<^esub> \<phi> x" using  group_hom.hom_inv[of "G" "H" \<phi> x] assms(1-3) 
     group_hom.intro group_hom_axioms.intro by blast
  from y' have "y \<in> carrier G" using assms(1,4)  by auto
  moreover have "y' = inv\<^bsub>G\<^esub> y" using y' assms(1,4) by fastforce
  ultimately have map_y':"\<phi> (y') = inv\<^bsub>H\<^esub> \<phi> y" using  group_hom.hom_inv[of "G" "H" \<phi> y] assms(1-3) 
     group_hom.intro group_hom_axioms.intro by blast    
  have "\<phi> x' = \<phi> y'" using map_x' eq assms(2) 
    using map_y' by force
  hence "x' = y'" using x'(2) y'(2) assms(5) unfolding inj_on_def by blast
  thus "x = y" using x' y' by auto
qed

lemma bij_to_invset: 
  assumes "\<phi> \<in> iso G H" "group G" "group H"
      and "A \<subseteq> carrier G"
      and "bij_betw \<phi> A Y"
    shows "bij_betw \<phi> (m_inv G ` A)  (m_inv H ` Y) "
proof-
  have " inj_on \<phi> (m_inv G ` A)" using assms unfolding bij_betw_def     
    by (simp add: inj_on_invset iso_imp_homomorphism)
  moreover have "\<phi> ` (m_inv G ` A) = (m_inv H ` Y)"
  proof
    show "\<phi> ` m_inv G ` A \<subseteq> m_inv H ` Y"
    proof
      fix \<phi>_x
      assume "\<phi>_x \<in> \<phi> ` m_inv G ` A "
      then obtain x where x:"x \<in> A" "\<phi>_x = \<phi>  (m_inv G  x)" by blast
      have "\<phi>_x = m_inv H (\<phi> x)" using assms unfolding iso_def 
        by (metis (no_types, lifting) \<open>\<phi>_x = \<phi> (inv\<^bsub>G\<^esub> x)\<close> \<open>x \<in> A\<close> assms(1) group_hom.hom_inv group_hom.intro group_hom_axioms.intro in_mono iso_imp_homomorphism)
      thus "\<phi>_x \<in> m_inv H ` Y" using assms(5) x(1) unfolding bij_betw_def by blast
    qed
  next
    show " m_inv H ` Y  \<subseteq> \<phi> ` m_inv G ` A"
    proof
      fix \<phi>_y
      assume "\<phi>_y \<in> m_inv H ` Y"
      then obtain y where y:"y \<in> Y" "\<phi>_y = m_inv H y" by blast
      then obtain x where x:"x \<in>  A" "\<phi> x = y" using assms 
        by (meson bij_betw_apply bij_betw_the_inv_into f_the_inv_into_f_bij_betw) 
      then have "\<phi>_y = \<phi> (m_inv G x)" using assms y
        by (metis (no_types, opaque_lifting) group_hom.hom_inv group_hom.intro group_hom_axioms.intro iso_imp_homomorphism subsetD)
      then show "\<phi>_y  \<in> \<phi> ` m_inv G ` A" using x(1) by fast
    qed
  qed
  ultimately show ?thesis  unfolding bij_betw_def by blast
qed

lemma in_map_of_union:
  assumes "\<forall>x \<in> S. x \<in> A \<union> B"
  shows "\<forall>x \<in> f ` S. x \<in> f ` A \<union> f ` B"
  using assms by blast

lemma(in group) exist_of_proj:
  assumes "\<forall>x \<in> set ls. x \<in> (liftgen S) \<union> (liftgen_inv S)"
  shows "\<exists>l. (\<forall> x \<in> set l. x \<in> S \<times> {True, False}) 
              \<and> (ls = map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) l)"
  using assms 
proof(induction ls)
  case (Cons a ls)
  hence "\<forall>x\<in>set ls. x \<in> liftgen S \<union> liftgen_inv S" by simp
  then obtain l where l:"\<forall>x \<in> set l. x \<in> S \<times> {True, False}" "(ls = map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) l)"
    using Cons(1) by auto
  have a_in:"a \<in> liftgen S \<or> a \<in> liftgen_inv S" using Cons(2) by auto
  hence a_in_carrier:"a \<in> carrier (freegroup S)" 
    using liftgen_inv_in_carrier liftgen_subset by blast
  then show ?case
  proof(cases "a \<in> liftgen S")
    case True
    then obtain s where s:"s \<in> S" "a = reln_tuple \<langle>S\<rangle> `` {\<iota> s}" unfolding liftgen_def by blast
    hence "\<forall>x \<in> set ((\<iota> s)@l). x \<in> S \<times> {True, False}" 
      by (simp add: inclusion_def l(1))
    moreover have "(a#ls) =  map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) ((\<iota> s)@l)"
      using s(2) l(2) 
      by (simp add: inclusion_def)
    ultimately show ?thesis by metis
  next
    case False
    hence "a \<in> liftgen_inv S" using a_in by simp
    then obtain b where b:"b \<in> liftgen S" "a = inv \<^bsub>freegroup S\<^esub> b" unfolding liftgen_inv_def 
      by blast
    hence inv_a:"b = inv \<^bsub>freegroup S\<^esub> a" 
      by (metis (no_types, lifting) freegroup_is_group group.inv_inv liftgen_subset subsetD) 
    from b(1) have b_in_fg:"b \<in> carrier (freegroup S)" 
      by (simp add: a_in_carrier freegroup_is_group inv_a)
    then obtain s' where s':"s' \<in> S" "b = reln_tuple \<langle>S\<rangle> `` {\<iota> s'}" using b unfolding liftgen_def
      by blast
    then have "wordinverse (\<iota> s') = [(s', False)]" unfolding inclusion_def by auto
    moreover have "a =  reln_tuple \<langle>S\<rangle> `` {wordinverse (\<iota> s')}" using inv_a
       wordinverse_inv[OF b_in_fg s'(2)]  b(2) by argo
    hence "a =   reln_tuple \<langle>S\<rangle> `` {[(s', False)]}" unfolding wordinverse_def inclusion_def by auto
    hence " a # ls = map (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[x]}) ((s',False)#l)" using l(2) by auto
    moreover have "\<forall> x \<in> set ((s',False)#l). x \<in> S \<times> {True, False}" using l(1) 
      by (simp add: s'(1))
    ultimately show ?thesis by metis
  qed
qed(simp)

lemma(in group) non_reduced_projection:
  assumes "\<forall>x \<in> set ls. x \<in> (liftgen S) \<union> (liftgen_inv S)"  
    and "ls = map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) l"
    and "length ls > 1"
    and   "\<forall>i \<le> (length ls)-2 . ls!i \<noteq> inv\<^bsub>(freegroup S)\<^esub> (ls!(i+1))"
  shows "\<forall>i \<le> (length l)-2 . (l!i) \<noteq> inverse (l!(i+1))"
proof(rule ccontr)
  assume "\<not> (\<forall>i\<le>length l - 2. l ! i \<noteq> FreeGroupMain.inverse (l ! (i + 1)))"
  then obtain i where i:"i \<le> length l - 2" "l ! i = FreeGroupMain.inverse (l ! (i + 1))"
    by blast
   
  then have "[l!i] = wordinverse [l ! (i + 1)]" by auto
  hence word_inv:"wordinverse [l!i] = [l ! (i + 1)]" 
    by (metis wordinverse_of_wordinverse)
  then have l_i_eq:" ls!i = (reln_tuple \<langle>S\<rangle> `` {[l!i]}) " using assms 
    by (metis (mono_tags, lifting) One_nat_def add_lessD1 diff_less i(1) le_add_diff_inverse length_greater_0_conv length_map list.size(3) nat_1_add_1 not_add_less2 nth_map plus_1_eq_Suc zero_less_Suc)
  have len_eq:"length ls = length l" using assms(2) by simp
  hence "ls!i \<in> set ls" using i(1) assms(3) by simp
  hence ls_i:"ls!i \<in> carrier (freegroup S)" using assms(1) i(1) using 
    liftgen_inv_in_carrier[of S] liftgen_subset[of S]
    by (meson Un_iff liftgen_subset subsetD)
  have " inv\<^bsub>freegroup S\<^esub> (ls!i) =  (reln_tuple \<langle>S\<rangle> `` {[l!(i + 1)]})"
    using wordinverse_inv[OF ls_i l_i_eq] word_inv by argo
  moreover have "(reln_tuple \<langle>S\<rangle> `` {[l!(i + 1)]}) = ls!(i+1)" using assms 
    by (smt (z3) Nat.le_diff_conv2 \<open>length ls = length l\<close> add_lessD1 i(1) le_add_diff_inverse nat_add_left_cancel_less nat_less_le neq0_conv nth_map one_less_numeral_iff plus_1_eq_Suc semiring_norm(76) zero_less_diff)
  ultimately have "inv\<^bsub>freegroup S\<^esub>  (ls!i) = ls!(i+1)" by auto
  hence "ls!i = inv\<^bsub>freegroup S\<^esub>  (ls!(i+1))" 
    by (metis freegroup_is_group group.inv_inv ls_i)
  thus False using i(1) len_eq assms(4) by auto
qed

lemma hom_to_subgp:
 assumes "h \<in> hom G H"
 and "h ` (carrier G) = H'"
shows "h \<in> hom G (H\<lparr>carrier := H'\<rparr>)"
  using assms unfolding hom_def by (simp, blast)

lemma non_reducible_imp_red:
  assumes "\<forall>i \<le> (length l)-2 . (l!i) \<noteq> inverse (l!(i+1))"
  shows "reduced l" using assms
proof(induction l)
  case (Cons a l)
  hence 1:"\<forall>i\<le>length l - 2. l ! i \<noteq> FreeGroupMain.inverse (l ! (i + 1)) \<Longrightarrow> reduced l" by auto
  from Cons have 2:"\<forall>i\<le>length (a # l) - 2. (a # l) ! i \<noteq> FreeGroupMain.inverse ((a # l) ! (i + 1))"
    by auto
  hence red:"reduced l" 
    by (smt (z3) length_Cons Cons.IH Nat.le_diff_conv2 Suc_1 add.assoc add.commute add_diff_cancel_left' le_add1 nth_Cons_Suc plus_1_eq_Suc reduced.elims(3))
  then show ?case 
  proof(cases l)
    case (Cons b ls)
    have "a \<noteq> inverse b" using 2 Cons by fastforce
    moreover have "reduced (b#ls)" using Cons red by auto
    ultimately show ?thesis unfolding Cons by simp
  qed(simp)
qed (simp)

lemma non_reducible_imp_non_trivial:
  assumes "\<forall>i \<le> (length l)-2 . (l!i) \<noteq> inverse (l!(i+1))" "l \<noteq> []"
  shows "\<not> (l ~ [])"
  using non_reducible_imp_red[OF assms(1)] assms(2) 
  using reduced.simps(1) reduced_cancel_eq reln_imp_cancels by blast 

lemma m_concat_singleton:
  assumes "x \<in> carrier (freegroup S)"
  shows   "monoid.m_concat (freegroup S) [x] = x"
  using assms 
  by (simp add: freegroup_is_group group.is_monoid)

lemma list_in_span:
  assumes "\<forall>x \<in> set xs. x \<in> S \<times> {True, False}"
  shows "xs \<in> \<langle>S\<rangle>"
  using assms 
proof(induction xs)
  case Nil
  then show ?case 
    by (simp add: freewords_on_def words_on.empty)
next
  case (Cons a xs)
  then show ?case 
    by (metis freewords_on_def invgen_def list.set_intros(1) list.set_intros(2) words_on.gen) 
qed

lemma empty_int_implies_nid:
  assumes "group G"
    "A \<inter> (m_inv G ` A) = {}"
  shows "\<one>\<^bsub>G\<^esub> \<notin> A"
  using assms disjoint_iff group.is_monoid monoid.inv_one rev_image_eqI
  by (metis)

lemma assumes "\<not> (reduced ys)"
  shows "\<not> (reduced (xs@ys))"
  using assms 
  using reduced_leftappend by blast

lemma inverse_in_reduced_lists:
  assumes "reduced l" "length l > 1"
  shows "\<forall>i \<le> length l - 2.  (l!i) \<noteq> inverse (l!(i+1))" 
proof(rule ccontr)
  assume "\<not>(\<forall>i \<le> length l - 2.  (l!i) \<noteq> inverse (l!(i+1)))"
  then obtain i where i:"i \<le> length l - 2" "(l!i) = inverse (l!(i+1))" by blast
  hence "drop (i - 1) l = (l!i)#(l!(i+1))#(drop (i+1) l)"
    using assms 
    by (metis Suc_leI add.right_neutral add_Suc_right add_less_le_mono inv_not_reduced inverse_of_inverse le_add_diff_inverse one_add_one plus_1_eq_Suc zero_less_one)
  hence "\<not> (reduced (drop (i - 1) l))" using i(2) by simp
  hence "\<not> (reduced l)" using i(1) assms 
    by (metis append_take_drop_id reduced_leftappend)
  thus False using assms(1) by auto
qed

lemma inverse_in_reduced_embedlists:
  assumes "reduced l" "length l > 1"
  shows "\<forall>i \<le> length l - 2.  [(l!i)] \<noteq> wordinverse [ (l!(i+1))]" 
  using inverse_in_reduced_lists assms by auto
lemma inv_in_freegp:
  assumes "[x] \<in> \<langle>S\<rangle>"
  shows "inv\<^bsub>freegroup S\<^esub> (reln_tuple \<langle>S\<rangle> `` {[x]}) 
        = reln_tuple \<langle>S\<rangle> `` {wordinverse [x]}" 
  using assms unfolding freegroup_def 
  by (metis freegroup_def freegroup_is_group group.wordinverse_inv partial_object.select_convs(1) quotientI)

lemma red_imp_no_cons_inv:
  assumes "reduced l" "length l > 1" "l \<in> \<langle>S\<rangle>"
  shows "\<forall>i \<le> length l - 2.  reln_tuple \<langle>S\<rangle> `` {[(l!i)]} 
                \<noteq> inv\<^bsub>freegroup S\<^esub> (reln_tuple \<langle>S\<rangle> `` {[(l!(i+1))]})" 
proof(rule ccontr)
  assume "\<not> (\<forall>i \<le> length l - 2.  reln_tuple \<langle>S\<rangle> `` {[(l!i)]} \<noteq> inv\<^bsub>freegroup S\<^esub> (reln_tuple \<langle>S\<rangle> `` {[(l!(i+1))]}))"
  then obtain i where i:"i \<le> length l - 2" 
      "reln_tuple \<langle>S\<rangle> `` {[(l!i)]} = inv\<^bsub>freegroup S\<^esub> (reln_tuple \<langle>S\<rangle> `` {[(l!(i+1))]})" by blast
  hence l_i_in:"[(l!i)] \<in> \<langle>S\<rangle>" using assms 
    by (metis Nat.le_diff_conv2 add.commute add_leD1 cons_span discrete freewords_on_def id_take_nth_drop one_add_one rightappend_span)
  with i have l_Si_in:"[(l!(i+1))] \<in> \<langle>S\<rangle>" using assms 
    by (metis (no_types, lifting) Suc_leI add.right_neutral add_Suc_right add_less_le_mono cons_span freewords_on_def id_take_nth_drop le_add_diff_inverse one_add_one one_less_numeral_iff plus_1_eq_Suc rightappend_span semiring_norm(76))
  hence "inv\<^bsub>freegroup S\<^esub> (reln_tuple \<langle>S\<rangle> `` {[(l!(i+1))]}) 
        = reln_tuple \<langle>S\<rangle> `` {wordinverse [(l!(i+1))]}" using inv_in_freegp by blast
  with i(2) have "reln_tuple \<langle>S\<rangle> `` {[(l!i)]} = reln_tuple \<langle>S\<rangle> ``  {wordinverse [(l!(i+1))]}"
    by argo
  hence "[(l!i)] ~ wordinverse [(l!(i+1))]" using l_i_in l_Si_in  unfolding reln_tuple_def 
    by (meson \<open>reln_tuple \<langle>S\<rangle> `` {[l ! i]} = reln_tuple \<langle>S\<rangle> `` {wordinverse [l ! (i + 1)]}\<close> span_wordinverse word_problem_not_eq)
  hence "(l!i) = inverse (l!(i+1))" 
    by (metis append_Nil assms i(1) inverse_in_reduced_embedlists reduced.simps(2) reduced_cancel_eq reln_imp_cancels wordinverse.simps(1) wordinverse.simps(2))
  moreover have "drop (i - 1) l= (l!i)# inverse (l!(i+1))#(drop (i + 1) l)" 
    using i(1) 
    using assms(1) assms(2) calculation inverse_in_reduced_lists by blast
  hence "\<not> (reduced (drop (i - 1) l))" 
    using assms(1) assms(2) calculation i(1) inverse_in_reduced_lists by blast 
  hence "\<not> (reduced l)" using reduced_leftappend i(1) 
    by (metis append_take_drop_id)
  thus False using assms(1) by auto
qed

lemma in_span_imp_invggen:
  assumes "x \<in> set l"
  "l \<in> \<langle>S\<rangle>"
shows "x \<in> S \<times> {True, False}" using assms
proof(induction l)
  case (Cons a l)
  then show ?case 
  proof(cases "x \<in> set l")
    case True
    hence "l \<in> \<langle>S\<rangle>" using Cons(3) 
      using freewords_on_def span_cons by blast
    then show ?thesis using Cons True by argo
  next
    case False
    hence "[a] \<in> \<langle>S\<rangle>" using cons_span Cons freewords_on_def 
      by blast
    hence "a \<in> S \<times> {True, False}" using freewords_on_def 
      by (metis gen_spanset invgen_def list.sel(1) list.simps(3))
    then show ?thesis using Cons False by simp
  qed
qed( auto)



lemma inv_in_freegrp_word:
  assumes"x \<in> S"
  shows " (reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) = inv \<^bsub>freegroup S\<^esub> (reln_tuple \<langle>S\<rangle> `` {[(x, True)]})"
  using assms inv_in_freegp[of "(x,True)" S] wordinverse_def 
  by (metis append.left_neutral image_subset_iff inclusion_def inclusion_subset_spanset inverse.simps(1) wordinverse.simps(1) wordinverse.simps(2))          

lemma liftgen_inv_eq:
  "liftgen_inv S = (\<lambda> x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]})  ` S"
   unfolding liftgen_inv_def
   liftgen_def inclusion_def using inv_in_freegrp_word by (blast)

lemma inv_liftgen_in_union:
  assumes "x \<in> (liftgen S) \<union> (liftgen_inv S)"
  shows "inv \<^bsub>freegroup S\<^esub> x \<in> (liftgen S) \<union> (liftgen_inv S)"
proof(cases "x \<in>  (liftgen S)")
  case True
  then show ?thesis unfolding liftgen_inv_def by simp 
next
  case False
  hence "x \<in> (liftgen_inv S)" using assms by force
  hence "inv \<^bsub>freegroup S\<^esub> x \<in> (liftgen S)" unfolding liftgen_inv_def 
    by (metis (no_types, lifting) freegroup_is_group group.inv_inv imageE liftgen_subset subset_iff)
  then show ?thesis by blast
qed

text \<open>The following lemma establishes that the group generated by a subset of a group is free, 
if and only if every non reducible word in the span of the subset is not identity. 
This corresponds to the lemma 1.9 of Lyndon and Schupp.\<close>

lemma (in group)fg_with_basis_eq_cond:
  assumes " A \<inter> (m_inv G ` A) = {}" "A \<subseteq> carrier G"
  shows  "(fg_with_basis (G\<lparr>carrier := \<langle>A\<rangle>\<^bsub>G\<^esub>\<rparr>) A) 
            \<longleftrightarrow> (\<forall>w \<in> \<langle>A\<rangle>\<^bsub>G\<^esub>. non_reducible G A w \<longrightarrow> w \<noteq> \<one>\<^bsub>G\<^esub>)"
proof
  assume fg:"fg_with_basis (G\<lparr>carrier := \<langle>A\<rangle>\<^bsub>G\<^esub>\<rparr>) A"
  have "\<one>\<^bsub>G\<^esub> \<notin> A" using assms(1) disjoint_iff group.is_monoid image_eqI monoid.inv_one
    by (metis is_group)
  define G_A where "G_A = (G\<lparr>carrier := \<langle>A\<rangle>\<^bsub>G\<^esub>\<rparr>)"
  hence carrier_eq:"\<langle>A\<rangle>\<^bsub>G_A\<^esub> = carrier (G_A)" using fg 
    by (meson fg_with_basis_def)
  then obtain "\<phi>" "S" where \<phi>_S:"\<phi> \<in> iso G_A (freegroup (S:: (unit \<times> 'a) set))" 
           "\<phi> ` A = (liftgen S)" using fg unfolding fg_with_basis_def G_A_def by auto
  hence bij_to_liftset:"bij_betw \<phi> A (liftgen S)" using \<phi>_S(1) carrier_eq  bij_betw_subset 
    unfolding G_A_def
    by (metis (no_types, lifting) Group.iso_def  gen_span.gen_gens mem_Collect_eq subsetI)  
  have subgp:" \<langle>A\<rangle>\<^bsub>G\<^esub> \<le> G" using assms(2) group.gen_subgroup_is_subgroup[of G A] is_group  
    by blast
  have grp:"group (G_A)" using subgroup.subgroup_is_group[OF subgp is_group] unfolding 
   G_A_def .
  have A_subset:"A \<subseteq> carrier G_A" using is_group unfolding G_A_def 
    by (simp add: gen_span.gen_gens subset_eq)
  have m_inv_eq:"m_inv G ` A = m_inv G_A ` A"  
  proof
    show " m_inv G ` A \<subseteq> m_inv G_A ` A"
    proof 
      fix y
      assume "y \<in> m_inv G ` A"
      then obtain x where "x \<in> A" "y = m_inv G x" by blast
      then have "y \<in> carrier (G_A)" using A_subset is_group
        by (metis G_A_def  group.incl_subgroup group.subgroup_self grp subgp subgroup.m_inv_closed subsetD)
      then show "y \<in> m_inv G_A ` A " using is_group
        by (metis G_A_def \<open>x \<in> A\<close> \<open>y = inv\<^bsub>G\<^esub> x\<close>  gen_span.intros(2) group.m_inv_consistent image_iff subgp)
    qed
  next
    show " m_inv G_A ` A \<subseteq> m_inv G ` A"
    proof
      fix y
      assume "y \<in> m_inv G_A ` A"
      then obtain x where "x \<in> A" "y = m_inv G_A x" by blast
      then have "y \<in> carrier (G)" using A_subset carrier_eq G_A_def is_group
        by (metis G_A_def  gen_span.gen_gens group.inv_closed group.m_inv_consistent subgp subgroup.mem_carrier)
      then show "y \<in> m_inv G ` A " 
        by (simp add: G_A_def \<open>x \<in> A\<close> \<open>y = inv\<^bsub>G_A\<^esub> x\<close> is_group gen_span.gen_gens group.m_inv_consistent subgp)
    qed
  qed
  show "\<forall>w\<in>\<langle>A\<rangle>\<^bsub>G\<^esub>. non_reducible G A w \<longrightarrow> w \<noteq> \<one>\<^bsub>G\<^esub>"
  proof(rule ccontr)
    assume "\<not> (\<forall>w\<in>\<langle>A\<rangle>\<^bsub>G\<^esub>. non_reducible G A w \<longrightarrow> w \<noteq> \<one>\<^bsub>G\<^esub>)"
    then obtain w where w:"w \<in> (\<langle>A\<rangle>\<^bsub>G\<^esub>)" "(non_reducible G A w)" "(w = \<one>\<^bsub>G\<^esub>)" by simp
    have  "\<exists> ls. \<phi> w = monoid.m_concat (freegroup S) ls \<and> ls \<noteq> [] \<and> 
                         (\<forall>x \<in> set ls. x \<in> liftgen S \<union> (liftgen_inv S)) 
               \<and> ((length ls = 1) \<or> (\<forall>i \<le> (length ls)-2 . ls!i \<noteq> inv\<^bsub>(freegroup S)\<^esub> (ls!(i+1))))"
    proof-
      obtain l where l:"w = monoid.m_concat G l" "\<forall>x \<in> set l. x \<in> A \<union> (m_inv G ` A)" "l \<noteq> []"
        "length l = 1 \<or> (\<forall>i \<le> (length l)-2 . l!i \<noteq> inv\<^bsub>G\<^esub> (l!(i+1)))"
        using w(2) unfolding non_reducible_def by blast
      hence "w = monoid.m_concat  G_A l" using carrier_eq G_A_def by simp
      hence  mod_w:"w = foldr (\<otimes>\<^bsub>G_A\<^esub>) l \<one>\<^bsub>G_A\<^esub>" unfolding G_A_def by auto
      have l_set_in:"\<forall> x \<in> set l. x \<in> carrier (G\<lparr>carrier := \<langle>A\<rangle>\<^bsub>G\<^esub>\<rparr>)" 
        using l(2) assms(2) is_group liftgen_inv_in_carrier  carrier_eq 
        unfolding G_A_def using G_A_def
      proof-
         have "A \<subseteq> \<langle>A\<rangle>\<^bsub>G\<lparr>carrier := \<langle>A\<rangle>\<rparr>\<^esub>" 
           using G_A_def A_subset carrier_eq by blast
         moreover have "m_inv G ` A \<subseteq> \<langle>A\<rangle>\<^bsub>G\<lparr>carrier := \<langle>A\<rangle>\<rparr>\<^esub>" 
           by (metis G_A_def carrier_eq gen_span.gen_gens group.subgroup_self grp image_subsetI incl_subgroup subgp subgroupE(3))
         ultimately show ?thesis using l(2) 
           by (metis G_A_def Un_subset_iff carrier_eq in_mono)
       qed
      let ?ls = "map \<phi> l"
      have ls_nonempty:"?ls \<noteq> []" using l(3) by blast
      have hom_phi:"\<phi> \<in> hom G_A (freegroup S)" using \<phi>_S(1) unfolding iso_def by blast
      have "\<phi> w = monoid.m_concat (freegroup S) ?ls" 
        using hom_preserves_m_concat[OF grp freegroup_is_group[of S] hom_phi mod_w] l(2) 
        using G_A_def l_set_in by fastforce
      have loc_eq:"set ?ls = \<phi> ` (set l)" by simp
       have ls_in:"\<forall>x \<in> set ?ls. x \<in> (liftgen S) \<union> (liftgen_inv S)"
       proof-
         have " \<phi> ` A = liftgen S" using bij_to_liftset unfolding bij_betw_def by argo
         moreover have "\<phi> ` m_inv G_A ` A = m_inv F\<^bsub>S\<^esub> ` liftgen S"
           using bij_to_invset[OF \<phi>_S(1) grp freegroup_is_group A_subset bij_to_liftset] 
           unfolding bij_betw_def by argo
         ultimately show ?thesis  unfolding liftgen_inv_def 
         using in_map_of_union[of "set l" "A" "m_inv G_A ` A" "\<phi>"] l(2) m_inv_eq unfolding loc_eq 
         by simp
     qed
      moreover have "(length ?ls = 1) \<or> (\<forall>i \<le> (length ?ls)-2 . ?ls!i \<noteq> inv\<^bsub>(freegroup S)\<^esub> (?ls!(i+1)))"
      proof(cases "length ?ls = 1")
        case False
        have "(\<forall>i \<le> (length ?ls)-2 . ?ls!i \<noteq> inv\<^bsub>(freegroup S)\<^esub> (?ls!(i+1)))"
        proof(rule ccontr)
          assume "\<not> (\<forall>i\<le>length (map \<phi> l) - 2. map \<phi> l ! i \<noteq> inv\<^bsub>(freegroup S)\<^esub> (?ls!(i+1)))"
          then obtain i where i:"i \<le> length ?ls -2" "?ls!i = inv\<^bsub>(freegroup S)\<^esub> (?ls!(i+1))" by blast
          have "i+1 \<le> length ?ls - 1" using i(1) ls_nonempty False 
            by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 Suc_leI diff_diff_add le_neq_implies_less length_greater_0_conv ordered_cancel_comm_monoid_diff_class.le_diff_conv2) 
          hence ls_iSi:"?ls!(i+1) \<in> set ?ls" by auto
          have "?ls!i \<in> set ?ls"  using i(1) nth_mem[of i "?ls"] l(3)
            by (metis (no_types, lifting) diff_less_mono2 diff_zero le_neq_implies_less length_greater_0_conv less_trans list.map_disc_iff nat_1_add_1 plus_1_eq_Suc zero_less_Suc)
          moreover have ls_i:"?ls!i \<in> carrier (freegroup S)" using ls_in  liftgen_subset[of S] 
            using calculation  
            by (meson Un_least liftgen_inv_in_carrier subset_iff) 
          moreover have ls_Si:"?ls!(i+1) \<in> carrier (freegroup S)" using ls_in  liftgen_subset[of S]
            using calculation ls_in ls_iSi 
            using liftgen_inv_in_carrier by blast   
          ultimately have "(?ls!i) \<otimes>\<^bsub>(freegroup S)\<^esub> (?ls!(i+1)) =  \<one>\<^bsub>(freegroup S)\<^esub>"
            using ls_in freegroup_is_group i(2) 
            by (metis group.l_inv)  
          have li:"l ! i \<in> carrier (G_A)" using i ls_i \<phi>_S(1) 
            by (metis G_A_def Suc_1 diff_less l(3) l_set_in le_neq_implies_less length_greater_0_conv length_map less_trans nth_mem zero_less_Suc)
          hence l_i_in:" l ! i \<in> \<langle>A\<rangle>\<^bsub>G\<^esub>" unfolding G_A_def by simp 
          have lSi:"l ! (i+1) \<in> carrier (G_A)" using i(1) ls_Si \<phi>_S(1)
            by (metis G_A_def One_nat_def Suc_pred \<open>i + 1 \<le> length (map \<phi> l) - 1\<close> l_set_in le_imp_less_Suc length_map length_pos_if_in_set ls_iSi nth_mem)        
          then have "\<phi> (l ! i) \<otimes>\<^bsub>(freegroup S)\<^esub> \<phi> (l ! (i+1)) =  \<one>\<^bsub>(freegroup S)\<^esub>"
            using i(1)
            by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 Suc_pred \<open>i + 1 \<le> length (map \<phi> l) - 1\<close> \<open>map \<phi> l ! i \<otimes>\<^bsub>F\<^bsub>S\<^esub>\<^esub> map \<phi> l ! (i + 1) = \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>\<close> dual_order.refl le_imp_less_Suc length_map length_pos_if_in_set less_trans ls_iSi nth_map)
          then have "\<phi> (l ! i \<otimes>\<^bsub>G_A\<^esub> (l ! (i + 1))) = \<one>\<^bsub>(freegroup S)\<^esub>" using \<phi>_S(1)
            unfolding iso_def using hom_mult[of \<phi> G_A "F\<^bsub>S\<^esub>"] li lSi by blast
          then have "l ! i \<otimes>\<^bsub>G_A\<^esub> (l ! (i + 1)) =  \<one>\<^bsub>G_A\<^esub>"  using \<phi>_S(1) 
            by (smt (verit) freegroup_is_group group.is_monoid group.iso_iff_group_isomorphisms group_isomorphisms_def grp hom_one lSi li monoid.m_closed)
          then have l_i_inv:"l ! i = inv\<^bsub>G_A\<^esub> (l ! (i + 1))" 
            by (metis group.inv_equality grp lSi li)
          hence l_i_inv_G:"l ! i = inv\<^bsub>G\<^esub> (l ! (i + 1))" unfolding G_A_def
            using Group.group.m_inv_consistent[OF is_group subgp l_i_in] 
            by (metis G_A_def is_group group.inv_inv grp lSi l_i_in subgp subgroup.mem_carrier) 
          moreover have "length l = length (map \<phi> l)" by simp
          hence "i \<le> length l - 2" 
            using i(1) by presburger
          ultimately have "\<exists> i \<le> length l - 2. l ! i  = inv\<^bsub>G_A\<^esub> l ! (i + 1)" using l_i_inv
            by blast
          then show False using l(4) l_i_inv_G 
          using \<open>i \<le> length l - 2\<close> 
          by (metis False \<open>length l = length (map \<phi> l)\<close>)
      qed
      then show ?thesis by blast
    qed (blast)     
    then show ?thesis 
      using \<open>\<phi> w = foldr (\<otimes>\<^bsub>F\<^bsub>S\<^esub>\<^esub>) (map \<phi> l) \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>\<close> ls_in ls_nonempty by blast
  qed
  then obtain ls where ls:"\<phi> w = monoid.m_concat (freegroup S) ls" "ls \<noteq> []" 
                         "\<forall>x \<in> set ls. x \<in> liftgen S \<union> (liftgen_inv S)"
        "length ls = 1 \<or> (\<forall>i \<le> (length ls)-2 . ls!i \<noteq> inv\<^bsub>(freegroup S)\<^esub> (ls!(i+1)))" 
    by auto   
  define w' where "w' = \<phi> w"
  hence w':"\<phi> w = w'" by auto
  then have "\<phi> w \<noteq> \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" 
  proof(cases "length ls = 1")
    case True
    then obtain x  where x:"x \<in> liftgen S \<or> x \<in> liftgen_inv S" "ls = [x]" using ls(3)
      by (metis One_nat_def Un_iff length_0_conv length_Suc_conv list.set_intros(1))
    then have \<phi>_w_is:"\<phi> w = x" using ls(1) m_concat_singleton 
      using liftgen_inv_in_carrier liftgen_subset by blast
    then show ?thesis
    proof(cases "x \<in> liftgen S")
      case True
      then obtain s where s:"x = reln_tuple \<langle>S\<rangle> `` {\<iota> s}" "s \<in> S"  unfolding liftgen_def by blast
      then have i_s:"\<iota> s = [(s, True)]" unfolding inclusion_def by auto
      then have s_in: "\<iota> s \<in> \<langle>S\<rangle>" 
        by (meson image_subset_iff inclusion_subset_spanset s(2))
      moreover have "reduced [(s, True)]" by simp
      hence "\<not>([(s, True)] ~ [])" 
        using reduced.simps(1) reduced_cancel_eq reln_imp_cancels by blast
      hence "x \<noteq> \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" using  word_problem_not_eq_id[OF s_in] i_s unfolding s(1) by simp
      then show ?thesis  unfolding \<phi>_w_is .
    next
      case False
      then obtain y where y:"y \<in> liftgen S" "y = inv\<^bsub>freegroup S\<^esub> x" using x(1) 
        by (metis (no_types, lifting) freegroup_is_group group.inv_inv imageE liftgen_inv_def liftgen_subset subsetD)
        then obtain s where s:"y = reln_tuple \<langle>S\<rangle> `` {\<iota> s}" "s \<in> S"  unfolding liftgen_def by blast
      then have i_s:"\<iota> s = [(s, True)]" unfolding inclusion_def by auto
      then have s_in: "\<iota> s \<in> \<langle>S\<rangle>" 
        by (meson image_subset_iff inclusion_subset_spanset s(2))
      moreover have "reduced [(s, True)]" by simp
      hence "\<not>([(s, True)] ~ [])" 
        using reduced.simps(1) reduced_cancel_eq reln_imp_cancels by blast
      hence "y \<noteq> \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" using  word_problem_not_eq_id[OF s_in] i_s unfolding s(1) by simp
      hence "x \<noteq> \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" using y(2) 
        by (metis (no_types, lifting) freegroup_is_group gen_span.gen_one group.inv_eq_1_iff group.span_liftgen subset_eq)
      then show ?thesis unfolding \<phi>_w_is . 
    qed
  next
    case False
    hence "\<forall>i \<le> (length ls)-2 . ls!i \<noteq> inv\<^bsub>(freegroup S)\<^esub> (ls!(i+1))" using ls(4) by auto
    then obtain l where l:"(\<forall> x \<in> set l. x \<in> S \<times> {True, False})"
    "(ls = map (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[x]})) l)" using False ls(2) exist_of_proj[OF ls(3)] by auto
    from     non_reduced_projection[OF ls(3) l(2) ] ls(2,4) False
    have inv_cond:"\<forall>i\<le>length l - 2. l ! i \<noteq> FreeGroupMain.inverse (l ! (i + 1))" 
      by (meson le_neq_implies_less length_0_conv less_one not_less)
    have l_in:"l \<in> \<langle>S\<rangle>" using list_in_span[OF l(1)] .
    hence "\<not> (l ~ [])" using non_reducible_imp_non_trivial[OF inv_cond] l(2) ls(2) by blast
    hence "reln_tuple \<langle>S\<rangle> `` {l} \<noteq> \<one>\<^bsub>F\<^bsub>S\<^esub>\<^esub>" using word_problem_not_eq_id[OF l_in] 
      by argo
    moreover have "reln_tuple \<langle>S\<rangle> `` {l} = \<phi> w " using reln_tuple_eq[OF l_in] unfolding ls(1) l(2) .
    ultimately show ?thesis by argo
  qed
  then have "w \<noteq> \<one>\<^bsub>G_A\<^esub>" using \<phi>_S(1) unfolding iso_def 
    by (meson \<phi>_S(1) freegroup_is_group grp hom_one iso_imp_homomorphism)
  then have "w \<noteq> \<one>\<^bsub>G\<^esub>" using subgp unfolding G_A_def by simp
  then show False using w(3) by argo
qed
next
  assume case_asm:"\<forall>w\<in>\<langle>A\<rangle>\<^bsub>G\<^esub>. non_reducible G A w \<longrightarrow> w \<noteq> \<one>\<^bsub>G\<^esub>"
  define S where "S = {()} \<times> A"
  define G_A where "G_A = (G\<lparr>carrier := \<langle>A\<rangle>\<^bsub>G\<^esub>\<rparr>)"
  hence carrier_eq:"carrier (G_A) = \<langle>A\<rangle>\<^bsub>G\<^esub>" by auto
  then have "(\<lambda>(x,y). y) \<in> S \<rightarrow> carrier G" using assms S_def by force
  then obtain h  where h:"h \<in> hom (freegroup S) G"
    "\<forall>x\<in>S. (\<lambda>(a,b). b)  x = h (reln_tuple \<langle>S\<rangle> `` {\<iota> x})"
    using exists_hom  by blast
  hence group_hom_G:"group_hom (freegroup S) G h" 
    by (simp add: h(1) freegroup_is_group group_hom.intro group_hom_axioms_def)
  have subgp:" \<langle>A\<rangle>\<^bsub>G\<^esub> \<le> G" using assms(2) group.gen_subgroup_is_subgroup[of G A] is_group  
    by blast
  have grp:"group (G_A)" using subgroup.subgroup_is_group[OF subgp is_group] unfolding 
   G_A_def .
  have A_subset:"A \<subseteq> carrier G_A" unfolding G_A_def using is_group 
    using subgp subgroup.subgroup_is_group 
    by (simp add: gen_span.gen_gens subsetI)
  have "h ` (liftgen S) = A" using S_def h(2) unfolding liftgen_def by auto
  hence h_to:"h ` (carrier (freegroup S)) =  \<langle>A\<rangle>\<^bsub>G\<^esub>" using h(1) group_hom.hom_span[OF group_hom_G] 
    by (metis liftgen_span liftgen_subset span_liftgen subset_antisym)  
  hence h_in:"h \<in> hom (freegroup S) G_A" using carrier_eq hom_to_subgp[OF h(1)] 
    unfolding G_A_def by presburger
  hence group_hom_G_A:"group_hom (freegroup S) G_A h" 
    using  group_hom.intro[OF freegroup_is_group grp] group_hom_axioms_def by blast
  then have surj:"h ` (carrier (freegroup S)) = carrier (G_A)" using h_to unfolding G_A_def by simp 
  have h_S_inv:"\<forall>x\<in>S. inv\<^bsub>G\<^esub> ((\<lambda>(a,b). b)  x) = h (reln_tuple \<langle>S\<rangle> `` {[(x, False)]})"
  proof
    fix x
    assume x:"x \<in> S"
    hence in_carr:"(reln_tuple \<langle>S\<rangle> `` {\<iota> x}) \<in> carrier (freegroup S)" unfolding freegroup_def 
      by (metis image_subset_iff inclusion_subset_spanset partial_object.select_convs(1) proj_def proj_preserves)
    hence " (reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) = inv \<^bsub>freegroup S \<^esub> (reln_tuple \<langle>S\<rangle> `` {\<iota> x})"
      using inv_in_freegrp_word[OF x] unfolding inclusion_def by argo
    moreover have "h (inv \<^bsub>freegroup S \<^esub> (reln_tuple \<langle>S\<rangle> `` {\<iota> x})) = inv\<^bsub>G\<^esub> ((\<lambda>(a,b). b)  x)"
      using x Group.group_hom.hom_inv[OF group_hom_G in_carr] h(2) by auto
    ultimately show "inv\<^bsub>G\<^esub> ((\<lambda>(a,b). b)  x) = h (reln_tuple \<langle>S\<rangle> `` {[(x, False)]})" by argo
  qed
  hence h_to:"\<forall>x \<in> S \<times> {True, False}. h (reln_tuple \<langle>S\<rangle> `` {[x]}) \<in> A \<union> (m_inv G ` A)"
    using h(2) unfolding S_def inclusion_def by simp
  have bij_liftgen_A:"bij_betw h (liftgen S) A" 
  proof(rule bij_betwI)
    show "h \<in> liftgen S \<rightarrow> A" using h 
      using \<open>h ` liftgen S = A\<close> by blast
  next  
    define g where "g = (\<lambda> x. (reln_tuple \<langle>S\<rangle> `` {\<iota> ((),x)}))"
    hence "g ` A \<subseteq> liftgen S" unfolding S_def liftgen_def by blast
    thus "g \<in> A \<rightarrow> liftgen S" by auto
  next
    fix x
    assume "x \<in> liftgen S"
    then obtain y where y:"y \<in> S" "x = reln_tuple \<langle>S\<rangle> `` {\<iota> y}" unfolding liftgen_def 
      by blast
    hence "h x = snd y" using h(2) 
      by (simp add: snd_def)
    thus "reln_tuple \<langle>S\<rangle> `` {\<iota> ((), h x)} = x" using y unfolding S_def by auto
  next
    fix y
    assume "y \<in> A"
    hence "((),y) \<in> S" unfolding S_def by auto
    thus "h (reln_tuple \<langle>S\<rangle> `` {\<iota> ((), y)}) = y" using h(1) unfolding S_def 
      using S_def h(2) by auto
  qed
  have bij_liftgen_inv_A:"bij_betw h (liftgen_inv S)  (m_inv G ` A)" unfolding liftgen_inv_eq
  proof(rule bij_betwI)
    show "h \<in> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S \<rightarrow> m_inv G ` A"
      using h h_S_inv unfolding S_def by force
  next
    define g where "g \<equiv> \<lambda> x. (reln_tuple \<langle>S\<rangle> `` {[(((),(inv\<^bsub>G\<^esub> x)), False)]})"
    have "\<forall>y \<in> m_inv G ` A. inv\<^bsub>G\<^esub>  y \<in> A" 
      using assms(2) by auto
    have "g ` (m_inv G) ` A \<subseteq>(\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S" 
    proof
      fix y
      assume y:"y \<in> g ` (m_inv G) ` A "
      then obtain x where x:"x \<in> A" "y = g (inv\<^bsub>G\<^esub> x)" by blast
      hence "g (inv\<^bsub>G\<^esub> x) =  reln_tuple \<langle>S\<rangle> `` {[(((),x), False)]}" 
        using assms(2) g_def by auto
      moreover have "((),x) \<in> S" using x(1) unfolding S_def by blast
      ultimately show "y \<in>(\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S" 
        using x(2) by blast 
    qed
    thus "g \<in> m_inv G ` A \<rightarrow> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S" by fast
  next
    fix x
    assume "x \<in> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S"
    then obtain y where y:"((),y) \<in> S" "reln_tuple \<langle>S\<rangle> `` {[(((),y), False)]} = x" 
      using S_def  by blast
    hence "h x = inv y" using h_S_inv by force
    hence "y = inv (h x)" 
      by (metis S_def assms(2) inv_inv mem_Sigma_iff subsetD y(1))
    thus "reln_tuple \<langle>S\<rangle> `` {[(((), inv h x), False)]} = x" using y(2) by argo
  next
    fix y
    assume "y \<in> m_inv G ` A "
    then obtain x where x:"x \<in> A" "y = inv x" by blast
    hence y_inv:"x = inv y" 
      by (metis assms(2) inv_inv subsetD)
    hence "((),x) \<in> S" using x(1) S_def by force
    thus "h (reln_tuple \<langle>S\<rangle> `` {[(((), inv y), False)]}) = y" using h_S_inv y_inv 
      using x(2) by fastforce
  qed
  have bij_h:"bij_betw h ((liftgen S) \<union> (liftgen_inv S)) (A \<union> (m_inv G ` A))"
    using  bij_betw_combine[OF bij_liftgen_A  bij_liftgen_inv_A assms(1)] . 
  moreover have "\<forall>w \<in> carrier (freegroup S). w \<noteq> \<one>\<^bsub>freegroup S\<^esub> \<longrightarrow>  h w \<noteq> \<one>\<^bsub>G_A\<^esub>"
  proof-
    {fix w
    assume in_fgp:"w \<in> carrier (freegroup S)"
    assume neq_one:"w \<noteq>  \<one>\<^bsub>freegroup S\<^esub>"
    obtain ls where ls:"w = reln_tuple  \<langle>S\<rangle> `` {ls}" "ls \<in> \<langle>S\<rangle>" using in_fgp unfolding freegroup_def 
      by (simp, meson quotientE)
    define l where "l = (reduce^^(length ls)) ls"
    have l_rel_ls:"l ~ ls" 
      using cancels_imp_rel iter_cancels_to l_def reln.sym by blast
    moreover have l_not_rel:"\<not> (l ~ [])" using neq_one ls word_problem_notrel[OF ls(2) ] ls(1) unfolding l_def
      by fastforce
    moreover have red_l:"reduced l" 
      by (simp add: l_def reduced_iter_length)   
    hence "reduce l = l" 
      by (simp add: reduced_reduce)
    hence iter_l:"(reduce^^(length l)) l = l" 
      using cancels_imp_iter l_def l_rel_ls reln_imp_cancels by blast
    moreover have l_in_S:"l \<in> \<langle>S\<rangle>" using ls(2) l_def 
      using cancels_to_preserves iter_cancels_to by blast
    moreover have w_is_l:"w = reln_tuple  \<langle>S\<rangle> `` {l}" using ls l_in_S iter_l l_def 
      using word_problem_eq by blast  
    hence w_decompose:"w = monoid.m_concat (freegroup S) (map (\<lambda>x.(reln_tuple \<langle>S\<rangle> `` {[x]})) l)"
      by (simp add: l_in_S reln_tuple_eq)
    have "h w \<noteq> \<one>\<^bsub>G_A\<^esub>"
    proof(cases "length l = 1")
      case True                                                                          
      then obtain s where s:"l = [s]" "s \<in> S \<times> {True, False}"
        using l_in_S unfolding freewords_on_def invgen_def words_on_def 
        by (metis (no_types, lifting) length_Cons add_cancel_right_left le_zero_eq length_0_conv mem_Collect_eq not_one_le_zero words_onp.cases)
      then obtain x where x:"x \<in> A" "fst s = ((), x)" unfolding S_def by auto    
      then show ?thesis
      proof(cases "snd s")
        case True
        hence l_is_fst_s:"l = \<iota> (fst s)" unfolding inclusion_def using s by force
        hence  "w = (reln_tuple \<langle>S\<rangle> `` {l})" using w_decompose 
          using w_is_l by blast  
        hence "h w = x" using l_is_fst_s x s h(2) 
          by fastforce 
        moreover have "x \<noteq> \<one>\<^bsub>G\<^esub>" using empty_int_implies_nid[OF is_group assms(1)] x(1) by blast
        ultimately show ?thesis unfolding G_A_def by simp 
      next
        case False
        hence l_is_fst_s:"l = wordinverse (\<iota> (fst s))" unfolding inclusion_def using s by force
        hence  w_is:"w = (reln_tuple \<langle>S\<rangle> `` {l})" using w_decompose 
          using w_is_l by blast 
        define w' where "w' = (reln_tuple \<langle>S\<rangle> `` {\<iota> (fst s)})"
        hence w_inv_w':"w = inv \<^bsub>freegroup S\<^esub> w'" using w_is wordinverse_inv unfolding l_is_fst_s 
          by (metis freegroup_is_group group.inv_inv in_fgp wordinverse_of_wordinverse)  
        hence "w' =  inv \<^bsub>freegroup S\<^esub> w" 
          by (metis in_fgp l_is_fst_s w'_def w_is wordinverse_inv wordinverse_of_wordinverse)
        hence "w' \<in> carrier (freegroup S)" 
          by (meson group.inv_closed group_hom.axioms(1) group_hom_G_A in_fgp)
        hence h_eq:"h w = inv\<^bsub>G\<^esub> (h w')" using h(1) in_fgp unfolding w_inv_w' 
          by (meson group_hom.hom_inv group_hom_G)
        hence "h w' = x" unfolding w'_def using l_is_fst_s x s h(2) 
          by fastforce 
        moreover have "x \<noteq> \<one>\<^bsub>G\<^esub>" using empty_int_implies_nid[OF is_group assms(1)] x(1) by blast
        ultimately have "h w \<noteq> \<one>\<^bsub>G\<^esub>" using h_eq 
          by (metis \<open>w' = inv\<^bsub>F\<^bsub>S\<^esub>\<^esub> w\<close> group_hom.hom_inv group_hom_G in_fgp inv_one)
        thus ?thesis unfolding G_A_def by simp 
      qed
    next
      case False
      hence "length l> 1" using l_not_rel
        using nat_neq_iff by fastforce
      define ls0 where "ls0 = map (\<lambda>x. (reln_tuple \<langle>S\<rangle> `` {[x]})) l"
      have "w = monoid.m_concat (freegroup S) ls0" using w_decompose ls0_def by auto
      moreover have ls0i:"\<forall>i \<le> length ls0 - 2. (ls0!i) \<noteq> inv\<^bsub>freegroup S\<^esub> (ls0!(i+1))"
        using red_imp_no_cons_inv[OF red_l] False l_in_S unfolding ls0_def 
        by (smt (verit, del_insts) One_nat_def \<open>1 < length l\<close> add.commute add_lessD1 diff_is_0_eq' le_add_diff_inverse2 le_neq_implies_less length_map nat_1_add_1 nat_add_left_cancel_less nat_le_linear not_add_less2 nth_map plus_1_eq_Suc zero_less_Suc)
      have helper:"(\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[x]}) ` (S \<times> {True, False})
                    =  (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, True)]}) ` S  \<union>  (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S"

        proof(rule equalityI, rule subsetI)
          fix x
          assume "x \<in>  (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[x]}) ` (S \<times> {True, False})"
          then obtain y where y:"y \<in> S \<times> {True, False}" "x = reln_tuple \<langle>S\<rangle> `` {[y]}" by force
          hence "x = reln_tuple \<langle>S\<rangle> `` {[(fst y, True)]} \<or>  x = reln_tuple \<langle>S\<rangle> `` {[(fst y, False)]}"
            apply(cases "snd y") apply force by force
          thus "x \<in> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, True)]}) ` S  \<union>  (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S"
            using y(1) by force
        next
          show " (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, True)]}) ` S \<union> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S
                  \<subseteq> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[x]}) ` (S \<times> {True, False}) "
          proof(rule subsetI)
            fix x 
            assume x:"x \<in> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, True)]}) ` S \<union> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S"
            then obtain y where y:"y \<in> S" "x = reln_tuple \<langle>S\<rangle> `` {[(y, True)]} \<or>  x = reln_tuple \<langle>S\<rangle> `` {[(y, False)]}"
              by blast
            show "x \<in>(\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[x]}) ` (S \<times> {True, False})"
            proof(cases "x  = reln_tuple \<langle>S\<rangle> `` {[(y, True)]}")
              case True
              hence "x = (\<lambda> x. reln_tuple \<langle>S\<rangle> `` {[x]}) (y,True)" using y by argo
              thus ?thesis using y(1) by auto
            next
              case False
              hence "x = (\<lambda> x. reln_tuple \<langle>S\<rangle> `` {[x]}) (y,False)" using y(2) by argo
              then show ?thesis using y(1) by auto
            qed
          qed
        qed
        have in_ls00:"\<forall>i \<le> length ls0 - 1. (ls0!i) \<in> (liftgen S) \<union> (liftgen_inv S)"
        proof-
          {fix j
          assume loc_j:"j \<le> length ls0 - 1"
          hence 1:"ls0!j = reln_tuple \<langle>S\<rangle> `` {[l!j]}" using ls0_def 
            using \<open>1 < length l\<close> by auto
          moreover have l_j:"l!j \<in> S \<times> {True, False}" using l_in_S in_span_imp_invggen[of "ls!j" l S]
            using loc_j 
            by (metis (mono_tags, lifting) One_nat_def Suc_pred \<open>1 < length l\<close> in_span_imp_invggen le_imp_less_Suc length_0_conv length_greater_0_conv length_map ls0_def not_add_less2 nth_mem plus_1_eq_Suc)
          ultimately have "reln_tuple \<langle>S\<rangle> `` {[l!j]} \<in> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[x]}) ` (S \<times> {True, False})"
            using loc_j by simp 
          have " (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[x]}) ` (S \<times> {True, False}) 
                    =  (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, True)]}) ` S  \<union>  (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[(x, False)]}) ` S"
            using helper by auto
          moreover have "ls0!j \<in> (\<lambda>x. reln_tuple \<langle>S\<rangle> `` {[x]}) ` (S \<times> {True, False})"
            using 1 l_j by force
          ultimately have "ls0 ! j \<in> liftgen S \<union> liftgen_inv S" 
                unfolding liftgen_inv_eq liftgen_def inclusion_def  
                by auto
            }
           thus ?thesis by auto
         qed
      have len_ls0:"length ls0 > 1" using False ls0_def 
        using \<open>1 < length l\<close> by force
      hence in_set_ls0:"\<forall>l \<in> set ls0. l \<in> (liftgen S) \<union> (liftgen_inv S)" using False ls0_def in_ls00 
        by (smt (verit) One_nat_def Suc_pred diff_commute diff_diff_cancel diff_is_0_eq'
 in_set_conv_nth less_imp_le_nat nat_le_linear zero_less_diff) 
      have non_cancel_in_ls0:"\<forall>i \<le> length ls0 - 2. (h (ls0!i)) \<noteq> inv\<^bsub>G\<^esub> (h (ls0!(i+1)))"
      proof-
        {fix i
        assume i_len:"i \<le> length ls0 - 2"
        hence "i \<le> length l - 2" using ls0_def by simp
        hence l_i_in_Sinvgen:"l!i \<in>  S\<^sup>\<plusminus>" using l_in_S in_span_imp_invggen[of "ls!i" l S] 
          by (metis diff_less in_span_imp_invggen invgen_def l_not_rel le_neq_implies_less length_greater_0_conv less_trans nat_1_add_1 nth_mem plus_1_eq_Suc reln.refl zero_less_Suc)
        hence  l_Si_in_Sinvgen:"l!(i+1) \<in>  S\<^sup>\<plusminus>" using l_in_S in_span_imp_invggen[of "ls!(i+1)" l S] 
          by (metis One_nat_def Suc_pred \<open>1 < length l\<close> \<open>i \<le> length l - 2\<close> diff_diff_left in_span_imp_invggen invgen_def le_imp_less_Suc less_diff_conv nat_1_add_1 nth_mem zero_less_diff)
        hence "h (ls0!i) \<in> A \<union> (m_inv G ` A)" unfolding ls0_def using h_to l_i_in_Sinvgen unfolding invgen_def
          by (metis (no_types, lifting) One_nat_def \<open>1 < length l\<close> \<open>i \<le> length l - 2\<close> diff_less le_neq_implies_less less_trans nat_1_add_1 nth_map plus_1_eq_Suc zero_less_Suc)
        hence a:"(ls0!i) \<in> (liftgen S) \<union> (liftgen_inv S)" using i_len in_ls00 by auto
        have b:"(ls0!(i+1)) \<in> (liftgen S) \<union> (liftgen_inv S)" using in_ls00 i_len 
          using One_nat_def Suc_pred \<open>1 < length l\<close> add.commute add_le_cancel_left 
                diff_diff_add length_map ls0_def one_add_one plus_1_eq_Suc zero_less_diff 
          by (smt (z3))
        have "(h (ls0!i)) \<noteq> inv\<^bsub>G\<^esub> (h (ls0!(i+1)))"
        proof(rule ccontr)
          assume " \<not> h (ls0 ! i) \<noteq> inv h (ls0 ! (i + 1))"
          hence 1:"h (ls0 ! i) = inv h (ls0 ! (i + 1))" by simp 
          have "h (inv\<^bsub>freegroup S\<^esub> (ls0 ! (i + 1))) = inv h (ls0 ! (i + 1))"
            using b Group.group_hom.hom_inv[OF group_hom_G] 
            using liftgen_inv_in_carrier liftgen_subset by blast  
          hence "h (ls0!i) = h (inv\<^bsub>freegroup S\<^esub> (ls0 ! (i + 1)))" 
            using 1 by auto
          hence "ls0!i = inv\<^bsub>freegroup S\<^esub> (ls0 ! (i + 1))" using bij_h a inv_liftgen_in_union[OF b] 
            unfolding bij_betw_def inj_on_def 
            by meson
          thus False using ls0i i_len by simp
        qed
      }
      then show ?thesis by blast
    qed 
    hence w_is:"w = monoid.m_concat (freegroup S) ls0" using w_decompose ls0_def by argo
    hence "h w = monoid.m_concat G (map h ls0)" 
      using h(1) hom_preserves_m_concat[OF freegroup_is_group[of S] is_group h(1) w_is] 
       in_set_ls0 
      by (meson Un_iff liftgen_inv_in_carrier liftgen_subset subset_iff)
    moreover have "\<forall>x \<in> set (map h ls0). x \<in> A \<union> m_inv G ` A"
      using bij_h in_ls00 in_set_ls0 
      using bij_betw_imp_surj_on by fastforce
    moreover have "\<forall>i \<le> (length (map h ls0))-2 . (map h ls0)!i \<noteq> inv\<^bsub>G\<^esub> ((map h ls0)!(i+1))"
      using non_cancel_in_ls0 
      by (smt (verit) Nat.le_diff_conv2 add.commute add_2_eq_Suc' add_leD2 diff_is_0_eq' le_neq_implies_less le_numeral_extra(4) len_ls0 length_map less_numeral_extra(4) less_one less_trans nat_le_linear nth_map plus_1_eq_Suc)
    ultimately have "non_reducible G A (h w)" unfolding non_reducible_def using False len_ls0 
      by (smt (verit, ccfv_threshold) add_lessD1 le0 le_Suc_ex len_ls0 length_greater_0_conv map_is_Nil_conv)
    hence "h w \<noteq> \<one>\<^bsub>G\<^esub>" using case_asm by auto
    then show ?thesis unfolding G_A_def by simp
  qed}
  thus ?thesis by auto
  qed 
  hence h_iso:"h \<in> iso (freegroup S) G_A" using group_hom.group_hom_isoI[OF group_hom_G_A] surj 
    by blast
  then obtain g where g:"group_isomorphisms G_A (freegroup S) g h" 
    using group.iso_iff_group_isomorphisms[OF freegroup_is_group[of S]] h_iso 
    using group_isomorphisms_sym by blast
  hence g_iso:"g \<in> iso G_A (freegroup S)" 
    using group_isomorphisms_imp_iso by blast
  have g_map:"g  ` A = (liftgen S)" 
   proof
    {fix y
      assume "y \<in> g ` A"
      hence "y \<in> g ` (h ` (liftgen S))" using bij_liftgen_A unfolding bij_betw_def by meson
      
      then obtain s where x:"y = g (h s)" "s \<in> liftgen S" by blast
      moreover then have "g (h s) = s" using liftgen_subset[of S] g 
        unfolding group_isomorphisms_def by fast
      ultimately have "y \<in> liftgen S" by argo}
    thus "g ` A \<subseteq> liftgen S" by blast
  next
    {fix y
      assume y:"y \<in> liftgen S"
      hence "h y \<in> A" using bij_liftgen_A unfolding bij_betw_def by blast
      moreover then have "g (h y) = y" using g assms(2) unfolding group_isomorphisms_def G_A_def 
        by (meson liftgen_subset subsetD y)
      ultimately have "y \<in> g ` A" using y by blast}
    thus "liftgen S \<subseteq> g ` A" by auto
  qed
  have "\<langle>A\<rangle>\<^bsub>G\<lparr>carrier := \<langle>A\<rangle>\<rparr>\<^esub> = carrier (G\<lparr>carrier := \<langle>A\<rangle>\<rparr>)" 
  proof-
    have "\<langle>A\<rangle>\<^bsub>G\<lparr>carrier := \<langle>A\<rangle>\<rparr>\<^esub> = \<langle>A\<rangle>" 
    proof
      show  "\<langle>A\<rangle>\<^bsub>G\<lparr>carrier := \<langle>A\<rangle>\<rparr>\<^esub> \<subseteq> \<langle>A\<rangle>" 
        using G_A_def A_subset carrier_eq group.gen_span_closed grp by blast
    next
      show  "\<langle>A\<rangle> \<subseteq> \<langle>A\<rangle>\<^bsub>G\<lparr>carrier := \<langle>A\<rangle>\<rparr>\<^esub>" 
      proof
        fix x
        assume "x \<in> \<langle>A\<rangle>"
        thus "x \<in> \<langle>A\<rangle>\<^bsub>G\<lparr>carrier := \<langle>A\<rangle>\<rparr>\<^esub>"
        proof(induction x rule:gen_span.induct)
          case gen_one
          then show ?case using assms(2) is_group 
            by (metis G_A_def carrier_eq gen_span.gen_one group.gen_subgroup_is_subgroup group.l_cancel_one' grp subgroup.mem_carrier subgroup_mult_equality) 
        next
          case (gen_gens x)
          then show ?case 
            by (simp add: gen_span.gen_gens)  
        next
          case (gen_inv x)
          then show ?case 
            by (metis gen_span.gen_inv m_inv_consistent subgp)
        next
          case (gen_mult x y)
          then show ?case 
            by (metis gen_span.gen_mult subgp subgroup_mult_equality)
        qed 
      qed
    qed
    thus ?thesis using carrier_eq unfolding G_A_def by argo
  qed
  thus "fg_with_basis (G\<lparr>carrier := \<langle>A\<rangle>\<^bsub>G\<^esub>\<rparr>) A"  unfolding fg_with_basis_def
    using g_iso carrier_eq g_map unfolding G_A_def by blast
qed


end