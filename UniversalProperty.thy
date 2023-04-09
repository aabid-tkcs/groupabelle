theory UniversalProperty
  imports "Generators" "FreeGroupMain" "Cancellation" "Word_Problem"
begin

definition (in group) genmap
  where "genmap S f g = (if g \<in> S then f g else inv (f (wordinverse g)))"

definition freeg :: "_  \<Rightarrow> bool"
  where "freeg G  = ((group G) 
 \<and> (\<exists>A \<subseteq> carrier G . \<forall>group H .
 (\<forall>f \<in> A \<rightarrow> carrier H . (\<exists>g \<in> hom G H . (\<forall>x \<in> A . f x = g x) \<and>
 (\<forall>h \<in> hom G H. \<forall>x \<in> A .f x = h x \<longrightarrow> (\<forall>y \<in> carrier G.  g y = h y))))))"

definition inclusion ("\<iota>")
  where "\<iota> g = [(g, True)]"

definition unlift :: "(('a, 'b) word set\<Rightarrow> 'c) \<Rightarrow> ('a, 'b) monoidgentype set\<Rightarrow> (('a, 'b) word set) set \<Rightarrow> ('a, 'b) word \<Rightarrow> 'c"
  where "unlift f S gens x = f (reln_tuple \<langle>S\<rangle> `` {x})"  

lemma (in group) genmap_closed:
  assumes cl: "f \<in> (\<iota> ` (S ::('c, 'd) monoidgentype set)) \<rightarrow> carrier G"
      and "g \<in> (\<iota> ` S) \<union> (wordinverse ` (\<iota> ` S))"
    shows "genmap (\<iota> ` S) f g \<in> carrier G"
proof-
  have 1:"g \<in> (\<iota> ` S) \<or> g \<in> (wordinverse ` (\<iota> ` S))" using assms(2) by blast
  then show ?thesis
  proof(cases "g \<in> (\<iota> ` S)")
    case True
    then show ?thesis using assms by (metis Pi_mem genmap_def)
  next
    case False
    then have 2: "g \<in> (wordinverse ` (\<iota> ` S))" using 1 by simp
    then have "genmap (\<iota> ` S) f g =  inv (f (wordinverse g))" by (simp add: False genmap_def)
    moreover have "wordinverse g  \<in> (\<iota> ` S)" by (metis 1 False image_iff wordinverse_symm)
    ultimately show ?thesis using assms by (metis Pi_mem Units_eq Units_inv_Units)
  qed
qed


fun (in group) genmapext
  where "genmapext S f [] = \<one>"|
"genmapext S f (x#xs) = (genmap S f [x]) \<otimes> (genmapext S f xs)"




lemma gen_spanset: assumes "xs \<in> \<langle>S\<rangle>" "xs \<noteq> []" shows "hd xs \<in> invgen S"
  by (metis assms(1) assms(2) freewords_on_def list.sel(1) words_on.cases)


lemma inclusion_union:
  assumes "a \<in> (S ::('a, 'b) monoidgentype set) \<times> {True, False}"
  shows "[a] \<in> (\<iota> ` S) \<union> (wordinverse ` (\<iota> ` S))"
proof(cases "snd a = True")
  case True
  have "fst a \<in> S" using assms by auto
  then show ?thesis by (metis (mono_tags, lifting) True UnI1 inclusion_def rev_image_eqI surjective_pairing)
next
  case False
  have 1:"fst a \<in> S" using assms by auto
  moreover have "snd a = False" using assms False by simp
  ultimately have "inverse a = (fst a, True)" by (metis inverse.simps(2) prod.collapse)
  then have "wordinverse [a] \<in> (\<iota> ` S)" by (simp add: 1 inclusion_def)
  then show ?thesis  by (metis UnCI imageI wordinverse_of_wordinverse)
qed

lemma (in group) genmapext_closed:
  assumes "f \<in> (\<iota> ` (S ::('c, 'd) monoidgentype set)) \<rightarrow> carrier G"
      and "x \<in> freewords_on  S"
    shows "genmapext (\<iota> ` S) f x \<in> carrier G"
  using assms
proof(induction x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  have a:"genmapext (\<iota> ` S) f (a # x) = genmap (\<iota> ` S) f [a] \<otimes>  (genmapext (\<iota> ` S)  f x)" by simp
  have "a \<in> S \<times> {True, False}"  using freewords_on_def gen_spanset invgen_def Cons by (metis list.distinct(1) list.sel(1))
  then have "[a] \<in> (\<iota> ` S) \<union> (wordinverse ` (\<iota> ` S))" using inclusion_union  by blast
  then have " genmap (\<iota> ` S) f [a] \<in> carrier G" using genmap_closed Cons.prems(1) by metis
  moreover have "x \<in> \<langle>S\<rangle>" using Cons.prems(2) freewords_on_def span_cons by blast
  ultimately show ?case using a by (simp add: Cons.IH assms(1))
qed

lemma (in group) genmapext_append:
  assumes "f \<in> (\<iota> ` (S ::('c, 'd) monoidgentype set)) \<rightarrow> carrier G"
      and "x \<in> freewords_on S"
      and "y \<in> freewords_on S"
    shows "genmapext (\<iota> ` S)  f (x @ y) = genmapext (\<iota> ` S) f x \<otimes> genmapext (\<iota> ` S) f y"
  using assms
proof(induction x)
  case Nil
  have "genmapext (\<iota> ` S) f [] = \<one>" by simp
  moreover have "genmapext (\<iota> ` S) f y \<in> carrier G" using genmapext_closed assms by auto
  then have "genmapext (\<iota> ` S) f [] \<otimes> genmapext (\<iota> ` S)  f y = genmapext (\<iota> ` S) f y" using r_one by simp
  then show ?case by simp
next
  case (Cons a x)
  have "a \<in> S \<times> {True, False}" using freewords_on_def gen_spanset invgen_def Cons by (metis list.distinct(1) list.sel(1))
  then have a:"[a] \<in> (\<iota> ` S) \<union> (wordinverse ` (\<iota> ` S))" using inclusion_union  by blast
  have x:"x \<in> \<langle>S\<rangle>" using Cons.prems(2) freewords_on_def span_cons by blast
  have "genmapext (\<iota> ` S) f (a # x) \<otimes> genmapext (\<iota> ` S) f y = genmap (\<iota> ` S) f [a] \<otimes> genmapext (\<iota> ` S) f x \<otimes> genmapext (\<iota> ` S) f y" by simp
  then have 1: "genmapext (\<iota> ` S) f (a # x) \<otimes> genmapext (\<iota> ` S) f y = genmap (\<iota> ` S) f [a] \<otimes> genmapext (\<iota> ` S) f (x @ y)" 
    using Cons.IH Cons.prems(1) Cons.prems(3)  a genmap_closed genmapext_closed m_assoc x by metis
  have "genmapext  (\<iota> ` S) f ((a # x) @ y) = genmapext (\<iota> ` S) f (a # (x  @ y))" by auto
  then have "genmapext (\<iota> ` S) f ((a #x) @ y) = genmap (\<iota> ` S) f [a] \<otimes> genmapext (\<iota> ` S) f (x @ y)" by simp
  then show ?case using 1 by auto
qed


lemma cancels_to_1_unfold:
  assumes "cancels_to_1 x y"
  obtains xs1 x1 x2 xs2
  where "x = xs1 @ x1 # x2 # xs2"
    and "y = xs1 @ xs2"
    and "inverse x1 = x2"
proof-
  assume a: "(\<And>xs1 x1 x2 xs2. \<lbrakk>x = xs1 @ x1 # x2 # xs2; y = xs1 @ xs2; inverse x1 =  x2\<rbrakk> \<Longrightarrow> thesis)"
  from assms
  obtain i where "cancels_to_1_at i x y"
    unfolding cancels_to_1_def by auto
  hence "inverse (x ! i) =  (x ! Suc i)"
    and "y = (take i x) @ (drop (Suc (Suc i)) x)"
    and "x = (take i x) @ x ! i # x ! Suc i # (drop (Suc (Suc i)) x)"
    unfolding cancel_at_def and cancels_to_1_at_def by (auto simp add: Cons_nth_drop_Suc)
  with a show thesis by blast
qed

lemma cancels_to_1_preserves:
  assumes "cancels_to_1 x y"
      and "x \<in> freewords_on S"
    shows "y \<in> freewords_on S"
proof-
  obtain xs1 x1 x2 xs2
  where x:"x = xs1 @ x1 # x2 # xs2"
    and y:"y = xs1 @ xs2"
    using assms cancels_to_1_unfold by metis
  have "xs1 \<in> freewords_on S" using x leftappend_span freewords_on_def assms(2) by blast
  moreover have "xs2 \<in> freewords_on S" using x rightappend_span freewords_on_def assms(2) span_cons by blast
  ultimately show ?thesis using y by (simp add: span_append freewords_on_def)
qed

lemma cancels_to_preserves:
  assumes "cancels_to x y"
      and "x \<in> freewords_on S"
    shows "y \<in> freewords_on S"
  using assms unfolding cancels_to_def
proof(induct rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then show ?case using cancels_to_1_preserves by auto
qed

lemma inclusion_snd:
  assumes "[x] \<in> (\<iota> ` S)"
  shows "snd x = True"
proof-
  show ?thesis using assms  by (metis image_iff inclusion_def last.simps old.prod.inject prod.collapse)
qed

lemma (in group) inverse_ext:
  assumes  "inverse x1 = x2"
  and "[x1] \<in> freewords_on (S ::('c, 'd) monoidgentype set)"
  and "[x2] \<in> freewords_on S"
  and "f \<in> (\<iota> ` S) \<rightarrow> carrier G"
  shows "(genmapext (\<iota> ` S) f [x1] \<otimes> genmapext (\<iota> ` S) f [x2]) = \<one>"
proof-
  have "genmapext (\<iota> ` S) f [x1] = genmap (\<iota> ` S) f [x1] \<otimes> \<one>" by simp
  have x1:"x1 \<in> S \<times> {True, False}" using  invgen_def gen_spanset freewords_on_def assms(2)  by (metis list.distinct(1) list.sel(1))
  then have "[x1] \<in> (\<iota> ` S) \<union> (wordinverse ` (\<iota> ` S))" using inclusion_union  by blast
  then have g1:"genmap (\<iota> ` S) f [x1] \<in> carrier G" using genmap_closed[of "f" "S" "[x1]"] assms(4) by fast
  moreover have "genmapext (\<iota> ` S) f [x1] = genmap (\<iota> ` S) f [x1] \<otimes> \<one>" by simp
  ultimately have 1:"genmapext (\<iota> ` S) f [x1] = genmap (\<iota> ` S) f [x1]" by simp
  have "genmapext (\<iota> ` S) f [x2] = genmap (\<iota> ` S) f [x2] \<otimes> \<one>" by simp
  have x2:"x2 \<in> S \<times> {True, False}" using  invgen_def gen_spanset freewords_on_def assms(3)  by (metis list.distinct(1) list.sel(1))
  then have "[x2] \<in> (\<iota> ` S) \<union> (wordinverse ` (\<iota> ` S))" using inclusion_union  by blast
  then have g2:"genmap (\<iota> ` S) f [x2] \<in> carrier G" using genmap_closed assms(4) by blast
  moreover have "genmapext (\<iota> ` S) f [x2] = genmap (\<iota> ` S) f [x2] \<otimes> \<one>" by simp
  ultimately have 2:"genmapext (\<iota> ` S) f [x2] = genmap (\<iota> ` S) f [x2]" by simp
  have fx1:"fst x1 \<in> S" using x1 by auto
  have fx2:"fst x2 \<in> S" using x2 by auto
  then show ?thesis
  proof (cases "snd x1 = False")
    case True
    then have "snd x2 = True" using assms(1) by (metis inverse.simps(2) snd_eqD surjective_pairing)
    then have "[x2] \<in> (\<iota> ` S)" using fx2 by (metis inclusion_def rev_image_eqI surjective_pairing)
    then have a:"genmap (\<iota> ` S) f [x2] = f [x2]" by (simp add: genmap_def)
    have "[x1] \<notin> (\<iota> ` S)" using inclusion_snd True  by metis
    moreover have "wordinverse [x1] = [x2]" by (simp add: assms(1))
    ultimately have "genmap (\<iota> ` S) f [x1] = inv (f [x2])" by (simp add: genmap_def)
    then show ?thesis  using 1 2 a  Units_eq Units_l_inv g2 by presburger
next
  case False
    then have T:"snd x1 = True" using assms(1) by (metis inverse.simps(2) snd_eqD surjective_pairing)
    then have "[x1] \<in> (\<iota> ` S)" using fx1 by (metis inclusion_def rev_image_eqI surjective_pairing)
    then have a:"genmap (\<iota> ` S) f [x1] = f [x1]" by (simp add: genmap_def)
    have "snd x2 = False" using T assms(1) by (metis eq_snd_iff inverse.simps(1))
    then have "[x2] \<notin> (\<iota> ` S)" using inclusion_snd  by metis
    moreover have "wordinverse [x2] = [x1]"  
      using assms(1) x1 by auto 
    ultimately have "genmap (\<iota> ` S) f [x2] = inv (f [x1])" by (simp add: genmap_def)
    then show ?thesis  using 1 2 a Units_eq Units_r_inv g1 by presburger
  qed
qed


lemma (in group) genmapext_cancels_to:
  assumes "cancels_to x y"
      and "x \<in> freewords_on (S ::('c, 'd) monoidgentype set)"
      and "y \<in> freewords_on S"
      and  "f \<in> (\<iota> ` S) \<rightarrow> carrier G"
  shows "genmapext (\<iota> ` S) f x = genmapext (\<iota> ` S) f y"
using assms
unfolding cancels_to_def
proof(induct rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by auto
  case (rtrancl_into_rtrancl a b c)
obtain c1 x1 x2 c2
      where b: "b = c1 @ x1 # x2 # c2"
      and c: "c = c1 @ c2"
      and i: "inverse x1 = x2"
  using cancels_to_1_unfold rtrancl_into_rtrancl.hyps(3) by blast
  have bin: "b \<in> freewords_on S" using cancels_to_preserves  cancels_to_def rtrancl_into_rtrancl.prems(1) rtrancl_into_rtrancl.hyps(1)  by metis
  have c1:"c1 \<in> freewords_on S" using b bin  freewords_on_def leftappend_span by blast
  moreover have fx1:"([x1] @ [x2] @ c2)\<in> freewords_on S" using b bin  freewords_on_def rightappend_span by fastforce
  moreover then have x1:"[x1] \<in> freewords_on S" using fx1  freewords_on_def leftappend_span by blast
  moreover  have fx2: "([x2] @ c2) \<in> freewords_on S" using fx1  freewords_on_def rightappend_span by fastforce
  moreover then have x2:"[x2] \<in> freewords_on S" using  freewords_on_def leftappend_span by blast
  moreover  have c2: "c2 \<in> freewords_on S" using fx2  freewords_on_def rightappend_span by fastforce
  ultimately have 2: "genmapext (\<iota> ` S) f (c1 @ [x1] @ [x2] @ c2) = genmapext (\<iota> ` S) f c1  \<otimes> (genmapext (\<iota> ` S) f [x1] \<otimes> genmapext (\<iota> ` S) f [x2]) \<otimes> genmapext (\<iota> ` S) f c2" using genmapext_append rtrancl_refl.prems(3) by (smt (z3) genmapext_closed m_assoc m_closed)
  then have "genmapext (\<iota> ` S) f (c1 @ [x1] @ [x2] @ c2) = genmapext (\<iota> ` S) f c1  \<otimes> \<one> \<otimes> genmapext (\<iota> ` S) f c2" using inverse_ext i x1 x2 assms(4) by metis
  then have "genmapext (\<iota> ` S) f (c1 @ [x1] @ [x2] @ c2) = genmapext (\<iota> ` S) f c1  \<otimes>  genmapext (\<iota> ` S) f c2" 
    using c1 c2 assms(4) genmapext_closed by (metis l_cancel_one' one_closed)
  then have "genmapext (\<iota> ` S) f (c1 @ [x1] @ [x2] @ c2) = genmapext (\<iota> ` S) f (c1@c2)" 
    using genmapext_append c1 c2 assms(4) by metis
  then have "genmapext (\<iota> ` S) f b = genmapext (\<iota> ` S) f c" using b c by simp
  then show ?case using rtrancl_into_rtrancl by (simp add: bin)
qed

lemma (in group) genmapext_reln_tuple:
  assumes "(x,y) \<in> (reln_tuple (freewords_on (S ::('c, 'd) monoidgentype set)))"
      and "x \<in> freewords_on S"
      and "y \<in> freewords_on S"
      and  "f \<in> (\<iota> ` S) \<rightarrow> carrier G"
  shows "genmapext (\<iota> ` S) f x = genmapext (\<iota> ` S) f y"
proof-
  let ?rx = "(reduce^^(length x)) x"
  let ?ry = "(reduce^^(length y)) y"
  have "cancels_to x ?rx" by (simp add: iter_cancels_to)
  moreover then have "?rx  \<in> freewords_on S" using assms cancels_to_preserves by blast
  ultimately have x:"genmapext (\<iota> ` S) f x = genmapext (\<iota> ` S) f ?rx"  using genmapext_cancels_to[of "x" "?rx" "S" "f"] assms(2) assms(4) by auto 
  have  "cancels_to y ?ry" by (simp add: iter_cancels_to)
  moreover then have ryg:"?ry  \<in> freewords_on S" using assms cancels_to_preserves by blast
  ultimately have y:"genmapext (\<iota> ` S) f y = genmapext (\<iota> ` S) f ?ry"  using genmapext_cancels_to[of "y" "?ry" "S" "f"] assms(3) assms(4) by auto
  have "FreeGroupMain.reln x y" using assms(1) reln_tuple_def assms by (metis (no_types, lifting) case_prodD mem_Collect_eq)
  then have "cancels_eq x y" using reln_imp_cancels by blast
  then have "?rx = ?ry" using cancels_imp_iter by blast
  then show ?thesis using x y by simp
qed

lemma (in group) congruentlift: assumes "f \<in> (\<iota> ` (S::('c,'d) monoidgentype set)) \<rightarrow> carrier G" shows "congruent (reln_tuple (freewords_on S)) (genmapext (\<iota> ` S) f)"
  unfolding congruent_def
proof-
  have "(\<And>x y. (x, y) \<in> (reln_tuple \<langle>S\<rangle>) \<Longrightarrow> (genmapext (\<iota> ` S) f x) = (genmapext (\<iota> ` S) f y))"
  proof-
    fix x y assume assm: "(x, y) \<in> (reln_tuple \<langle>S\<rangle>)"
    moreover then have "x \<in> \<langle>S\<rangle>" using reln_tuple_def by auto
    moreover have "y \<in> \<langle>S\<rangle>" using reln_tuple_def assm  by auto
    ultimately show "(genmapext (\<iota> ` S) f x) = (genmapext (\<iota> ` S) f y)" using genmapext_reln_tuple assms by blast
  qed
  then show "\<forall>(y, z)\<in>reln_tuple \<langle>S\<rangle>. genmapext (\<iota> ` S) f y = genmapext (\<iota> ` S)  f z" by blast
qed

definition (in group) genmapext_proj where "genmapext_proj S f a = (\<Union>x \<in> a. {genmapext S f x})"

lemma (in group) genmapext_proj_wd:
  assumes " A \<in> quotient \<langle>(S::('c,'d) monoidgentype set)\<rangle> (reln_tuple \<langle>S\<rangle>)" 
          "a \<in> A" 
          "f \<in> (\<iota> ` S) \<rightarrow> carrier G" 
          shows "genmapext_proj (\<iota> ` S) f A = {genmapext (\<iota> ` S) f a}"
proof-
  have "\<forall> x \<in> A . ({genmapext (\<iota> ` S) f x} = {genmapext (\<iota> ` S) f a})"
  proof-
    have "(\<And>x. x \<in> A \<Longrightarrow> ({genmapext (\<iota> ` S) f x} = {genmapext (\<iota> ` S) f a}))"
    proof-
      fix x  assume assm: "x \<in> A"
      then have "(x, a)\<in>reln_tuple \<langle>S\<rangle>" by (meson assms(1) assms(2) quotient_eq_iff reln_equiv)
      then have "genmapext (\<iota> ` S) f x = genmapext (\<iota> ` S) f a" 
        using assms(3) congruentlift unfolding congruent_def by blast 
      then show "{genmapext (\<iota> ` S) f x} = {genmapext (\<iota> ` S) f a}" by simp
    qed
    then show "\<forall> x \<in> A . ({genmapext (\<iota> ` S) f x} = {genmapext (\<iota> ` S) f a})" by simp
  qed
  then show ?thesis unfolding genmapext_proj_def using assms(2) by blast
qed

definition (in group) genmapext_lift where "genmapext_lift S f a = (THE x. x \<in> genmapext_proj S f a)"

lemma (in group) genmapext_lift_wd:
assumes " A \<in> quotient \<langle>(S::('c,'d) monoidgentype set)\<rangle> (reln_tuple \<langle>S\<rangle>)" 
          "a \<in> A" 
          "f \<in> (\<iota> ` S) \<rightarrow> carrier G" 
        shows "genmapext_lift (\<iota> ` S) f A = genmapext (\<iota> ` S) f a"
  unfolding genmapext_lift_def
proof-
  have "genmapext_proj (\<iota> ` S) f A = {genmapext (\<iota> ` S) f a}" using assms genmapext_proj_wd by blast
  then show "(THE x. x \<in> genmapext_proj (\<iota> ` S) f A) = genmapext (\<iota> ` S) f a"  by simp
qed

lemma (in group) genmapext_lift_hom:
  assumes "f \<in> (\<iota> ` (S::('c,'d) monoidgentype set)) \<rightarrow> carrier G"
  shows "genmapext_lift (\<iota> ` S) f \<in> hom (freegroup S) G"
proof-
  { 
  fix x
  assume "x \<in> carrier (freegroup S)"
  then have x2: "x \<in>   quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" unfolding freegroup_def by simp
  moreover then obtain x1 where x1:"x1 \<in> x" by (metis all_not_in_conv in_quotient_imp_non_empty reln_equiv)
  ultimately have xx1: "x = ((reln_tuple \<langle>S\<rangle>)``{x1})"  by (metis (no_types, lifting) Image_singleton_iff equiv_class_eq quotientE reln_equiv)
  then have xin: "x1 \<in> \<langle>S\<rangle>" by (meson in_mono in_quotient_imp_subset reln_equiv x1 x2)
  have "genmapext_lift (\<iota> ` S) f x = genmapext (\<iota> ` S) f x1" using genmapext_lift_wd x2 x1 assms(1) 
    by (simp add: genmapext_lift_wd) (* by simp*)
  then have "genmapext_lift (\<iota> ` S) f x \<in> carrier G" using genmapext_closed  assms(1) xin 
    by (simp add: genmapext_closed) 
}
  moreover
  {
  fix x assume x:"x \<in> carrier (freegroup S)"
  fix y assume y:"y \<in> carrier (freegroup S)"
  have x2:"x \<in>   quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" using freegroup_def x by (metis partial_object.select_convs(1))
  moreover then obtain x1 where x1:"x1 \<in> x" by (metis all_not_in_conv in_quotient_imp_non_empty reln_equiv)
  ultimately have xx1: "x = ((reln_tuple \<langle>S\<rangle>)``{x1})"  by (metis (no_types, lifting) Image_singleton_iff equiv_class_eq quotientE reln_equiv)
  then have xin: "x1 \<in> \<langle>S\<rangle>" by (meson in_mono in_quotient_imp_subset reln_equiv x1 x2)
  have y2:"y \<in>   quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" using freegroup_def y by (metis partial_object.select_convs(1))
  moreover then obtain y1 where y1:"y1 \<in> y" by (metis all_not_in_conv in_quotient_imp_non_empty reln_equiv)
  ultimately have yy1:"y = ((reln_tuple \<langle>S\<rangle>)``{y1})"  by (metis (no_types, lifting) Image_singleton_iff equiv_class_eq quotientE reln_equiv)
  then have yin:"y1 \<in> \<langle>S\<rangle>" by (meson in_mono in_quotient_imp_subset reln_equiv y1 y2)
  have 1:"x \<otimes>\<^bsub>(freegroup S)\<^esub> y = proj_append \<langle>S\<rangle> (x) (y)" by (simp add: freegroup_def)
  then have "x \<otimes>\<^bsub>(freegroup S)\<^esub> y = proj_append \<langle>S\<rangle> ((reln_tuple \<langle>S\<rangle>)``{x1}) ((reln_tuple \<langle>S\<rangle>)``{y1})" using xx1 yy1 by simp
  then have 2:"x \<otimes>\<^bsub>(freegroup S)\<^esub> y = ((reln_tuple \<langle>S\<rangle>)``{x1@y1})" using proj_append_wd x2 y2 x1 y1 reln_equiv by (metis (no_types, lifting)   quotient_eq_iff refl_onD1 reln_refl)
  then have "genmapext_lift (\<iota> ` S) f (x \<otimes>\<^bsub>(freegroup S)\<^esub> y) = genmapext_lift (\<iota> ` S) f ((reln_tuple \<langle>S\<rangle>)``{x1@y1})" by simp
  moreover  have "((reln_tuple \<langle>S\<rangle>)``{x1@y1}) \<in> quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)"  by (metis 1 2 proj_append_clos x2 y2)
  moreover have "(x1@y1) \<in> ((reln_tuple \<langle>S\<rangle>)``{x1@y1})" using append_congruent eq_equiv_class equiv_2f_clos reln_equiv x1 x2 y1 y2 by fastforce 
  ultimately have "genmapext_lift (\<iota> ` S) f (x \<otimes>\<^bsub>(freegroup S)\<^esub> y) = genmapext (\<iota> ` S) f (x1@y1)" using genmapext_lift_wd[of "((reln_tuple \<langle>S\<rangle>)``{x1@y1})" "S" "(x1@y1)" "f"] using assms by presburger
  then have "genmapext_lift (\<iota> ` S) f (x \<otimes>\<^bsub>(freegroup S)\<^esub> y) = genmapext (\<iota> ` S) f x1 \<otimes> genmapext (\<iota> ` S) f y1" using genmapext_append xin yin assms(1) by auto
  then have "genmapext_lift (\<iota> ` S) f (x \<otimes>\<^bsub>(freegroup S)\<^esub> y) = (genmapext_lift (\<iota> ` S) f x) \<otimes> (genmapext_lift (\<iota> ` S) f y)" using genmapext_lift_wd x2 x1 y2 y1  assms(1) 
    by metis
}
  ultimately show ?thesis by (simp add: homI)
qed

definition liftgen where "liftgen S = (\<Union>x \<in> (\<iota> ` S).{reln_tuple \<langle>S\<rangle> ``{x}})"

lemma (in group) unlift_S: assumes "f \<in> liftgen S \<rightarrow> carrier G"
  shows "unlift f S (liftgen S) \<in> (\<iota> ` (S::('c,'d) monoidgentype set)) \<rightarrow> carrier G"
proof(rule funcsetI)
  fix x assume assm:"x \<in> \<iota> ` S"
  have "(reln_tuple \<langle>S\<rangle> ``{x}) \<in> (\<Union>x \<in> (\<iota> ` (S::('c,'d) monoidgentype set)).{reln_tuple \<langle>S\<rangle> ``{x}} )" using assm by blast
  then have "f (reln_tuple \<langle>S\<rangle> ``{x}) \<in> carrier G" using assms Pi_split_insert_domain unfolding liftgen_def by fastforce
  moreover have "f (reln_tuple \<langle>S\<rangle> ``{x}) = unlift f S (liftgen S) x"  by (simp add: unlift_def)
  ultimately show "unlift f S (liftgen S) x \<in> carrier G" by simp
qed

lemma (in group) genmapext_unlift_hom: assumes 
               "f \<in> liftgen (S::('c,'d) monoidgentype set) \<rightarrow> carrier G"
  shows "genmapext_lift (\<iota> ` S) (unlift f S (liftgen S)) \<in> hom (freegroup S) G"
  by (simp add: assms genmapext_lift_hom unlift_S)

lemma inclusion_subset_spanset:"(\<iota> ` S) \<subseteq> \<langle>S\<rangle>"
proof(rule subsetI)
  fix x assume assms:"x \<in> \<iota> ` S"
  then have "fst (hd x) \<in> S" by (metis fstI image_iff inclusion_def list.sel(1))
  moreover have "snd (hd x) \<in> {True, False}" by simp
  ultimately have "hd x \<in> invgen S" unfolding invgen_def by (simp add: mem_Times_iff)
  moreover have "x = ((hd x)#[])" using assms inclusion_def by (metis image_iff list.sel(1))
  ultimately show "x \<in> \<langle>S\<rangle>" unfolding freewords_on_def using empty gen by metis
qed

lemma liftgen_subset_quotient:"(liftgen S) \<subseteq> quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)"
proof(rule subsetI)
  fix x assume assms:"x \<in> liftgen S"
  then have "x \<in> (\<Union>x \<in> (\<iota> ` S).{reln_tuple \<langle>S\<rangle> ``{x}})" by (simp add: liftgen_def)
  then obtain x1 where "x = (reln_tuple \<langle>S\<rangle> ``{x1}) \<and> x1 \<in> (\<iota> ` S)" by blast
  then moreover have "x1 \<in> \<langle>S\<rangle>" using inclusion_subset_spanset by auto
  ultimately show "x \<in> \<langle>S\<rangle> // reln_tuple \<langle>S\<rangle>" by (simp add: quotientI)
qed 

lemma inclusion_hd: assumes "x \<in> (\<iota> ` S)"
  shows "(hd x#[]) = x"
proof-
  show ?thesis using assms inclusion_def by (metis image_iff list.sel(1))
qed

lemma (in group) genmapext_unlift_ext: 
  assumes "f \<in> liftgen (S::('c,'d) monoidgentype set) \<rightarrow> carrier G" 
  shows "\<And>x. x \<in> (liftgen S) \<Longrightarrow> f x = genmapext_lift (\<iota> ` S) (unlift f S (liftgen S)) x"
proof-
  fix x assume assm:"x \<in> (liftgen S)"
  then have x:"x \<in> quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" using liftgen_subset_quotient by auto
  have "x \<in> (\<Union>x \<in> (\<iota> ` S).{reln_tuple \<langle>S\<rangle> ``{x}})" using assm by (simp add: liftgen_def)
  then obtain x1 where x1x:"x = (reln_tuple \<langle>S\<rangle> ``{x1}) \<and> x1 \<in> (\<iota> ` S)" by blast
  then have x1s:"x1 \<in> \<langle>S\<rangle>" using inclusion_subset_spanset by blast
  then have "x1 \<in> x" using reln_tuple_def reln_refl x1x by fastforce
  then have A:"genmapext_lift (\<iota> ` S) (unlift f S (liftgen S)) x = genmapext (\<iota> ` S) (unlift f S (liftgen S)) x1" using  x assms genmapext_lift_wd[of "x" "S" "x1"] by (simp add: unlift_S)
  have "x1 = (hd x1#[])" using x1x by (metis inclusion_hd)
  then have "genmapext (\<iota> ` S) (unlift f S (liftgen S)) x1 = (genmap (\<iota> ` S) (unlift f S (liftgen S)) x1) \<otimes> \<one>" using genmapext.simps by metis
  then have "genmapext (\<iota> ` S) (unlift f S (liftgen S)) x1 = (genmap (\<iota> ` S) (unlift f S (liftgen S)) x1)" using genmap_closed[of "(unlift f S (liftgen S))" "S" "x1"] unlift_S[of "f" "S"] assms by (simp add: x1x)
  then have "genmapext (\<iota> ` S) (unlift f S (liftgen S)) x1 = (unlift f S (liftgen S)) x1" using x1x unfolding genmap_def by simp
  then have "genmapext (\<iota> ` S) (unlift f S (liftgen S)) x1 = f x" using  x1x by (simp add: unlift_def)
  then show "f x = genmapext_lift (\<iota> ` S) (unlift f S (liftgen S)) x" using A by simp
qed

lemma (in group) span_liftgen: "\<langle>liftgen S\<rangle>\<^bsub>(freegroup S)\<^esub>  \<subseteq> carrier (freegroup S)"
proof-
  have "carrier (freegroup S) = quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" by (simp add: freegroup_def)
  moreover have "(liftgen S)  \<subseteq> quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" by (simp add: liftgen_subset_quotient)
  ultimately show ?thesis by (metis freegroup_is_group group.gen_span_closed)
qed

lemma invgen_elem: assumes "x \<in> invgen S" shows "[x] \<in> (\<iota> ` S) \<or> wordinverse [x] \<in> (\<iota> ` S)"
 proof(cases "snd x = True")
   case True
   moreover have fx:"fst x \<in> S" using assms invgen_def[of "S"] by (metis mem_Sigma_iff prod.collapse)
  ultimately have "[x] \<in> (\<iota> ` S)" using assms fx inclusion_def  by (metis (mono_tags, lifting) image_iff prod.collapse)
  then show "[x] \<in> (\<iota> ` S) \<or> wordinverse [x] \<in> (\<iota> ` S)"  by blast
next
  case False
  then have "snd x = False" using assms by auto
  moreover have "wordinverse [x] = (inverse x)#[]" by simp
moreover have fx:"fst x \<in> S" using assms invgen_def[of "S"] by (metis mem_Sigma_iff prod.collapse)
  ultimately have "wordinverse [x] \<in> (\<iota> ` S)" using inverse.simps(2) assms fx inclusion_def  by (metis (mono_tags, lifting) image_iff prod.collapse)
  then show "[x] \<in> (\<iota> ` S) \<or> wordinverse [x] \<in> (\<iota> ` S)" by blast
qed

lemma (in group) wordinverse_inv: 
  assumes "x \<in> carrier (freegroup S)" "x = (reln_tuple \<langle>S\<rangle>) `` {x1}"
  shows "inv\<^bsub>(freegroup S)\<^esub> x = (reln_tuple \<langle>S\<rangle>) `` {wordinverse x1}"
proof-
  have nil: "[] \<in> \<langle>S\<rangle>"  by (simp add: freewords_on_def words_on.empty)
  have 1:"x1 \<in> \<langle>S\<rangle>" using assms unfolding freegroup_def using in_quotient_imp_non_empty refl_onD1 reln_equiv reln_refl by fastforce
  then have 2:"wordinverse x1 \<in> \<langle>S\<rangle>"  
    using span_wordinverse by auto
  then have A:"(reln_tuple \<langle>S\<rangle>) `` {wordinverse x1} \<in> carrier (freegroup S)" unfolding freegroup_def by (simp add: quotientI)
  have "x \<otimes>\<^bsub>(freegroup S)\<^esub> (reln_tuple \<langle>S\<rangle>) `` {wordinverse x1} = (proj_append \<langle>S\<rangle>) ((reln_tuple \<langle>S\<rangle>) `` {x1}) ((reln_tuple \<langle>S\<rangle>) `` {wordinverse x1})" using assms  by (simp add: freegroup_def)
  then have "x \<otimes>\<^bsub>(freegroup S)\<^esub> (reln_tuple \<langle>S\<rangle>) `` {wordinverse x1} 
       = ((reln_tuple \<langle>S\<rangle>) `` {x1@wordinverse x1})" using proj_append_wd
    using "1" "2" by blast
  moreover have "x1@(wordinverse x1) \<in> \<langle>S\<rangle>" using 1 2 span_append freewords_on_def by blast
  moreover then have "((x1@(wordinverse x1)), []) \<in> reln_tuple \<langle>S\<rangle>" using nil wordinverse_inverse reln_tuple_def by auto
  moreover then have "reln_tuple \<langle>S\<rangle> `` {x1@(wordinverse x1)} = reln_tuple \<langle>S\<rangle> `` {[]}" by (metis equiv_class_eq reln_equiv)
  ultimately have "x \<otimes>\<^bsub>(freegroup S)\<^esub> (reln_tuple \<langle>S\<rangle>) `` {wordinverse x1} = reln_tuple \<langle>S\<rangle> `` {[]}" by simp
  then have B:"x \<otimes>\<^bsub>(freegroup S)\<^esub> (reln_tuple \<langle>S\<rangle>) `` {wordinverse x1} = \<one>\<^bsub>(freegroup S)\<^esub>" by (simp add: freegroup_def)
  have " (reln_tuple \<langle>S\<rangle>) `` {wordinverse x1}  \<otimes>\<^bsub>(freegroup S)\<^esub> x = (proj_append \<langle>S\<rangle>) ((reln_tuple \<langle>S\<rangle>) `` {wordinverse x1}) ((reln_tuple \<langle>S\<rangle>) `` {x1})"  using assms  by (simp add: freegroup_def)
  then moreover have "proj_append \<langle>S\<rangle>  ((reln_tuple \<langle>S\<rangle>)``{wordinverse x1}) ((reln_tuple \<langle>S\<rangle>)``{x1}) 
      = reln_tuple \<langle>S\<rangle> `` {(wordinverse x1)@x1}"  
    by (meson "1" "2" proj_append_wd) 
  moreover have "(wordinverse x1)@x1 \<in> \<langle>S\<rangle>" using 1 2 span_append freewords_on_def by blast
  moreover then have "(((wordinverse x1)@x1), []) \<in> reln_tuple \<langle>S\<rangle>" using nil inverse_wordinverse reln_tuple_def by auto
  moreover then have "reln_tuple \<langle>S\<rangle> `` {(wordinverse x1)@x1} = reln_tuple \<langle>S\<rangle> `` {[]}" by (metis equiv_class_eq reln_equiv)
  ultimately have C:"(reln_tuple \<langle>S\<rangle>) `` {wordinverse x1}  \<otimes>\<^bsub>(freegroup S)\<^esub> x = \<one>\<^bsub>(freegroup S)\<^esub>" by (simp add: freegroup_def)
  show ?thesis 
    by (meson A C assms(1) freegroup_is_group group.inv_equality)
qed

lemma inclusion_liftgen: assumes "x \<in> (\<iota> ` S)" shows "(reln_tuple \<langle>S\<rangle> `` {x}) \<in> liftgen S"
  using assms unfolding liftgen_def
proof-
  fix x assume "x \<in> \<iota> ` S"
  then show "reln_tuple \<langle>S\<rangle> `` {x} \<in> (\<Union>x\<in>\<iota> ` S. {reln_tuple \<langle>S\<rangle> `` {x}})" by blast
qed

lemma (in group) liftgen_span: "carrier (freegroup S) \<subseteq> \<langle>liftgen S\<rangle>\<^bsub>(freegroup S)\<^esub>"
proof(rule subsetI)
  fix x assume assm: "x \<in> carrier (freegroup S)"
  have "carrier (freegroup S) = quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" by (simp add: freegroup_def)
  then have x:"x \<in> quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" using assm by simp
  then show "x \<in> \<langle>liftgen S\<rangle>\<^bsub>freegroup S\<^esub>"
  proof(cases "x = \<one>\<^bsub>freegroup S\<^esub>")
case True
  then show ?thesis by simp
next
  case False
  then obtain x1 where def:"x = (reln_tuple \<langle>S\<rangle> ``{x1}) \<and> (x1 \<in> \<langle>S\<rangle>)"  by (meson x quotientE)
  then have "(x1 \<in> \<langle>S\<rangle>)" by simp
  then have "(reln_tuple \<langle>S\<rangle> ``{x1}) \<in> \<langle>liftgen S\<rangle>\<^bsub>freegroup S\<^esub>"
  proof(induction x1)
    case Nil
    have "\<one>\<^bsub>freegroup S\<^esub> = reln_tuple \<langle>S\<rangle> `` {[]}" by (simp add: freegroup_def)
  then show ?case  by (metis gen_span.gen_one)
next
  case (Cons a x1)
  then have a: "[a] \<in> \<langle>S\<rangle>" using Cons cons_span  freewords_on_def by blast
  moreover have c1:"x1  \<in> \<langle>S\<rangle>" using Cons span_cons  freewords_on_def by blast
  ultimately have wd:"reln_tuple \<langle>S\<rangle> `` {a # x1} = (proj_append \<langle>S\<rangle>) (reln_tuple \<langle>S\<rangle> `` {[a]})  (reln_tuple \<langle>S\<rangle> `` {x1})"  by (simp add: proj_append_wd)
  have x1in:"reln_tuple \<langle>S\<rangle> `` {x1} \<in> \<langle>liftgen S\<rangle>\<^bsub>freegroup S\<^esub>" using Cons by (simp add: c1)
  have "wordinverse [a] \<in> \<langle>S\<rangle>" using a span_wordinverse by blast
  then have inva: "reln_tuple \<langle>S\<rangle> `` {wordinverse [a]} \<in> carrier (freegroup S)" using freegroup_def by (simp add: freegroup_def quotientI)
  have invgen:"a \<in> (invgen S)" using a by (metis words_on.cases list.inject not_Cons_self2 freewords_on_def)
  then show ?case
  proof(cases "[a]  \<in> (\<iota> ` S)")
    case True
    then have "(reln_tuple \<langle>S\<rangle> `` {[a]}) \<in> liftgen S" by (simp add: inclusion_liftgen)
    then have "(reln_tuple \<langle>S\<rangle> `` {[a]}) \<in> \<langle>liftgen S\<rangle>\<^bsub>(freegroup S)\<^esub>"  
      by (simp add: gen_span.gen_gens)
    then have "(proj_append \<langle>S\<rangle>) (reln_tuple \<langle>S\<rangle> `` {[a]})  (reln_tuple \<langle>S\<rangle> `` {x1}) \<in> \<langle>liftgen S\<rangle>\<^bsub>(freegroup S)\<^esub>" using freegroup_def x1in gen_mult[of "(reln_tuple \<langle>S\<rangle> `` {[a]})" "freegroup S" "liftgen S" "(reln_tuple \<langle>S\<rangle> `` {x1})"] by (metis monoid.select_convs(1))
    then show ?thesis using wd by simp 
next
  case False
  then have "wordinverse [a] \<in> \<iota> ` S" using invgen invgen_elem by blast
  then have "(reln_tuple \<langle>S\<rangle> `` {wordinverse [a]}) \<in> liftgen S" by (simp add: inclusion_liftgen)
  then have 1: "(reln_tuple \<langle>S\<rangle> `` {wordinverse [a]}) \<in> \<langle>liftgen S\<rangle>\<^bsub>(freegroup S)\<^esub>" 
    by (simp add: gen_span.gen_gens)
  have "wordinverse (wordinverse [a]) = [a]"  using wordinverse_of_wordinverse by blast
  then have "inv\<^bsub>(freegroup S)\<^esub> (reln_tuple \<langle>S\<rangle> `` {wordinverse [a]}) = (reln_tuple \<langle>S\<rangle> `` { [a]})" using inva wordinverse_inv[of "(reln_tuple \<langle>S\<rangle> `` {wordinverse [a]})" "S" "wordinverse [a]"] by auto
  then have "(reln_tuple \<langle>S\<rangle> `` { [a]}) \<in> \<langle>liftgen S\<rangle>\<^bsub>(freegroup S)\<^esub>" using 1  by (metis gen_span.gen_inv)
  then have "(proj_append \<langle>S\<rangle>) (reln_tuple \<langle>S\<rangle> `` {[a]})  (reln_tuple \<langle>S\<rangle> `` {x1}) \<in> \<langle>liftgen S\<rangle>\<^bsub>(freegroup S)\<^esub>" using freegroup_def x1in gen_mult[of "(reln_tuple \<langle>S\<rangle> `` {[a]})" "freegroup S" "liftgen S" "(reln_tuple \<langle>S\<rangle> `` {x1})"] by (metis monoid.select_convs(1))
  then show ?thesis using wd by simp
qed
qed
  then show ?thesis using def by simp
qed
qed

lemma (in group) genmapext_unlift_uni:
  assumes "group G"
  and "f  \<in> liftgen (S::('c,'d) monoidgentype set) \<rightarrow> carrier G"
  and "h \<in> hom (freegroup S) G"
  and "\<forall> x \<in> (liftgen S) . f x = h x"
shows "\<forall>y \<in> carrier (freegroup S).  (genmapext_lift (\<iota> ` S) (unlift f S (liftgen S))) y = h y"
proof-
  have 1:"group (freegroup S)" by (simp add: freegroup_is_group)
  have "\<forall> x \<in> (liftgen S) . f x = (genmapext_lift (\<iota> ` S) (unlift f S (liftgen S))) x" using genmapext_unlift_ext assms(2) by blast
  then have "\<forall> x \<in> (liftgen S) . (genmapext_lift (\<iota> ` S) (unlift f S (liftgen S))) x = h x" using assms(4) by auto
  moreover have "(liftgen S) \<subseteq> carrier (freegroup S)" by (simp add: freegroup_def liftgen_subset_quotient)
  moreover have "(genmapext_lift (\<iota> ` S) (unlift f S (liftgen S))) \<in> hom (freegroup S) G" using assms(2) by (simp add: genmapext_unlift_hom)
  ultimately have "\<forall>x \<in> \<langle>(liftgen S)\<rangle>\<^bsub>(freegroup S)\<^esub>. (genmapext_lift (\<iota> ` S) (unlift f S (liftgen S))) x = h x" using hom_unique_on_span assms 1 by blast
  then show ?thesis  using liftgen_span by blast
qed

lemma "carrier (freegroup S) = \<langle>liftgen S\<rangle>\<^bsub>(freegroup S)\<^esub>"
  by (meson freegroup_is_group group.liftgen_span group.span_liftgen subset_antisym)


text \<open>The following lemma proves that, every function from the generating set S to a group G, 
extends to a homomorphism from the freegroup generated by S to G.\<close>

theorem (in group) exists_hom:
  assumes "group G"
      and "f  \<in>  (S::('c,'d) monoidgentype set) \<rightarrow> carrier G"
    shows "\<exists>h \<in> hom (freegroup S) G. \<forall> x \<in> S. f x = h (reln_tuple \<langle>S\<rangle> `` {\<iota>  x})"
proof-
  have "inj_on \<iota> S" unfolding inclusion_def 
    by (meson Pair_inject inj_onI list.inject)
  hence bij_step:"bij_betw \<iota> S (\<iota> ` S)" unfolding inclusion_def 
    by (meson \<open>inj_on \<iota> S\<close> bij_betw_imageI inclusion_def inj_on_cong)
  then have inv:"\<forall>x \<in>  S. (the_inv_into S \<iota>) (\<iota> x) = x" unfolding the_inv_into_def bij_betw_def
       inj_on_def by auto
  define f' where "f' = f \<circ> (the_inv_into S \<iota>)" 
  have "f' \<in> (\<iota> ` S) \<rightarrow> carrier G" using bij_step inv unfolding f'_def using assms(2) by force
  then have step1:"genmapext_lift (\<iota> ` S) f' \<in> hom (freegroup S) G" using genmapext_lift_hom
    by (simp add: \<open>\<And>f S. f \<in> \<iota> ` S \<rightarrow> carrier G \<Longrightarrow> genmapext_lift (\<iota> ` S) f \<in> hom F\<^bsub>S\<^esub> G\<close>)
  define h where "h = genmapext_lift (\<iota> ` S) f'"
  {fix x
   assume "x \<in> \<iota> ` S"
   hence ext_eq:"genmapext_lift (\<iota> ` S) f' (reln_tuple \<langle>S\<rangle> `` {x}) =  genmapext (\<iota> ` S) f' x"
     using genmapext_lift_wd 
     by (smt (verit, best) Set.set_insert \<open>f' \<in> \<iota> ` S \<rightarrow> carrier G\<close> equiv_class_self inclusion_subset_spanset insert_subset quotientI reln_equiv)
  hence "h (reln_tuple \<langle>S\<rangle> `` {x}) =  genmapext (\<iota> ` S) f' x" unfolding h_def by simp}
  moreover then have "\<forall>x \<in> S. f x = genmapext (\<iota> ` S) f' (\<iota> x)" unfolding f'_def 
    by (smt (z3) PiE assms(2) genmap_def genmapext.simps(1) genmapext.simps(2) image_eqI inclusion_def inv o_apply r_one)
  moreover then have "\<forall> x \<in> S. f x = f' (\<iota> x)" unfolding f'_def using inv by force
  ultimately have "\<forall> x \<in> S. f x = h (reln_tuple \<langle>S\<rangle> `` {\<iota> x})" by simp
  then show ?thesis using step1 h_def by fast
qed

text\<open>The following theorem proves that if a function f from a generating set S to a group G, 
extends to homomorphims h and g from the freegroup on S to G, then h and g are unique upto
their restriction on the carrier set of the freegroup. With the previous theorem, this
suffices to show the existence and uniqueness of homomorphism extensions from freegroup S to 
G. \<close>
theorem (in group) uniqueness_of_lift:
  assumes "group G"
     and "f  \<in>  (S::('c,'d) monoidgentype set) \<rightarrow> carrier G"
     and "h \<in> hom (freegroup S) G" "g \<in> hom (freegroup S) G"
     and "\<forall> x \<in> S. f x = h (reln_tuple \<langle>S\<rangle> `` {\<iota>  x})"
     and "\<forall> x \<in> S. f x = g (reln_tuple \<langle>S\<rangle> `` {\<iota>  x})"
   shows "\<forall> x \<in> carrier (freegroup S).  h x  = g x"
proof-    
  have "liftgen S \<subseteq> carrier (freegroup S)" 
    by (simp add: freegroup_def liftgen_subset_quotient)
  hence h_in:"h \<in> (liftgen S) \<rightarrow> carrier G" using assms(3) span_liftgen
    using hom_in_carrier by fastforce
  hence h_eq:"\<forall>y\<in>carrier (freegroup S). genmapext_lift (\<iota> ` S) (unlift h S (liftgen S)) y = h y"
    using assms genmapext_unlift_uni by blast
  moreover have liftgen_inv:"\<forall>x \<in> (liftgen S). \<exists>y \<in> S. x = (reln_tuple \<langle>S\<rangle> `` {\<iota>  y})"
  proof
    fix x
    assume x:"x \<in> liftgen S"
    then obtain  y' where y':"y' \<in> \<iota> ` S" "x = reln_tuple \<langle>S\<rangle> ``{y'}" unfolding liftgen_def by blast
    then obtain y where "y \<in> S" "y' = \<iota> y" by auto
    thus "\<exists>y\<in>S. x = reln_tuple \<langle>S\<rangle> `` {\<iota> y}" using y' by auto
  qed
  {fix x
   assume asm:"x \<in> (liftgen S)"
   then obtain y where y:"y \<in> S" "x = (reln_tuple \<langle>S\<rangle> `` {\<iota>  y})" using liftgen_inv by meson
   then have "f y = h x" using assms by auto
   moreover have "f y =g x" using assms y by auto 
   ultimately have "h x = g x" by auto}
  then have "\<forall>x \<in> (liftgen S). h x = g x" by auto
  then have "\<forall>y\<in>carrier (freegroup S). genmapext_lift (\<iota> ` S) (unlift h S (liftgen S)) y = g y"
    using h_in genmapext_unlift_uni 
    using assms(4) by blast
  with h_eq have "\<forall>y\<in>carrier (freegroup S). h y = g y" by fastforce
  then show ?thesis by blast
qed

lemma  inv_extn_to_carrier:
 assumes "group G" 
 and "(\<langle>S\<rangle>\<^bsub>G\<^esub>) = carrier G"
 and  "h \<in> hom G (freegroup S')"
 and  "g \<in> hom (freegroup S') G"
 and "\<forall> x \<in> S. g (h x) = x"
 shows "\<forall> x \<in> carrier G. g (h x) = x"
proof
  fix x
  assume "x \<in> carrier G"
  hence x_in:"x \<in> (\<langle>S\<rangle>\<^bsub>G\<^esub>)" using assms by auto
  have comp_hom:"g \<circ> h \<in> hom G G" using assms 
    using Group.hom_compose by blast
  have "g (h x) = x" using x_in
  proof(induction rule:gen_span.induct)
    case gen_one
    then show ?case using x_in comp_hom hom_one[OF comp_hom assms(1) assms(1)] by force
  next
    case (gen_gens x)
    then show ?case using assms(5) by metis 
  next
    case (gen_inv x)
    show ?case using assms(1,2,3,4) gen_inv 
      by (metis comp_def comp_hom group.int_pow_1 group.int_pow_neg hom_int_pow)
  next
    case (gen_mult x y)
    then show ?case  using assms gen_mult.IH(1) gen_mult.IH(2) gen_mult.hyps(1) gen_mult.hyps(2) hom_mult comp_hom
      by (smt (verit, ccfv_SIG) hom_in_carrier)     
  qed
  then show "g (h x) = x" by blast
qed

lemma surj_gen_implies_epi:
  assumes "h \<in> hom G H"
   and "carrier H = \<langle>S\<rangle>\<^bsub>H\<^esub>"
   and "group G"
   and "group H"
   and "S \<subseteq> h ` (carrier G)"
 shows "h \<in> epi G H" 
proof-
  {fix x
  assume x_in:"x \<in> carrier H"
  hence "x \<in> h ` (carrier G)" unfolding assms(2)
  proof(induction x rule:gen_span.induct)
    case gen_one
    then show ?case using assms 
      by (smt (verit, ccfv_SIG) antisym_conv gen_span.gen_one group.gen_span_closed group_hom.hom_span group_hom.intro group_hom_axioms.intro hom_carrier subset_image_iff)  
  next
    case (gen_gens x)
    then show ?case using assms(5) by blast
  next
    case (gen_inv x)
    then show ?case 
      by (smt (verit) assms(1) assms(3) assms(4) group.inv_equality group.l_inv_ex group_hom.hom_inv group_hom.intro group_hom_axioms.intro image_iff)  
  next
    case (gen_mult x y)
    then show ?case  
      by (smt (verit, ccfv_SIG) antisym_conv assms(1) assms(2) assms(3) assms(4) assms(5) group.gen_span_closed group.surj_const_mult group_hom.hom_span group_hom.intro group_hom_axioms.intro hom_carrier image_eqI subset_image_iff)  
  qed}
  hence "h ` carrier G = carrier H" using assms(1) 
    by (simp add: hom_carrier subsetI subset_antisym)
  thus ?thesis using assms(1) unfolding epi_def by blast 
qed


text\<open>The following lemma states that a group G generated by a set S, satisfies
 the property that given any map f from S to a monoid of type ((unit \<times> 'a) \<times> bool) list set,
it extends to a homomorphism from G to H, then G is isomorphic to a freegroup\<close>

lemma (in group) exist_of_hom_implies_freegroup: fixes S::"'a set"
  assumes "group G"
    and "(\<langle>S\<rangle>\<^bsub>G\<^esub>) = carrier G"
    and "\<And>(H::((unit \<times> 'a) \<times> bool) list set monoid).
          \<And>f. (group H) 
           \<and> (f  \<in> S \<rightarrow> (carrier H)) \<longrightarrow> (\<exists>h \<in> hom G H. (\<forall> x \<in> S. h x = f x))"
  shows "\<exists>(S_H::(unit \<times> 'a) set). G \<cong> (freegroup S_H)" using assms
proof-
  define S_H where "(S_H::(unit, 'a) monoidgentype set) = ({()::unit}) \<times> S"
  define f' where "f' = (\<lambda>(x::'a). ((()::unit), x))"
  define f where "f = (\<lambda> (x::'a). (reln_tuple \<langle>S_H\<rangle> `` {\<iota>  (f' x)}))"
  hence bij:"bij_betw f' S S_H" unfolding bij_betw_def inj_on_def S_H_def f'_def by blast
  define Gs where "Gs = freegroup S_H"
  hence group_G:"group Gs" 
    by (simp add: freegroup_is_group)
  moreover have f_to_carrier:"f \<in> S \<rightarrow> carrier Gs"
    unfolding f_def S_H_def Gs_def f'_def
  proof
    fix x
    assume "x \<in> S"
    hence "f' x \<in> S_H" using bij 
      using bij_betwE by auto
    thus " reln_tuple \<langle>{()} \<times> S\<rangle> `` {\<iota> ((), x)} \<in> carrier F\<^bsub>{()} \<times> S\<^esub> " unfolding f'_def S_H_def 
      by (metis (no_types, lifting) freegroup_def inclusion_subset_spanset insert_image insert_subset partial_object.simps(1) quotientI)
  qed
  then obtain h where h:"h \<in> hom G Gs" "\<forall>x \<in> S. h x = f x" using assms(3)[of Gs] 
    by (metis group_G)  
  have mod_assms2: "carrier G = \<langle>S\<rangle>\<^bsub>G\<^esub>" using assms by blast
  have h_epi:"h \<in> epi G Gs" 
  proof-
   have carr_eq:"carrier Gs = \<langle>liftgen S_H\<rangle>\<^bsub>(freegroup S_H)\<^esub>" using Gs_def 
         by (simp add: liftgen_span span_liftgen subset_antisym)
   moreover have "f ` S = liftgen S_H" unfolding liftgen_def S_H_def f_def f'_def
         by blast
   moreover have "f ` S = h ` S" using h(2) by simp
   ultimately have "(liftgen S_H) \<subseteq> h ` (carrier G)" using assms 
         by (metis gen_span.gen_gens subsetI subset_image_iff)
   hence "h \<in> epi G Gs"  using surj_gen_implies_epi[OF h(1) ] unfolding Gs_def
         using  carr_eq freegroup_is_group assms(1) 
         by (metis Gs_def)
   thus ?thesis unfolding epi_def by blast
  qed
  have inv_exists:"(inv_into S f') \<in> S_H \<rightarrow> carrier G" using  f_def f_to_carrier bij_betw_inv_into[OF bij] 
    by (metis (no_types, lifting) Pi_I assms(2) bij_betw_imp_funcset funcset_mem gen_span.gen_gens)
  then obtain g where g:"g \<in> hom Gs G" "\<forall> x \<in> S_H. (inv_into S f') x = g (reln_tuple \<langle>S_H\<rangle> `` {\<iota>  x})" 
    using bij exists_hom[OF assms(1) inv_exists]  Gs_def by auto
  then have "\<forall> x \<in> S. g (h x) = x" using h 
    by (metis bij bij_betw_apply bij_betw_inv_into_left f_def) 
  then have "\<forall>x \<in> carrier G. g (h x) = x" using inv_extn_to_carrier[OF assms(1,2)] h(1) g(1)
    unfolding Gs_def by fast
  hence "g \<circ> h \<in> iso G G" by auto
  hence "h \<in> Group.iso G Gs \<and> g \<in> Group.iso Gs G" using epi_iso_compose_rev[OF h_epi g(1)] 
       iso_def by blast
  thus ?thesis using is_isoI unfolding Gs_def by blast
qed


text \<open>this provides a sufficient condition for isomorphism to a free group\<close>
lemma (in group) exist_of_hom_implies_freegroup': fixes S::"'a set"
  assumes "group G"
    and "(\<langle>S\<rangle>\<^bsub>G\<^esub>) = carrier G"
    and "\<And>(H::((unit \<times> 'a) \<times> bool) list set monoid).
          \<And>f. (group H) 
           \<and> (f  \<in> S \<rightarrow> (carrier H)) \<longrightarrow> (\<exists>h \<in> hom G H. (\<forall> x \<in> S. h x = f x))"
  shows "is_freegroup G"
  using exist_of_hom_implies_freegroup[OF assms] unfolding is_freegroup_def by argo



end
