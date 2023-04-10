theory FreeGroupMain
imports Main "HOL-Algebra.Group"
begin

type_synonym ('a,'b) monoidgentype = "'a \<times> 'b"


type_synonym ('a,'b) groupgentype = "('a,'b) monoidgentype \<times> bool"

text \<open>Words are defined as lists over groupgentype\<close>
type_synonym ('a,'b) word = "(('a,'b) groupgentype) list"

text \<open>We define the inverse of a groupgentype element\<close>
fun inverse::"('a,'b) groupgentype \<Rightarrow> ('a,'b) groupgentype"
  where
"inverse (x, True) = (x, False)"
|"inverse (x, False) = (x, True)"

lemma inverse_of_inverse:
  assumes "g = inverse h"
  shows "h = inverse g"
  using assms inverse.simps 
  by (metis inverse.elims)

definition invgen ::  "('a,'b) monoidgentype set \<Rightarrow> ('a,'b) groupgentype set" ("_\<^sup>\<plusminus>")
  where
"S \<^sup>\<plusminus> = S \<times> {True,False}"

text \<open>Following definitions define the set of words in the span of a set\<close>
inductive_set words_on::"('a,'b) groupgentype set \<Rightarrow> ('a,'b) word set" ("_\<^sup>\<star>")
  for S::"('a,'b) groupgentype set"
  where
empty:"[] \<in> (S\<^sup>\<star>)"
|gen:"x \<in> S \<Longrightarrow> xs \<in> (S\<^sup>\<star>) \<Longrightarrow> (x#xs) \<in> (S\<^sup>\<star>)"

definition freewords_on::"('a,'b) monoidgentype set \<Rightarrow> ('a,'b) word set" ("\<langle>_\<rangle>")
  where
"\<langle>S\<rangle>  = words_on (invgen S)"

text\<open>Some lemmas about words on a set.\<close>

lemma cons_span: 
  assumes "(x#xs) \<in> (words_on S)" 
    shows "[x] \<in> (words_on S)"
proof(induction xs)
  case Nil
  then show ?case using assms words_on.cases words_on.empty words_on.gen
    by (metis list.distinct(1) list.sel(1))
next
  case (Cons y xs)
  then show ?case  by auto
qed

lemma span_append:
  assumes "xs \<in> (words_on S)" "ys \<in> (words_on S)" 
    shows "(xs@ys) \<in> (words_on S)"
    using assms
proof(induction xs)
  case empty
  then show ?case by simp
next
  case (gen x)
  then show ?case using  words_on.gen  by (metis Cons_eq_appendI)
qed

lemma span_cons:
  assumes "(x#xs) \<in> (words_on S)" 
  shows "xs \<in> (words_on S)"
  using assms
proof(induction xs)
  case Nil
  then show ?case  by (simp add: words_on.empty)
next
  case (Cons a xs)
  then show ?case  using words_on.cases  words_on.gen  by blast
qed

lemma leftappend_span: 
  assumes "(xs@ys) \<in> (words_on S)" shows "xs \<in> (words_on S)"
  using assms
proof(induction xs)
  case Nil
  then show ?case using words_on.empty by simp
next
  case (Cons a1 a2)
  then have 1: "(a1#(a2 @ ys)) \<in> (words_on S)" by auto
  then have 2:"[a1] \<in> (words_on S)" using cons_span by blast
  have "(a2 @ ys) \<in> (words_on S)" using span_cons Cons 1 by blast
  then have "a2 \<in> (words_on S)" using Cons by simp
  moreover have "(a1#a2)  = [a1] @ a2" by simp
  ultimately show ?case using 1 2 span_append  by metis 
qed

lemma rightappend_span: 
  assumes "(xs@ys) \<in> (words_on S)" 
    shows "ys \<in>  (words_on S)"
    using assms
proof(induction xs)
case Nil
  then show ?case using empty by simp
next
  case (Cons a1 a2)
 then have 1: "(a1#(a2 @ ys)) \<in> (words_on S)" by auto
  then have 2:"[a1] \<in> (words_on S)" using cons_span by blast
  have "(a2 @ ys) \<in> (words_on S)" using span_cons Cons 1 by blast
  then show ?case using Cons by blast
qed

lemma span_inverse: 
  assumes "x \<in> invgen S" 
    shows "inverse x \<in> invgen S"
proof-
  let ?g = "fst x"
  let ?b = "snd x"
  have x: "x = (?g, ?b)" by simp
  have g:"?g \<in> S"using assms invgen_def by (metis eq_fst_iff mem_Sigma_iff)
  show ?thesis
  proof(cases "?b = False")
    case True
    have "(?g, True) \<in> invgen  S" using g by (simp add: invgen_def)
    then show ?thesis using True inverse.simps(2) x by metis
  next
    case False
    have "(?g, False) \<in> invgen  S" using g by (simp add: invgen_def)
    then show ?thesis using False inverse.simps(1) x  by metis
  qed
qed

text \<open>wordinverse xs recursively defines the reverse of a word with its elements
      mapped to their inverses, and will be used to define the inverses of elements
      of a free group.\<close>


primrec wordinverse::"('a,'b) word \<Rightarrow> ('a, 'b) word"
  where
"wordinverse [] = []"
|"wordinverse (x#xs) =  (wordinverse xs)@[inverse x]"

text \<open>Alternate definitions of wordinverse (defined using rev and map) which might
       be more convenient in some circumstances.\<close>

lemma wordinverse_redef1: 
  "wordinverse xs = rev (map inverse xs)"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have 1:"wordinverse (a#xs) = wordinverse xs @ [inverse a]" by auto
  have "rev (map inverse (a#xs)) = rev((inverse a#( map inverse xs)))" by simp
  then have 2: "rev (map inverse (a#xs)) = rev (map inverse (xs)) @ [inverse a]" by simp
  then show ?case using 1 2 Cons.IH by simp
qed

lemma wordinverse_redef2: 
  "wordinverse xs = map inverse (rev xs)"
proof(induction xs)
case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have 1:"wordinverse (a#xs) = wordinverse xs @ [inverse a]" by auto
  have "map inverse (rev (a#xs)) = map inverse (rev xs @ [a])"  by simp
  then have 2: "map inverse (rev (a#xs)) = map inverse (rev xs) @ [inverse a]"  by simp
  then show ?case using 1 2 Cons.IH by auto
qed

text \<open>Some lemmas about wordinverse.\<close>

lemma span_wordinverse: 
  assumes "xs \<in> \<langle>S\<rangle>" 
    shows "wordinverse xs \<in> \<langle>S\<rangle>"
    using assms unfolding freewords_on_def
proof(induction xs)
  case empty
  then show ?case by (simp add: words_on.empty)
next
  case (gen x xs)
  then have "inverse x \<in> invgen  S"  by (simp add: span_inverse)
  then have "[inverse x] \<in> (words_on (invgen S))" using words_on.empty words_on.gen by blast
  then have "wordinverse xs @ [inverse x] \<in> (words_on (invgen S))" using gen span_append by auto
  moreover have "wordinverse (x#xs) = wordinverse xs @ [inverse x]" by simp
  ultimately show ?case  by simp
qed

lemma wordinverse_append: 
  "(wordinverse xs) @ (wordinverse ys) = (wordinverse (ys@xs))"
proof(induction ys)
  case Nil
  have "wordinverse [] = []" by simp
  then show ?case by simp
next
  case (Cons a y)
  have "(wordinverse xs) @ (wordinverse (a # y)) = (wordinverse xs) @ (wordinverse y) @ [inverse a]" by simp
  moreover have "(wordinverse ((a#y)@xs)) = (wordinverse (y@xs)) @ [inverse a]" by simp
  ultimately show ?case using "Cons.IH" by simp
qed

lemma wordinverse_of_wordinverse:  
    "wordinverse (wordinverse xs) = xs" 
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  have 1: "wordinverse (a#xs) = (wordinverse xs) @ [inverse a]" by auto
  have "wordinverse [inverse a] = [a]" using inverse_of_inverse 
    by (metis append_Nil list.simps(8) list.simps(9) rev.simps(1) rev.simps(2) wordinverse_redef2)
  then have 2:"wordinverse ((wordinverse xs) @ [inverse a]) = [a] @ wordinverse (wordinverse xs)" using wordinverse_append by metis
  then have "[a] @ wordinverse (wordinverse xs) = [a] @ xs" using Cons by auto
  moreover have "[a] @ xs = (a#xs)" by simp
  ultimately show ?case using 1 2 by simp
qed

lemma wordinverse_symm:
  assumes "wordinverse xs = ys" 
    shows "xs = wordinverse ys"
proof-
  have "wordinverse (wordinverse xs) = wordinverse ys"  using assms by auto
  then show ?thesis using wordinverse_of_wordinverse by metis
qed

text\<open>reduced words are words where no element and its inverse occur ext to each 
      other.\<close>

fun reduced::"('a,'b) word \<Rightarrow> bool"
  where
"reduced [] = True"
|"reduced [x] = True"
|"reduced (x#y#xs) = (if (x \<noteq> inverse y) then reduced (y#xs) else False)"

text\<open>reln\<close>

inductive reln::"('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool" (infixr "~" 65)
  where
refl[intro!]: "xs ~ xs" |
sym: "xs ~ ys \<Longrightarrow> ys ~ xs" |
trans: "xs ~ ys \<Longrightarrow> ys ~ zs \<Longrightarrow> xs ~ zs" |
base: "[x, inverse x] ~ []" |
mult: "xs ~ xs' \<Longrightarrow> ys ~ ys' \<Longrightarrow> (xs@ys) ~ (xs'@ys')"

definition reln_tuple :: "(('a,'b) word) set \<Rightarrow>(('a,'b) word \<times> ('a,'b) word) set"
  where
"reln_tuple S = {(xs,ys).xs~ys \<and> xs \<in> S \<and> ys \<in> S}" 

lemma wordinverse_inverse: 
  "(xs @ (wordinverse xs)) ~ []"
proof(induction xs)
  case Nil
  have "[] = []" by simp
  then show ?case by (simp add: reln.refl)
next
  case (Cons a xs)
  have "wordinverse (a#xs) = (wordinverse xs) @ [inverse a]"  by simp
  moreover have "(a#xs) = [a] @ xs" by simp
  ultimately have 1: "((a # xs) @ wordinverse (a # xs)) = [a] @ xs @ (wordinverse xs) @  [inverse a]" by (metis append_assoc)
  have "([a] @ xs @ (wordinverse xs)) ~ [a] @ []"  using Cons.IH mult by blast
  then have "([a] @ xs @ (wordinverse xs)) ~ [a]"  by auto
  moreover have "[inverse a] ~ [inverse a]" by (simp add: reln.refl)
  ultimately have "([a] @ xs @ (wordinverse xs) @  [inverse a]) ~ [a] @ [inverse a]" using mult by (metis append_assoc)
  then have "([a] @ xs @ (wordinverse xs) @  [inverse a]) ~ []" by (simp add: base reln.trans)
  then show ?case using 1 by auto
qed

lemma inverse_wordinverse: 
  "((wordinverse xs) @  xs) ~ []"
proof-
  let ?ys = "wordinverse xs"
  have "(wordinverse ?ys = xs)" sledgehammer
    by (metis wordinverse_symm) 
  moreover have "(?ys @ wordinverse ?ys) ~ []" using wordinverse_inverse by blast
  ultimately show ?thesis using wordinverse_of_wordinverse by simp
qed

lemma reln_refl: 
  "refl_on \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)"
proof-
  have "(\<And>xys. xys \<in> (reln_tuple \<langle>S\<rangle>) \<Longrightarrow> xys \<in> \<langle>S\<rangle> \<times> \<langle>S\<rangle>)"
  proof-
    fix xys assume 1: "xys \<in> (reln_tuple \<langle>S\<rangle>)"
    let ?a = "(fst xys)"
    let ?b = "(snd xys)"
    have "(?a, ?b) \<in> (reln_tuple \<langle>S\<rangle>)" by (simp add: "1")
    then have "(?a, ?b) \<in> \<langle>S\<rangle> \<times> \<langle>S\<rangle>" using reln_tuple_def by (metis (no_types, lifting) Product_Type.Collect_case_prodD SigmaI prod.collapse)
    then show "xys \<in> \<langle>S\<rangle> \<times> \<langle>S\<rangle>" by simp
  qed
  then have A:"reln_tuple \<langle>S\<rangle> \<subseteq> \<langle>S\<rangle> \<times> \<langle>S\<rangle>" by (simp add: subsetI)
  have "(\<And>xs. xs\<in>\<langle>S\<rangle> \<Longrightarrow> (xs, xs) \<in> reln_tuple \<langle>S\<rangle>)"
  proof-
    fix xs assume "xs\<in>\<langle>S\<rangle>"
    moreover have "xs ~ xs" by (simp add: reln.refl)
    ultimately show "(xs, xs) \<in> reln_tuple \<langle>S\<rangle>" by (simp add: reln_tuple_def)
  qed
  then have "(\<forall>xs\<in>\<langle>S\<rangle>. (xs, xs) \<in> reln_tuple \<langle>S\<rangle>)" by simp
  then show ?thesis using A unfolding refl_on_def  by simp
qed

lemma reln_sym: 
  "sym (reln_tuple \<langle>S\<rangle>)"
proof-
  have "(\<And>xs ys. (xs, ys) \<in> (reln_tuple \<langle>S\<rangle>) \<Longrightarrow> (ys, xs) \<in> (reln_tuple \<langle>S\<rangle>))"
  proof- 
    fix xs ys assume 1:"(xs,ys)\<in>(reln_tuple \<langle>S\<rangle>)"
    then have 2:"xs ~ ys" using reln_tuple_def 1 by (metis (no_types, lifting) case_prodD mem_Collect_eq)
    then have "ys ~ xs" by (simp add: 2 reln.sym)
    then show "(ys, xs) \<in> reln_tuple \<langle>S\<rangle>" 
      using 1 by (simp add: reln_tuple_def)
  qed
  then have "(\<forall>xs ys. (xs, ys) \<in> (reln_tuple \<langle>S\<rangle>) \<longrightarrow> (ys, xs) \<in> (reln_tuple \<langle>S\<rangle>))" by simp
  then show ?thesis unfolding sym_def  by simp
qed

lemma reln_trans: 
  "trans (reln_tuple \<langle>S\<rangle>)"
proof-
  have "(\<And>xs ys zs. (xs, ys) \<in> (reln_tuple \<langle>S\<rangle>) \<Longrightarrow> (ys, zs) \<in> (reln_tuple \<langle>S\<rangle>) \<Longrightarrow> (xs, zs) \<in> (reln_tuple \<langle>S\<rangle>))"
  proof-
    fix xs ys zs assume 1:"(xs,ys)\<in>(reln_tuple \<langle>S\<rangle>)" assume 2: "(ys, zs) \<in> (reln_tuple \<langle>S\<rangle>)"
    have "xs ~ ys" using reln_tuple_def 1 by (metis (no_types, lifting) case_prodD mem_Collect_eq)
    moreover have "ys ~ zs" using reln_tuple_def 2 by (metis (no_types, lifting) case_prodD mem_Collect_eq)
    ultimately have "xs ~ zs" using reln.trans by auto
    then show "(xs, zs) \<in> reln_tuple \<langle>S\<rangle>" using 1 2 by (simp add: reln_tuple_def)
  qed
  then have "(\<forall>xs ys zs. (xs, ys) \<in> (reln_tuple \<langle>S\<rangle>) \<longrightarrow> (ys, zs) \<in> (reln_tuple \<langle>S\<rangle>) \<longrightarrow> (xs, zs) \<in> (reln_tuple \<langle>S\<rangle>))" by simp
  then show ?thesis unfolding trans_def by simp
qed

lemma reln_equiv: 
  "equiv \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)"
  by (simp add: equivI reln_refl reln_sym reln_trans)

text\<open>The following Congruence and projected functions and the subsequent results,
Congruent2 and ProjFun2 are adapted from IsarMathLib. Original formalisations are
 available on https://isarmathlib.org/EquivClass1.html.\<close>

definition Congruent2 :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool"
  where
"Congruent2 r f \<longleftrightarrow> (\<forall> x1 x2 y1 y2. (x1, x2) \<in> r \<and> (y1, y2) \<in> r 
                                  \<longrightarrow> (f x1 y1, f x2 y2)  \<in> r)"

lemma append_congruent: 
  "Congruent2 (reln_tuple \<langle>S\<rangle>) (@)"
proof-
  have "\<And>x1 x2 y1 y2. \<lbrakk>(x1, x2) \<in> reln_tuple \<langle>S\<rangle> ; (y1, y2) \<in> reln_tuple \<langle>S\<rangle>\<rbrakk> \<Longrightarrow> (x1 @ y1, x2 @ y2) \<in> reln_tuple \<langle>S\<rangle>"
  proof-
    fix x1 x2 y1 y2 assume 1:"(x1, x2) \<in> (reln_tuple \<langle>S\<rangle>)" "(y1, y2) \<in> (reln_tuple \<langle>S\<rangle>)"
  have "x1 \<in>  \<langle>S\<rangle> \<and> x2 \<in> \<langle>S\<rangle>" using 1 reln_tuple_def by auto
  moreover have "y1 \<in>  \<langle>S\<rangle> \<and> y2 \<in> \<langle>S\<rangle>" using 1 reln_tuple_def by auto
  ultimately have A:"(x1@y1) \<in>  \<langle>S\<rangle> \<and> (x2@y2) \<in> \<langle>S\<rangle>" unfolding freewords_on_def by (simp add: span_append)
  have "x1 ~ x2" using 1 reln_tuple_def by auto
  moreover have "y1 ~ y2" using 1 reln_tuple_def by auto
  ultimately have "(x1@y1) ~ (x2@y2)" using mult by auto
  then show "((x1@y1) , (x2@y2)) \<in> (reln_tuple \<langle>S\<rangle>)" using A reln_tuple_def by auto
qed
  thus ?thesis  using Congruent2_def by blast
qed

definition ProjFun2 :: "('a\<times>'a) set \<Rightarrow> ('a\<Rightarrow>'a \<Rightarrow>'a) \<Rightarrow>
                   ('a set \<Rightarrow> 'a set \<Rightarrow> 'a set) " where
"ProjFun2 r f =  (\<lambda>p q. (\<Union>x\<in>(p\<times>q) .r `` {f (fst x) (snd x)}))"

lemma equiv_2f_con: 
  assumes "equiv A r"  
      and "Congruent2 r f" 
      and "C1\<in>A//r" "C2\<in>A//r" 
      and "y1\<in>C1" "z1\<in>C1" "y2\<in>C2" "z2\<in>C2"
    shows "r `` {(f y1 y2)} = r `` {(f z1 z2)}"
proof-
  have "(y1, z1) \<in> r" by (meson assms(1) assms(3) assms(5) assms(6) quotient_eq_iff)
  moreover have "(y2, z2) \<in> r" by (meson assms(1) assms(4) assms(7) assms(8) quotient_eq_iff)
  ultimately have "((f y1 y2),(f z1 z2)) \<in> r"  using Congruent2_def assms(2) by fastforce
  then show ?thesis  by (meson assms(1) equiv_class_eq)
qed

lemma equiv_2f_clos: 
  assumes "equiv A r"  
      and "Congruent2 r f" "C1\<in>A//r"  "C2\<in>A//r"  "y1\<in>C1"  "y2\<in>C2"
    shows "(f y1 y2) \<in> A"
proof-
  have y:"y1 \<in> A" using Union_quotient assms(1) assms(3) assms(5) by auto
  have z:"y2 \<in> A" using Union_quotient assms(1) assms(4) assms(6) by auto
  have yy: "(y1,y1) \<in> r" by (metis assms(1) assms(3) assms(5) quotient_eq_iff)
  have zz:  "(y2,y2) \<in> r" by (metis assms(1) assms(4) assms(6) quotient_eq_iff)
  have "(f y1 y2, f y1 y2) \<in> r" using yy zz using Congruent2_def assms(2) by fastforce
  then show ?thesis by (metis assms(1) equiv_class_eq_iff)
qed

lemma union_eq_2f_in:
  assumes "C1\<times>C2\<noteq>{}"  
      and "\<forall>x\<in>C1\<times>C2. r``{ (b (fst x) (snd x))}\<in>A//r"  
      and "\<forall>x y. x\<in>C1\<times>C2\<and>y\<in>C1\<times>C2\<longrightarrow> r``{(b (fst x) (snd x))}= r``{(b (fst y) (snd y))}" 
    shows "(\<Union>x\<in>C1\<times>C2. r``{(b (fst x) (snd x))} )\<in>A//r"
proof-
  obtain x where A:"x\<in>C1\<times>C2" using assms(1) by auto
  then have "\<forall>y\<in>C1\<times>C2. r``{(b (fst x) (snd x))}= r``{(b (fst y) (snd y))}" using assms(3) by blast
  then have "(\<Union>y\<in>C1\<times>C2. r``{(b (fst y) (snd y))}) = r``{(b (fst x) (snd x))}"  using assms(1) by blast
    then show ?thesis using A  by (simp add: assms(2))
  qed

lemma proj2fun_clos:
  assumes "equiv A r"  
      and "Congruent2 r f" 
      and "C1\<in>A//r" "C2\<in>A//r"
    shows "((ProjFun2  r f) C1 C2) \<in> A//r"
proof-
  have "\<And>z. z\<in>C1\<times>C2 \<Longrightarrow> f (fst z) (snd z)\<in>A" 
  proof-
    fix z assume z: "z\<in>C1\<times>C2"
    show "f (fst z) (snd z) \<in> A" using equiv_2f_clos using assms(1) assms(2) assms(3) assms(4) z by fastforce
  qed
  then have "\<forall>z\<in>C1\<times>C2. f (fst z) (snd z)\<in>A" by simp
  then have "\<forall>z\<in>C1\<times>C2. r``{f (fst z) (snd z)}\<in>A//r" by (simp add: quotientI)
  moreover have "\<forall>z1 z2. z1\<in>C1\<times>C2\<and>z2\<in>C1\<times>C2\<longrightarrow>  r ``{f (fst(z1)) (snd(z1))} = r `` {f (fst(z2)) (snd(z2))}"
  proof-
    have "\<And>z1 z2. z1\<in>C1\<times>C2\<and>z2\<in>C1\<times>C2 \<Longrightarrow>  r ``{f (fst(z1)) (snd(z1))} = r `` {f (fst(z2)) (snd(z2))}"
    proof-
      fix z1 z2 assume 1:"z1\<in>C1\<times>C2\<and>z2\<in>C1\<times>C2"
      have 2:"(fst(z1)) \<in>C1" using 1 by auto
      have 3:"(fst(z2)) \<in>C1" using 1 by auto
      have 4:"(snd(z1)) \<in>C2" using 1 by auto
      have 5:"(snd(z2)) \<in>C2" using 1 by auto
      show " r ``{f (fst(z1)) (snd(z1))} = r `` {f (fst(z2)) (snd(z2))}" using equiv_2f_con[of "A" "r" "f" "C1" "C2" "(fst(z1))" "(fst(z2))" "(snd(z1))" "(snd(z2))"]   1 2 3 4 5  assms(1) assms(2) assms(3) assms(4) by simp
    qed
    then show ?thesis by simp
  qed
  moreover have "C1\<times>C2\<noteq>{}"  using assms(1) assms(3) assms(4) in_quotient_imp_non_empty by auto
  ultimately have "(\<Union>x\<in>C1\<times>C2. r``{(f (fst x) (snd x))} )\<in>A//r" using union_eq_2f_in[of "C1" "C2" "r" "f" "A"] by fastforce
  then show ?thesis unfolding ProjFun2_def by auto
qed

lemma union_eq_2f_eq: 
  assumes "C1\<times>C2\<noteq>{}"  
      and "\<forall>x\<in>C1\<times>C2. r``{ (b (fst x) (snd x))} = X" 
    shows "(\<Union>y\<in>C1\<times>C2 .r``{ (b (fst y) (snd y))})=X"
    by (metis (no_types, lifting) SUP_eq_const assms(1) assms(2))

lemma equiv_2f_wd:
  assumes "equiv A r" 
      and "Congruent2 r f"  
      and "x\<in>A" "y\<in>A"
    shows "(ProjFun2  r f) (r``{x}) (r``{y}) = r ``{(f x y)}"
proof-
  have "(r``{x})\<times> (r``{y}) \<noteq> {}"  by (metis Sigma_empty_iff assms(1) assms(3) assms(4) equals0D equiv_class_self)
  moreover have "\<forall>z\<in>r``{x}\<times>r``{y}. r ``{f (fst z) (snd z)}=r ``{f x y}"
  proof-
    have "\<And>z. z \<in> r``{x}\<times>r``{y} \<Longrightarrow> r ``{f (fst z) (snd z)}=r ``{f x y}"
    proof-
      fix z assume 1:"z \<in> r``{x}\<times>r``{y}"
      have "(fst z) \<in> r``{x}" using 1 by auto
      moreover have  "(snd z) \<in> r``{y}" using 1 by auto
      moreover have "r``{x}\<in>A//r" by (simp add: assms(3) quotientI)
      moreover have "r``{y}\<in>A//r" by (simp add: assms(4) quotientI)
      moreover have "x\<in>r``{x}" using assms(1) assms(3) equiv_class_self by force
     moreover have "y \<in>r``{y}" using assms(1) assms(4) equiv_class_self by force
     ultimately show "r ``{f (fst z) (snd z)}=r ``{f x y}" using assms(1) assms(2)  equiv_2f_con[of "A" "r" "f" "r `` {x}" "r `` {y}" "(fst z)" "x" "(snd z)" "y"]   by fastforce
   qed
   then show ?thesis by simp
 qed
  ultimately have "(\<Union>z\<in>r``{x}\<times>r``{y}. r``{(f (fst z) (snd z))} ) = r ``{f x y}" using union_eq_2f_eq by simp
  then show ?thesis unfolding ProjFun2_def by simp
qed

lemma projfun2_assoc:
  assumes "equiv A r" 
      and "Congruent2 r f" 
      and "\<forall>x \<in> A. \<forall> y \<in> A. \<forall> z \<in> A. f x (f y z) = f (f x y) z" 
      and "C1\<in>A//r" "C2\<in>A//r" "C3\<in>A//r" 
      and "g=(ProjFun2 r f)" 
    shows "(g (g C1 C2) C3) = (g C1 (g C2 C3))"
proof-
  obtain x y z where A:"C1=r``{x} \<and> C2=r``{y} \<and>  C3=r``{z} \<and>  x\<in>A \<and>  y\<in>A \<and>  z\<in>A" by (meson assms(4) assms(5) assms(6) quotientE)
  moreover then have B: "(f x y) \<in> A \<and> (f y z)  \<in> A"  using assms(1) assms(2) assms(4) assms(5) assms(6) equiv_2f_clos equiv_class_self by fastforce
  ultimately have "g (g C1 C2) C3 = r``{f (f x y) z}" 
    using assms(1) assms(2) assms(7) equiv_2f_wd by fastforce
  moreover have "... = r``{f  x (f y z)}" by (simp add: A assms(3))
  moreover have "... = g  C1 (g C2 C3)" 
    using A B assms(1) assms(2) assms(7) equiv_2f_wd by fastforce
  ultimately show ?thesis by simp
qed

text \<open> The following definition defines product on the equivalence classes, by 
factoring concatenation through equivalence relations.\<close>
definition proj_append ::  "(('a,'b) word) set \<Rightarrow> (('a,'b) word) set \<Rightarrow> (('a,'b) word) set \<Rightarrow> (('a,'b) word) set"
  where
"proj_append S X Y =  (ProjFun2 (reln_tuple S) append) X Y"

lemma proj_append_clos: 
  assumes "C1\<in> quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" 
      and "C2\<in> quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)"
    shows "(proj_append \<langle>S\<rangle> C1 C2) \<in>  (quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>))"
proof-
  show ?thesis using assms(1) assms(2) reln_equiv[of "S"] append_congruent[of "S"] proj2fun_clos[of "\<langle>S\<rangle>" "(reln_tuple \<langle>S\<rangle>)" "append" "C1" "C2"] unfolding proj_append_def by fastforce
qed

lemma append_assoc2: 
  "\<forall>x \<in> A.\<forall>y \<in> A.\<forall>z \<in> A. append x (append y z) = append (append x y) z"
  by simp

lemma proj_append_assoc: 
  assumes "C1\<in>quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" 
      and "C2\<in>quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" 
      and "C3\<in>quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" 
    shows "(proj_append \<langle>S\<rangle> C1 (proj_append \<langle>S\<rangle> C2 C3)) = (proj_append \<langle>S\<rangle> (proj_append \<langle>S\<rangle> C1 C2) C3)"
proof-
  show ?thesis using assms reln_equiv[of "S"] append_congruent[of "S"] append_assoc2[of "\<langle>S\<rangle>"] projfun2_assoc[of "\<langle>S\<rangle>" "(reln_tuple \<langle>S\<rangle>)" "append" "C1" "C2" "C3"] unfolding proj_append_def by simp
qed

lemma proj_append_wd: 
  assumes "xs \<in> \<langle>S\<rangle>" "ys \<in> \<langle>S\<rangle>" 
    shows "(proj_append \<langle>S\<rangle> ((reln_tuple \<langle>S\<rangle>)``{xs}) ((reln_tuple \<langle>S\<rangle>)``{ys})) = (reln_tuple \<langle>S\<rangle>) `` {append xs ys}"
proof-
  show ?thesis 
    using reln_equiv[of "S"] append_congruent[of "S"] assms equiv_2f_wd[of "\<langle>S\<rangle>" "(reln_tuple \<langle>S\<rangle>)" "append" "xs" "ys"] unfolding proj_append_def  by simp
qed

text\<open>Free group is defined as follows. We prove below that it satsifies the group 
axioms.\<close>
definition freegroup :: "('a,'b) monoidgentype set \<Rightarrow> (('a,'b) word set) monoid" ("F\<index>")
  where
"freegroup S \<equiv> \<lparr>
     carrier =  quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>),
     mult = proj_append \<langle>S\<rangle>,
     one = (reln_tuple \<langle>S\<rangle>) `` {[]}
  \<rparr>"


theorem freegroup_is_group: 
  "group (freegroup S)"
proof
  fix X Y
  assume "X \<in> carrier (freegroup S)" hence x: "X \<in>(quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>))" by(auto simp add:freegroup_def) 
  assume "Y \<in> carrier (freegroup S)" hence y: "Y \<in> (quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>))" by(auto simp add:freegroup_def)
  from x and y
  have "X \<otimes>\<^bsub>freegroup S\<^esub> Y \<in> (quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>))" by (simp add: freegroup_def proj_append_clos)
  thus "X \<otimes>\<^bsub>freegroup S\<^esub> Y \<in> carrier (freegroup S)"
    by (auto simp add:freegroup_def)
next
  fix X Y Z assume x:"X \<in> carrier (freegroup S)" assume y: "Y \<in> carrier (freegroup S)" assume z: "Z \<in> carrier (freegroup S)"
  from x and y and z
  show  "X \<otimes>\<^bsub>freegroup S\<^esub> Y \<otimes>\<^bsub>freegroup S\<^esub> Z = X \<otimes>\<^bsub>freegroup S\<^esub> (Y \<otimes>\<^bsub>freegroup S\<^esub> Z)" by (simp add: freegroup_def proj_append_assoc)
next
  have "[] \<in> \<langle>S\<rangle>" unfolding freewords_on_def using empty by auto
  then have "(reln_tuple \<langle>S\<rangle>) `` {[]} \<in> quotient \<langle>S\<rangle> (reln_tuple \<langle>S\<rangle>)" by (simp add: quotientI)
  then show "\<one>\<^bsub>freegroup S\<^esub> \<in> carrier (freegroup S)"  by (auto simp add:freegroup_def)
next
  fix X assume "X \<in> carrier (freegroup S)"
  moreover then obtain x1 where x:"(reln_tuple \<langle>S\<rangle>)``{x1} = X" by (metis freegroup_def partial_object.select_convs(1) quotientE)
  ultimately have "x1 \<in> \<langle>S\<rangle>"   by (metis freegroup_def partial_object.select_convs(1) proj_def proj_in_iff reln_equiv)
  moreover have "[] \<in> \<langle>S\<rangle>" using empty freewords_on_def by auto
  ultimately have "proj_append \<langle>S\<rangle> ((reln_tuple \<langle>S\<rangle>) `` {[]}) ((reln_tuple \<langle>S\<rangle>)``{x1}) = ((reln_tuple \<langle>S\<rangle>)``{x1})" by (simp add: proj_append_wd)
  then show "\<one>\<^bsub>freegroup S\<^esub> \<otimes>\<^bsub>freegroup S\<^esub> X = X" using x by (simp add: freegroup_def)
next
 fix X assume "X \<in> carrier (freegroup S)"
  moreover then obtain x1 where x:"(reln_tuple \<langle>S\<rangle>)``{x1} = X" by (metis freegroup_def partial_object.select_convs(1) quotientE)
  ultimately have "x1 \<in> \<langle>S\<rangle>"   by (metis freegroup_def partial_object.select_convs(1) proj_def proj_in_iff reln_equiv)
  moreover have "[] \<in> \<langle>S\<rangle>" using empty freewords_on_def by auto
  ultimately have "proj_append \<langle>S\<rangle>  ((reln_tuple \<langle>S\<rangle>)``{x1}) ((reln_tuple \<langle>S\<rangle>) `` {[]}) = ((reln_tuple \<langle>S\<rangle>)``{x1})" by (simp add: proj_append_wd)
  then show "X \<otimes>\<^bsub>freegroup S\<^esub> \<one>\<^bsub>freegroup S\<^esub> = X" using x by (simp add: freegroup_def)
next
  show "carrier (freegroup S) \<subseteq> Units (freegroup S)"
  proof (simp add:freegroup_def Units_def, rule subsetI)
    fix X assume 1:"X \<in> \<langle>S\<rangle> // reln_tuple \<langle>S\<rangle>"
    moreover then obtain x1 where x:"(reln_tuple \<langle>S\<rangle>)``{x1} = X" by (metis quotientE)
    ultimately have x1:"x1 \<in> \<langle>S\<rangle>"  by (metis  proj_def proj_in_iff reln_equiv)
    then have ix1:"wordinverse x1 \<in> \<langle>S\<rangle>" 
      using span_wordinverse by auto 
    then have 2:"(reln_tuple \<langle>S\<rangle>)``{wordinverse x1} \<in> \<langle>S\<rangle> // reln_tuple \<langle>S\<rangle>" by (simp add: quotientI)
    have nil: "[] \<in> \<langle>S\<rangle>" using empty freewords_on_def by auto
    have "proj_append \<langle>S\<rangle> ((reln_tuple \<langle>S\<rangle>)``{x1}) ((reln_tuple \<langle>S\<rangle>)``{wordinverse x1}) 
        = reln_tuple \<langle>S\<rangle> `` {x1@(wordinverse x1)}" 
      using ix1 proj_append_wd x1 by blast
    moreover have "x1@(wordinverse x1) \<in> \<langle>S\<rangle>" using ix1 span_append freewords_on_def x1 by blast
    moreover then have "((x1@(wordinverse x1)), []) \<in> reln_tuple \<langle>S\<rangle>" using nil wordinverse_inverse reln_tuple_def by auto
    moreover then have "reln_tuple \<langle>S\<rangle> `` {x1@(wordinverse x1)} = reln_tuple \<langle>S\<rangle> `` {[]}" by (metis equiv_class_eq reln_equiv)
    ultimately have 3:"proj_append \<langle>S\<rangle> ((reln_tuple \<langle>S\<rangle>)``{x1}) ((reln_tuple \<langle>S\<rangle>)``{wordinverse x1}) = reln_tuple \<langle>S\<rangle> `` {[]}" by simp
    have "proj_append \<langle>S\<rangle>  ((reln_tuple \<langle>S\<rangle>)``{wordinverse x1}) ((reln_tuple \<langle>S\<rangle>)``{x1}) = reln_tuple \<langle>S\<rangle> `` {(wordinverse x1)@x1}" 
      using ix1 proj_append_wd x1 by blast
    moreover have "(wordinverse x1)@x1 \<in> \<langle>S\<rangle>" using ix1 span_append freewords_on_def x1 by blast
    moreover then have "(((wordinverse x1)@x1), []) \<in> reln_tuple \<langle>S\<rangle>" using nil inverse_wordinverse reln_tuple_def by auto
    moreover then have "reln_tuple \<langle>S\<rangle> `` {(wordinverse x1)@x1} = reln_tuple \<langle>S\<rangle> `` {[]}" by (metis equiv_class_eq reln_equiv)
    ultimately have 4:"proj_append \<langle>S\<rangle> ((reln_tuple \<langle>S\<rangle>)``{wordinverse x1}) ((reln_tuple \<langle>S\<rangle>)``{x1}) = reln_tuple \<langle>S\<rangle> `` {[]}" by simp
    show "X \<in> {y \<in> \<langle>S\<rangle> // reln_tuple \<langle>S\<rangle>.\<exists>x\<in>\<langle>S\<rangle> // reln_tuple \<langle>S\<rangle>.proj_append \<langle>S\<rangle> x y = reln_tuple \<langle>S\<rangle> `` {[]} \<and> proj_append \<langle>S\<rangle> y x = reln_tuple \<langle>S\<rangle> `` {[]}}"  using 1 2 3 4 x by auto
  qed
qed

text\<open>Some lemmas about the overlap of words used extensively in the formalization.\<close>

lemma overlapleftexist:
  assumes "(xs@ys) = (us@ws)" 
      and "length us > length xs" 
    shows "(\<exists>zs.(xs@zs) = us)"
proof-
let ?v = "take (length us) (xs@ys)"
  have "?v = us" by (simp add: assms(1))
  moreover then have "take ( length xs) ?v = xs" by (metis append_eq_append_conv_if assms(1) assms(2) less_imp_le_nat)
  ultimately have "xs @ (drop (length xs) ?v)= us" by (metis append_take_drop_id)
  then show ?thesis  by blast
qed

lemma overlaprightexist:
  assumes "(ws@us) = (xs@ys)" 
      and "length ys > length us" 
    shows "(\<exists>zs.(zs@us) = ys)"
proof-
let ?v = "drop (length xs) (ws@us)"
  have "?v = ys" by (simp add: assms(1))
  moreover then have "drop (length ?v - length us) ?v = us" using  append_eq_append_conv_if assms(2) by fastforce
  ultimately have "(take (length ?v - length us) ?v) @ us = ys" by (metis append_take_drop_id)
  then show ?thesis  by blast
qed

text \<open>We provide a definition of a group being 'free', 
if it is isomorphic to a free group \<close>
definition is_freegroup::"_ \<Rightarrow> bool"
  where
"is_freegroup (G::('a,'b) monoid_scheme) \<equiv> (\<exists>(S::(unit \<times> 'a) set). G \<cong> (freegroup S))"

end