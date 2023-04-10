theory Cancellation
imports "FreeGroupMain"  "HOL-Proofs-Lambda.Commutation" 
begin

text \<open>This file contains sections that are adapted from the Cancelation.thy, 
available in the formalisation of Free Groups, by Joachim Breitner, 
available in Archive of Formal Proofs.
 The formalisation is available on 
 https://isa-afp.org/entries/Free-Groups.html. 
Parts where they are either reproduced or adapted, as explicitly mentioned.\<close>

subsection \<open>Defining cancellation functions and some basic properties\<close>

text \<open>The following definitions are directly reproduced from Theory Cancellation.
They correspond to a term rewrite system on words, whose reflective symmetric 
transitive close is the equivalence relation on words, involved in the definition 
of free groups\<close>

definition cancel_at :: "nat \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word"
  where "cancel_at i l = take i l @ drop (2+i) l"

definition cancels_to_1_at ::  "nat \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
where "cancels_to_1_at i l1 l2 = (0\<le>i \<and> (1+i) < length l1
                              \<and> (inverse (l1 ! i) = (l1 ! (1 + i)))
                              \<and> (l2 = cancel_at i l1))"

definition cancels_to_1 :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cancels_to_1 l1 l2 = (\<exists>i. cancels_to_1_at i l1 l2)"

definition cancels_to  :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cancels_to = (cancels_to_1)^**"

definition cancels_eq::"('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where
"cancels_eq = (\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)^**"

text\<open>Cancellation with append\<close> 

lemma cancel_at_leftappend:
  assumes "i\<ge>0" 
      and "(1+i) < length xs" 
      and "cancel_at i xs = ys"
    shows "cancel_at (length zs + i) (zs@xs) = (zs@ys)"
proof-
  have "zs@(take i xs) = take (length zs + i) (zs@xs)" using assms(1) assms(2) by auto
  moreover have "drop (i+2) xs = drop (length zs + (i+2)) (zs@xs)"using assms(1) assms(2) by simp
  ultimately show ?thesis unfolding cancel_at_def by (metis add.assoc add.commute append.assoc assms(3) cancel_at_def)
qed

lemma cancel_at_rightappend:
  assumes "i\<ge>0" 
      and "(1+i) < length xs" 
      and "cancel_at i xs = ys"
    shows "cancel_at i (xs@zs) = (ys@zs)"
proof-
  have "take i (xs@zs) = take i xs" using assms(1) assms (2) by simp
  moreover have "(drop (2 + i) xs)@zs = drop (2+i) (xs@zs)" using assms(1) assms(2) by simp
  ultimately show ?thesis unfolding cancel_at_def by (metis append.assoc assms(3) cancel_at_def)
qed

lemma cancels_to_1_at_leftappend:
  assumes "i\<ge>0" 
      and "(1+i) < length xs" 
      and "cancels_to_1_at i xs ys"
    shows "cancels_to_1_at (length zs + i) (zs@xs) (zs@ys)"
  unfolding cancels_to_1_at_def
proof-
  have 1:"0 \<le> (length zs + i)" using assms(1) by simp
  moreover have 2: "1 + (length zs + i) < length (zs @ xs)" using assms(2) by auto
  have "(inverse (xs ! i)) = (xs ! (i+1))" using assms(3) by (metis add.commute cancels_to_1_at_def)
  moreover then have 3: "inverse ((zs @ xs) ! (length zs + i)) = (zs @ xs) ! (1 + (length zs + i))" by (metis add.commute add.left_commute nth_append_length_plus)
  have "(ys = cancel_at i xs)" using assms(3)using cancels_to_1_at_def by auto
  moreover then have 4: "zs @ ys = cancel_at (length zs + i) (zs @ xs)" using cancel_at_leftappend assms(1) assms(2) by metis
  ultimately show "0 \<le> length zs + i \<and>
    1 + (length zs + i) < length (zs @ xs) \<and>
    inverse ((zs @ xs) ! (length zs + i)) = (zs @ xs) ! (1 + (length zs + i)) \<and>
    zs @ ys = cancel_at (length zs + i) (zs @ xs)" using "2" "3" by blast
qed

lemma cancels_to_1_at_rightappend:
  assumes "i\<ge>0" 
      and "(1+i) < length xs"
      and "cancels_to_1_at i xs ys"
    shows "cancels_to_1_at i (xs@zs) (ys@zs)"
  unfolding cancels_to_1_at_def
proof-
  have 1:"0 \<le> i" using assms(1) by simp
  moreover have 2: "1 + i < length (xs@zs)" using assms(2) by auto
  have "(inverse (xs ! i)) = (xs ! (i+1))" using assms(3) by (metis add.commute cancels_to_1_at_def)
  moreover then have 3: "inverse ((xs @ zs) ! i) = (xs @ zs) ! (1 + i)" by (metis Suc_eq_plus1 Suc_lessD add.commute assms(2) nth_append)
  have "(ys = cancel_at i xs)" using assms(3)using cancels_to_1_at_def by auto
  moreover then have 4: "ys@zs = cancel_at i (xs@zs)" using cancel_at_rightappend assms(1) assms(2) by metis
  ultimately show "0 \<le> i \<and>
    1 + i < length (xs @ zs) \<and> inverse ((xs @ zs) ! i) = (xs @ zs) ! (1 + i) \<and> ys @ zs = cancel_at i (xs @ zs)" using "2" "3" by blast
qed

lemma cancels_to_1_leftappend:
  assumes "cancels_to_1 xs ys"
  shows "cancels_to_1 (zs@xs) (zs@ys)"
  using assms
  unfolding cancels_to_1_def
proof-
  obtain i where 1:"cancels_to_1_at i xs ys" using assms cancels_to_1_def by auto
  then have "i\<ge>0 \<and> (1+i) < length xs" using cancels_to_1_at_def by auto
  then have "cancels_to_1_at (length zs + i) (zs@xs) (zs@ys)" using 1 cancels_to_1_at_leftappend by auto
  then show "\<exists>i. cancels_to_1_at i (zs @ xs) (zs @ ys)" by auto
qed

lemma cancels_to_1_rightappend:
  assumes "cancels_to_1 xs ys"
    shows "cancels_to_1 (xs@zs) (ys@zs)"
  using assms
  unfolding cancels_to_1_def
proof-
 obtain i where 1:"cancels_to_1_at i xs ys" using assms cancels_to_1_def by auto
  then have "i\<ge>0 \<and> (1+i) < length xs" using cancels_to_1_at_def by auto
  then have "cancels_to_1_at i (xs@zs) (ys@zs)" by (simp add: cancels_to_1_at_rightappend 1)
  then show "\<exists>i. cancels_to_1_at i (xs @ zs) (ys @ zs)" by auto
qed

lemma cancels_to_leftappend:
  "cancels_to xs ys \<longrightarrow> cancels_to (zs@xs) (zs@ys)"
  unfolding cancels_to_def
  apply(rule impI)
proof(induction rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have 1:"cancels_to_1 (zs@b) (zs@c)"by (simp add: cancels_to_1_leftappend)
  have "cancels_to_1\<^sup>*\<^sup>* (zs @ a) (zs @ b)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "cancels_to_1\<^sup>*\<^sup>* (zs @ a) (zs @ c)" using 1 by auto
qed

lemma cancels_to_rightappend:
 "cancels_to xs ys \<longrightarrow> cancels_to (xs@zs) (ys@zs)"
  unfolding cancels_to_def
  apply(rule impI)
proof(induction rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have 1:"cancels_to_1 (b@zs) (c@zs)"by (simp add: cancels_to_1_rightappend)
  have "cancels_to_1\<^sup>*\<^sup>* (a@zs) (b@zs)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "cancels_to_1\<^sup>*\<^sup>* (a@zs) (c@zs)" using 1 by auto
qed

lemma cancels_eq_leftappend:
"cancels_eq xs ys \<longrightarrow> cancels_eq (zs@xs) (zs@ys)"
  unfolding cancels_eq_def
  apply(rule impI)
proof(induction rule:rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have 1: "cancels_to (zs@b) (zs@c) \<or> cancels_to (zs@c) (zs@b)" using cancels_to_leftappend by blast
  have "(\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (zs @ a) (zs @ b)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "(\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (zs @ a) (zs @ c)" unfolding cancels_eq_def using 1  by (metis (no_types, lifting) rtranclp.simps)
qed

lemma cancels_eq_rightappend:
  "cancels_eq xs ys \<longrightarrow> cancels_eq (xs@zs) (ys@zs)"
  unfolding cancels_eq_def
  apply(rule impI)
proof(induction rule:rtranclp.induct)
case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have 1: "cancels_to (b@zs) (c@zs) \<or> cancels_to (c@zs) (b@zs)" using cancels_to_rightappend by auto
  have "(\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (a@zs) (b@zs)" by (simp add: rtrancl_into_rtrancl.IH)
  then show "(\<lambda> wrd1 wrd2. cancels_to wrd1 wrd2 \<or> cancels_to wrd2 wrd1)\<^sup>*\<^sup>* (a@zs) (c@zs)" unfolding cancels_eq_def using 1  by (metis (no_types, lifting) rtranclp.simps)
qed

text \<open>Relating cancellation and reduction.\<close>

lemma cancels_to_1_at_not_reduced:
  assumes "reduced xs" 
    shows "\<not>(\<exists>i. i<(length xs - 1) \<and> xs!i = inverse (xs!(i+1)))"
  using assms
proof(induction xs)
  case Nil
  then show ?case  by auto
next
  case (Cons a xs)
  then have xs:"reduced xs" by (metis (mono_tags, lifting) reduced.elims(3) reduced.simps(3))
  then show ?case
  proof(cases "xs = []")
    case True
    then have "(a#xs) = [a]" by simp
    then have "length (a#xs) = 1" by simp
    then show ?thesis using Cons by auto
  next
    case False
    then have gnil: "xs \<noteq> []"  by auto
    then show ?thesis
    proof(cases "length xs = 1")
      case True
      then obtain b where "xs = [b]"  using length_Cons reduced.elims(2) xs by fastforce 
      then have 1:"(a#xs) = (a#[b])" by simp
      then have 2:"length (a#xs) = 2" by auto
      then show ?thesis
      proof(cases "a = inverse b")
        case True
        then have "\<not> reduced (a#xs)" using 1 by auto
  then show ?thesis using Cons by blast
next
  case False
  then have "(a # xs) ! 0 \<noteq> inverse ((a # xs) ! (0 + 1))" using 1  by simp
  then show ?thesis using 2  by force
qed
next
  case False
  then have "1 < length xs" using gnil  nat_neq_iff by auto
  then have ix:"\<not> (\<exists>i<length xs - 1. xs ! i = inverse (xs ! (i + 1)))" using xs Cons by blast
  let ?x = "hd xs"
  show ?thesis
  proof(cases "a = inverse ?x")
    case True
    then have "\<not> reduced (a#xs)"  by (metis gnil list.exhaust_sel reduced.simps(3)) 
then show ?thesis using Cons by blast
next
  case False
  then show ?thesis using ix    
    by (metis (no_types, opaque_lifting) Suc_eq_plus1 Suc_length_conv 
            diff_Suc_1 gnil hd_conv_nth less_diff_conv nat_neq_iff 
            nth_Cons_Suc nth_non_equal_first_eq old.nat.exhaust)
qed
qed
qed
qed

lemma not_reduced_cancels_to_1_at:
  assumes "\<not> reduced xs"
    shows "(\<exists>i .i<(length xs - 1)\<and> xs!i = inverse (xs!(i+1)))"
proof(rule ccontr)
  assume assm: "\<not>(\<exists>i .i<(length xs - 1)\<and>  xs!i = inverse (xs!(i+1)))"
  then have  "\<not>(\<exists>i .i<(length xs - 1)\<and> xs!i = inverse (xs!(i+1)))" by simp
  then have "reduced xs"
  proof(induction xs rule:reduced.induct)
    case 1
    then show ?case by simp
  next
    case (2 g)
    then show ?case by simp
  next
    case (3 g h wrd)
    then have 1: "g \<noteq> inverse h"  by force
    moreover have " \<not> (\<exists>i<length (h # wrd) - 1. (h # wrd) ! i = inverse ((h # wrd) ! (i + 1)))" using 3  using BNF_Greatest_Fixpoint.length_Cons add.commute add_diff_cancel_left' by auto
    ultimately have "reduced (h # wrd)" using 3 by simp
    then show ?case using 1 by simp
  qed
  then show False using assms by blast
qed

lemma cancels_imp_rel: 
  "cancels_to x y \<Longrightarrow> x ~ y"
  unfolding cancels_to_def
proof(induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by blast
next
  case (rtrancl_into_rtrancl a b c)
  then have "cancels_to_1 b c" by simp
  then obtain i where i:"cancels_to_1_at i b c" unfolding cancels_to_1_def by meson
  then have c_def:"(take i b)@(drop (i + 2) b) = c" unfolding cancels_to_1_at_def cancel_at_def
    by force
  moreover have "b!i = inverse (b!(i+1))" using i  unfolding cancels_to_1_at_def cancel_at_def
    using inverse_of_inverse 
    by (simp add: inverse_of_inverse add.commute)
  then have "[b!i, b!(i+1)] ~ []" 
    by (metis base inverse_of_inverse)
  then have "([b!i, b!(i+1)]@(drop (i+2) b)) ~ []@(drop (i+2) b)"
    using reln.refl reln.mult by fast
  then have "((take i b)@(([b!i, b!(i+1)]@(drop (i+2) b)))) ~ (take i b)@(drop (i+2) b)"
    using reln.refl reln.mult 
    by (simp add: mult reln.refl)
  then have "b ~ c" using c_def 
    by (metis Cons_nth_drop_Suc add.commute add_2_eq_Suc' append_Cons append_self_conv2 cancels_to_1_at_def i id_take_nth_drop linorder_not_less plus_1_eq_Suc trans_le_add2)
  then show ?case using reln.trans rtrancl_into_rtrancl(3) by fast
qed

lemma  reln_imp_cancels: 
  "x ~ y \<Longrightarrow> cancels_eq x y"
proof(induction rule:reln.induct)
case (refl a)
then show ?case unfolding cancels_eq_def cancels_to_def by simp
next
  case (sym a b)
  then show ?case unfolding cancels_eq_def 
    by (metis (no_types, lifting) sympD sympI symp_rtranclp)
next
  case (trans a b c)
  then show ?case by (metis (no_types, lifting) cancels_eq_def rtranclp_trans)
next
  case (base g)
  then have "cancels_to_1_at 0 [g, inverse g] []" unfolding cancels_to_1_at_def cancel_at_def by auto
  then have "cancels_to [g, inverse g] []" unfolding cancels_to_def using cancels_to_1_def by auto
  then show ?case unfolding cancels_eq_def by (simp add: r_into_rtranclp)
next
  case (mult xs xs' ys ys')
  have "cancels_eq xs xs'" by (simp add: mult.IH(1))
  then have 1:"cancels_eq (xs@ys) (xs'@ys)"  by (simp add: cancels_eq_rightappend)
  have "cancels_eq ys ys'"  by (simp add: mult.IH(2))
  then have 2:"cancels_eq (xs'@ys) (xs'@ys')" by (simp add: cancels_eq_leftappend)
  then show "cancels_eq (xs@ys) (xs'@ys')" using 1 2  by (metis (no_types, lifting) cancels_eq_def rtranclp_trans)
qed

lemma reduced_rightappend:
  assumes "reduced (xs@ys)"
    shows "reduced xs"
  using assms
proof (induction xs rule : reduced.induct)
case 1
then show ?case
  by simp
next
  case (2 x)
  then show ?case
    by simp
next
  case (3 g1 g2 wrd)
  then show ?case
  proof (cases "g1 =  inverse g2")
    case True    
then show ?thesis 
  using "3.prems" by force
next
  case False
  have "reduced ((g2 # wrd) @ ys)" 
    by (metis "3.prems" append_Cons reduced.simps(3))
  then have "reduced (g2#wrd)"  by (simp add: "3.IH" False)
  then show ?thesis by (simp add: False)
qed
qed

lemma reduced_leftappend:
  assumes "reduced (xs@ys)"
    shows "reduced ys"
  using assms
proof(induction xs rule:reduced.induct)
  case (2 g)
  then show ?case using reduced.simps 
    by (metis append_Cons append_Nil list.exhaust)
next
  case (3 g h wrd)
  then show ?case
    by force
qed (simp)

lemma inv_not_reduced:
  assumes "(i + 1) < length xs"  
      and "inverse (xs ! i) = (xs ! (i + 1))" 
    shows "\<not>(reduced xs)"
  using assms
proof-
  have "inverse (xs ! i) = xs ! (i + 1)" using assms by auto
  have "i + 1 < length xs" using  assms by blast
  then have 1: "xs = (take i xs) @ ((xs ! i)#(xs !(i + 1))#(drop (i + 2) xs))" by (metis Cons_nth_drop_Suc Suc_1 Suc_eq_plus1 add_Suc_right add_lessD1 append_take_drop_id)
  then have "\<not>(reduced ((xs ! i)#(xs ! (i + 1))#(drop (i + 2) xs)))" using assms by (metis inverse_of_inverse reduced.simps(3))
  then have "reduced xs = False" using "1" by (metis reduced_leftappend) 
  then show ?thesis using assms by simp
qed

lemma reduced_no_cancels_to_1_at:
  assumes "reduced xs"
    shows "\<not>(\<exists>i . cancels_to_1_at i xs ys)"
proof(rule ccontr)
  assume assm: "\<not>(\<not>(\<exists>i . cancels_to_1_at i xs ys))"
  hence "\<exists>i . cancels_to_1_at i xs ys" by auto
  then obtain i where "cancels_to_1_at i xs ys" by auto
  then have 1:"inverse (xs!i) = (xs!(i+1))" using cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
  have 2: "i + 1 < length xs" by (metis \<open>cancels_to_1_at i xs ys\<close> add.commute cancels_to_1_at_def)
  then have "xs = (take i xs) @ ((xs!i)#(xs!(i+1))#(drop (i+2) xs))" by (metis Cons_nth_drop_Suc Suc_1 Suc_eq_plus1 add_Suc_right add_lessD1 append_take_drop_id)
  then have "reduced ((xs!i)#(xs!(i+1))#(drop (i+2) xs))" using assms
       reduced_leftappend by metis
  then show "False" using reduced.simps  by (simp add: "1" inverse_of_inverse)
qed


lemma cancels_to_1_red:
  assumes "reduced xs"
    shows "\<forall>ys. \<not>(cancels_to_1 xs ys)"
proof(rule ccontr)
  assume assm : "\<not>(\<forall>ys. \<not>(cancels_to_1 xs ys))"
  then have "\<exists>ys. cancels_to_1 xs ys" by simp
  then obtain ys where y: "cancels_to_1 xs ys" by auto
  then have 1: "\<exists>i\<ge>0. cancels_to_1_at i xs ys" 
    unfolding cancels_to_1_def cancels_to_1_at_def by simp
  then have "reduced xs = False" using "1" using reduced_no_cancels_to_1_at by auto
  then show "False" using assms by simp
qed

lemma reduced_normal:
  assumes "reduced xs"
    shows "(\<not> Domainp cancels_to_1 xs)"
proof-
  show ?thesis using assms cancels_to_1_red by (simp add: cancels_to_1_red Domainp.simps)
qed

lemma eq_symp: 
  "cancels_eq = (symclp cancels_to)^**"
  unfolding cancels_eq_def symclp_def
  by simp

lemma symp_sup:
  "(symclp cancels_to)^** = (sup cancels_to cancels_to^--1)^**"
proof-
  show ?thesis using symclp_pointfree[of "cancels_to"] by metis
qed

lemma sympstar:
  "(symclp cancels_to)^** = (symclp cancels_to_1)^**"
proof-
  have 1:"(symclp cancels_to)^** = (sup cancels_to cancels_to^--1)^**" using symp_sup by simp
  have 2: "... = (sup cancels_to_1^** (cancels_to_1^**)^--1)^**" using cancels_to_def by metis
  have 3: "... = (sup cancels_to_1 cancels_to_1^--1)^**" using rtranclp_sup_rtranclp rtranclp_conversep by metis
  have 4: "... = (symclp cancels_to_1)^**"  using symclp_pointfree[of "cancels_to_1"] by metis
  show ?thesis by(simp add: 1 2 3 4)
qed


text\<open>A few useful lemmas about order of cancellation\<close> 

lemma a1: 
  assumes "j \<ge> 0" 
      and "j + 2 < length xs" 
    shows "take j xs @ drop (2+j) xs = take j xs @ [nth xs (2+j)] @  drop (2+(1+j)) xs"
  using assms
proof(induction j)
case 0
  then show ?case by (metis Suc_1 add.left_neutral add.right_neutral add_2_eq_Suc append_Cons append_take_drop_id id_take_nth_drop same_append_eq self_append_conv2)
next
case (Suc j)
  then show ?case using Cons_nth_drop_Suc by fastforce
qed

lemma a2: 
  assumes "j \<ge> 0" 
      and "j + 2 < length xs" 
    shows "take (j+1) xs @ drop (2+(j+1)) xs = take j xs @ [nth xs j] @  drop (2+(1+j)) xs"
  using assms
proof(induction j)
case 0
  then show ?case by (metis Suc_1 Suc_inject add.commute add_2_eq_Suc' add_lessD1 append_Nil id_take_nth_drop plus_nat.add_0 take_Suc_Cons take_eq_Nil)
next
case (Suc j)
  then show ?case by (metis add.commute add_lessD1 append_assoc plus_1_eq_Suc take_Suc_conv_app_nth)
qed

lemma drop_assoc: 
  assumes "i \<le> j"
    shows "drop i ((take j xs)@(drop (j+2) xs)) =  (drop i (take j xs)) @(drop (j+2) xs)"
  using assms
proof(induction xs arbitrary: i j)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
  proof(cases "i = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have i: "i > 0" using False by simp
    have j:"j \<ge> 1" using False Cons(2) by arith
    then have "take j (a#xs) = a#(take (j - 1) xs)" by (simp add: take_Cons')
    moreover have "drop (j + 2) (a#xs) = drop (j + 1) xs" using j by force
    ultimately have 1:"(take j (a#xs))@(drop (j + 1) xs) = a#(take (j-1) xs)@(drop (j + 1) xs)" by simp
    with False
    have 2: "drop i (a#(take (j-1) xs)@(drop (j + 1) xs)) = (drop (i-1) ((take (j-1) xs)@(drop (j + 1) xs)))"using  drop_Cons' by metis
    have 3: "drop i (a#(take (j-1) xs)@(drop (j + 1) xs)) = (drop (i-1) ((take (j-1) xs)@(drop ((j - 1) + 2) xs)))" using "2" j by auto
    then have 4: "... = (drop (i-1) (take (j-1) xs) @ drop ((j-1) + 2) xs)" using Cons(1)[of "i-1" "j-1"] Cons(2) i j by linarith
    then have 5: "... = drop i (a#(take (j-1) xs)) @ drop (j + 2) (a#xs)" by (metis False \<open>drop (j + 2) (a # xs) = drop (j + 1) xs\<close> ab_semigroup_add_class.add_ac(1) drop_Cons' j le_add_diff_inverse2 nat_1_add_1)
    then have 6: "... = drop i (take j (a#xs)) @  drop (j + 2) (a#xs)"  using \<open>take j (a # xs) = a # take (j - 1) xs\<close> by presburger
    then show ?thesis by (metis "1" "3" "4" "5" \<open>drop (j + 2) (a # xs) = drop (j + 1) xs\<close>)
  qed
qed

lemma take_assoc:
  assumes "i \<le> j"
    shows  "take i ((take j xs)@(drop (j+2) xs)) = take i xs"
  using assms
proof(induction xs arbitrary: i j)
  case (Cons a xs)
  then show ?case
  proof(cases "i = 0")
    case True
    then show ?thesis by simp
  next
    case False
    hence j:"j \<ge> 1" using Cons(2) by arith
    then have "take j (a#xs) = a#(take (j - 1) xs)"  
      by (simp add: take_Cons')
    moreover have "drop (j + 2) (a#xs) = drop (j + 1) xs" using j by force
    ultimately have 1:"(take j (a#xs))@(drop (j + 1) xs) = a#(take (j-1) xs)@(drop (j + 1) xs)"
      by simp
    with take_Cons' False
    have 2:"take i  (a#(take (j-1) xs)@(drop (j + 1) xs)) = a#(take (i - 1) ((take (j-1) xs)@(drop (j + 1) xs)))"
      by metis
    then have 3:"... = a#(take (i - 1) xs)" using Cons(1)[of "i-1" "j-1"] Cons(2) using j by auto
    then have 4:"... = (take i (a#xs))" using False
      by (metis take_Cons')
    then show ?thesis
      by (metis "2" "3" Cons_eq_appendI \<open>drop (j + 2) (a # xs) = drop (j + 1) xs\<close> \<open>take j (a # xs) = a # take (j - 1) xs\<close>)
  qed
qed(auto)

lemma cancel_order: 
  assumes "i +1 < j" 
      and "j + 1 < length xs"
    shows "cancel_at i (cancel_at j xs) = (cancel_at (j-2) (cancel_at i xs))"
  using assms
proof(induction xs arbitrary: i j)
  case Nil
  then show ?case unfolding cancel_at_def by force
next
  case (Cons a xs)
  then show ?case
  proof(cases "i \<le> 1")
    case True
    show ?thesis
    proof(cases "i = 0")
      case True
      have 1: "take i (take j (a # xs) @ drop (2 + j) (a # xs)) = []" using True by simp
      have 2: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) =  take (j - 2) (drop (2 + i) (a # xs))" using True by simp
      have 3: "drop (2 + (j - 2)) (take i (a # xs) @ drop (2 + i) (a # xs)) = drop (2 + (j - 2)) (drop (2 + i) (a # xs))" using True by simp
      then have 4: "... = drop (j + 2) (a#xs)" using True using Cons.prems(1) canonically_ordered_monoid_add_class.lessE by fastforce
      have ij: "2 + i \<le> j" using assms(1) using Cons.prems(1) by linarith
      have 5: "drop (2 + i) ((take j (a # xs)) @ drop (2 + j) (a # xs)) = (drop (2 + i) (take j (a # xs))) @ (drop (2 + j) (a # xs))" using drop_assoc[of "2+i" "j"] ij by (smt (z3) add.commute)
      have 6: "(drop (2 + i) (take j (a # xs))) = (drop 2 (take j (a # xs)))" using True by auto
      then have 7: "... =  take (j - 2) (drop (2 + i) (a # xs))" by (simp add: "6" True drop_take)
      then have 8: "... = take (j - 2) (drop (2 + i) (a # xs))" using True by blast
      show ?thesis unfolding cancel_at_def by (metis "1" "2" "3" "4" "5" "6" "7" add.commute append_self_conv2)
    next
      case False
      then have i1: "i = 1" using True by linarith
      have 1: "take i (take j (a # xs)) = take 1 (a#(take (j - 1) xs))" using i1 take_Cons' by (metis Cons.prems(1) less_nat_zero_code)
      then have 2: "... = (a#(take 0 (take (j - 1) xs)))" using take_Cons' by simp
      then have 3: "... = [a]" by simp
      have 4: "drop (2 + i) (take j (a # xs) @ drop (2 + j) (a # xs)) = (drop (2 + i) (take j (a # xs))) @ drop (2 + j) (a # xs)" using drop_assoc by (metis Cons.prems(1) add.commute discrete i1 nat_1_add_1)
      then have 5: "... =  (drop (1 + i) (take (j - 1) xs)) @ drop (1 + j) xs" using take_Cons' drop_Cons' by (simp add: "4" drop_Cons' take_Cons' Cons.prems(1) add.assoc add_diff_cancel_left' add_eq_0_iff_both_eq_0 gr_implies_not_zero less_one nat_1_add_1)
      have 6: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) = take (j - 2) (a#(drop (1 + i) xs))"  by (metis (no_types, lifting) True append_Cons append_eq_append_conv2 append_self_conv diff_add_inverse2 diff_is_0_eq' drop_Cons' i1 nat_1_add_1 numerals(1) take_0 take_Cons_numeral zero_le_one)
      then have 7: "... = (a#(take (j - 3) (drop (1 + i) xs)))" using take_Cons' by (metis Cons.prems(1) diff_diff_left i1 less_numeral_extra(3) nat_1_add_1 numeral_Bit1 numerals(1) zero_less_diff)
      then have 8: "... = [a] @ (take (j - 3) (drop (1 + i) xs))"  by simp
      have 9: "drop (2 + (j - 2)) (take i (a # xs) @ drop (2 + i) (a # xs)) = drop j (a#(drop (1 + i) xs))" using i1 drop_Cons' by (smt (z3) "7" "8" Cons.prems(1) Nat.diff_add_assoc add_diff_cancel_left' add_diff_cancel_right' append.assoc append_take_drop_id diff_diff_left diff_is_0_eq' le_numeral_extra(4) less_imp_le_nat list.distinct(1) nat_1_add_1 numeral_One numeral_plus_one semiring_norm(5) take0 take_0 take_Cons' take_Cons_numeral)
      then have 10: "... = drop (j - 1) (drop (1 + i) xs)" using drop_Cons' by (metis "1" "2" list.distinct(1) take_eq_Nil)
      then have 11: "... = drop (j - 1 + 1 + i) xs" by simp
      then have 12: "... = drop (j + 1) xs" using i1 Cons.prems(1) by force
      have 13: "(take (j - 3) (drop (1 + i) xs)) = (drop (1 + i) (take (j - 1) xs))" using drop_take by (simp add: drop_take i1 numeral_Bit1)
      then have 14: "[a] @ (take (j - 3) (drop (1 + i) xs)) = [a] @ (drop (1 + i) (take (j - 1) xs))" by blast
      then have 15: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) = take i (take j (a # xs)) @ (drop (1 + i) (take (j - 1) xs))" using "1" "2" "3" "6" "7" "8" by presburger
      have 16: "take i (take j (a # xs)) = take i (take j (a # xs) @ drop (2 + j) (a # xs))" using Cons.prems(1) i1 by auto
      then have 17: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) = take i (take j (a # xs) @ drop (2 + j) (a # xs)) @ (drop (1 + i) (take (j - 1) xs))" using 15 16  by presburger
      then have 18: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) @ drop (2 + (j - 2)) (take i (a # xs) @ drop (2 + i) (a # xs)) = take i (take j (a # xs) @ drop (2 + j) (a # xs)) @ (drop (1 + i) (take (j - 1) xs)) @ drop (j + 1) xs" by (metis "10" "11" "12" "9" append_assoc)
      then have 19: "take (j - 2) (take i (a # xs) @ drop (2 + i) (a # xs)) @ drop (2 + (j - 2)) (take i (a # xs) @ drop (2 + i) (a # xs)) = take i (take j (a # xs) @ drop (2 + j) (a # xs)) @ drop (2 + i) (take j (a # xs) @ drop (2 + j) (a # xs))" by (metis "4" "5" add.commute)
      then show ?thesis unfolding cancel_at_def by presburger
    qed
  next
    case False
    hence "i \<ge> 2" by simp
    with Cons(1)[of "i-1" "j-1"]
    have "cancel_at (i - 1) (cancel_at (j - 1) xs) =  cancel_at (j - 1 - 2) (cancel_at (i - 1) xs)" using Cons(2,3) by fastforce
    then have A: "take (i - 1) (take (j - 1) xs @ drop (2 + (j - 1)) xs) @
               drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =
               take (j - 1 - 2) (take (i - 1) xs @ drop (2 + (i - 1)) xs) @
               drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs)" unfolding cancel_at_def by blast
    have 1: "drop (2 + (j - 1)) xs = drop (2 + j) (a#xs)" using drop_Cons' Cons.prems(1) by auto
    have 2: "drop (2 + (i - 1)) xs = drop (2 + i) (a#xs)" using drop_Cons' False by auto
    have 3: "(a#(take (i - 1) (take (j - 1) xs @ drop (2 + (j - 1)) xs))) @
               drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =
               (a#(take (j - 1 - 2) (take (i - 1) xs @ drop (2 + (i - 1)) xs))) @
               drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs)" using A by (metis append_Cons)
    then have 4: "take i (a#(take (j - 1) xs @ drop (2 + (j - 1)) xs)) @
               drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =
               take (j - 2) (a#(take (i - 1) xs @ drop (2 + (i - 1)) xs)) @
               drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs)" using take_Cons' by (smt (verit, ccfv_SIG) Cons.prems(1) False Nat.add_diff_assoc2 diff_add_inverse2 diff_diff_left diff_is_0_eq less_diff_conv nat_1_add_1 nat_le_linear not_add_less2)
    then have 5: "take i (take j (a#xs) @ drop (2 + (j - 1)) xs) @
               drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =
               take (j - 2) (take i (a#xs) @ drop (2 + (i - 1)) xs) @
               drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs)" using take_Cons' by (smt (z3) Cons.prems(1) False Nat.add_diff_assoc2 add_is_0 append_Cons diff_add_inverse2 less_nat_zero_code nat_le_linear)
    have 6:  "drop (2 + (i - 1)) (take (j - 1) xs @ drop (2 + (j - 1)) xs) =  drop (2 + i) (a#(take (j - 1) xs @ drop (2 + (j - 1)) xs))" using drop_Cons' False by auto
    then have 7: "... =  drop (2 + i) (take j (a#xs) @ drop (2 + (j - 1)) xs)" using take_Cons' by (metis Cons.prems(1) Cons_eq_appendI gr_implies_not_zero)
    have 8: "drop (2 + (j - 1 - 2)) (take (i - 1) xs @ drop (2 + (i - 1)) xs) =  drop (2 + (j - 2)) (a#(take (i - 1) xs @ drop (2 + (i - 1)) xs))" using drop_Cons' False by (smt (z3) Cons.prems(1) Nat.add_diff_assoc \<open>2 \<le> i\<close> diff_add_inverse diff_le_self le_eq_less_or_eq le_trans less_diff_conv not_numeral_le_zero)
    then have 9: "... =  drop (2 + (j - 2)) (take i (a#xs) @ drop (2 + (i - 1)) xs)" using take_Cons' by (metis (no_types, opaque_lifting) False append_eq_Cons_conv linordered_nonzero_semiring_class.zero_le_one)
    then show ?thesis unfolding cancel_at_def by (metis "1" "2" "5" "6" "7" "8")
  qed  
qed

lemma takenth: 
  assumes "take i xs = take i ys" "i \<ge> 0" "j < i"
    shows "(nth xs j) = (nth ys j)"
  by (metis assms(1) assms(3) nth_take)

lemma Con_nth: 
  assumes "(nth xs i) = (nth ys j)" 
    shows "(nth (x#xs) (i+1)) = (nth (x#ys) (j+1))"
  by (simp add: assms)

lemma comm: 
  assumes "a > 0"
    shows "(a::nat) - 1 + 1 = a + 1 - 1" 
  by (simp add: assms)

lemma cancel_atnth: 
  assumes "j > i + 1" 
      and "j < length xs"
    shows "(nth xs j) = (nth (cancel_at i xs) (j-2))"
  using assms
  unfolding cancel_at_def
  proof(induction xs arbitrary: i j)
    case Nil
    have "j < 0" using Nil assms(2) by auto
    then show ?case by simp
next
  case (Cons a x)
  then show ?case
  proof(cases "i > 0")
    case True
  have i: "i > 0" using True by simp
  have a:"(j - 1) < length x" using Cons(3) Cons.prems(1) by auto
  have b: "(i - 1) + 1 < (j - 1)" using Cons True i by linarith
  have "(nth x (j - 1)) = nth (take (i - 1) x @ drop (2 + (i - 1)) x) ((j - 1) - 2)" using Cons(1)[of "i - 1" "j - 1"]  a b by metis
  then have c: "(nth (a#x) (j - 1 + 1)) = nth (a#(take (i - 1) x @ drop (2 + (i - 1)) x)) ((j - 1 - 2 + 1))" using Con_nth[of "x" "j - 1" "(take (i - 1) x @ drop (2 + (i - 1)) x)" "j - 1 - 2" "a"] by metis
  then have "(nth (a#x) j) = nth (a#(take (i - 1) x @ drop (2 + (i - 1)) x)) ((j - 2))"by (smt (z3) add_eq_0_iff_both_eq_0 b diff_add_inverse2 diff_diff_left less_diff_conv less_nat_zero_code nat_1_add_1 nth_Cons')
  then have "(nth (a#x) j) = nth ((a#(take (i-1) x)) @ drop (2 + (i - 1)) x) ((j - 2))" by (smt (z3) append_Cons)
  then have "(nth (a#x) j) = nth ((take i (a#x)) @ drop (2 + (i - 1)) x) ((j - 2))" using take_Cons' i  by (smt (z3) not_gr_zero)
  then have "(nth (a#x) j) = nth ((take i (a#x)) @ drop (2 + i) (a#x)) (j - 2)" using drop_Cons' i  by (smt (z3) drop_drop gr_implies_not0)
  then show ?thesis by metis
  next
    case False
    then have i: "i = 0" by blast
    then have a:"nth ((take i (a#x)) @ drop (2 + i) (a#x)) (j - 2) = nth (drop (2 + i) (a#x)) (j - 2)" by simp
    have b:"... = nth (drop 2 (a#x)) (j - 2)" using i  by auto
    have c:"... = nth (drop 1 x) (j - 2)" using drop_Cons' by simp
    then have d: "... =  nth (tl x) (j - 2)" by (simp add: drop_Suc)
    then have e: "... = nth x (j - 1)" using nth_tl by (smt (verit, ccfv_threshold) Cons.prems(1) Cons.prems(2) Suc_1 Suc_diff_Suc add_cancel_right_left add_diff_inverse_nat diff_diff_left drop_Suc_Cons i length_drop length_tl not_less_eq zero_less_diff)
    have f: "(nth (a#x) j) = (nth x (j - 1))" by (metis Cons.prems(1) add_lessD1 i nth_Cons_pos)
    then show ?thesis using a b c d e by presburger
  qed 
qed

lemma length_Cons: "(length xs) + 1 = (length (a#xs))"
  by auto

lemma assoc_Cons: "(x#(ys@zs)) = ((x#ys)@zs)"
  by simp

lemma cancel_at_length: 
  assumes "0 \<le> i" 
      and "i + 1 < length xs"
    shows "length (cancel_at i xs) = (length xs) - 2"
  using assms
  unfolding cancel_at_def
proof(induction xs arbitrary: i)
case Nil
  then show ?case by auto
next
  case (Cons a x)
  then show ?case
  proof(cases "length x \<ge> 1")
    case True
    then have lx: "length x \<ge> 1" by simp
    then show ?thesis
  proof(cases "i > 0")
    case True 
    have a: "0 \<le> i - 1" using Cons.prems(1) by simp
  have b: "(i - 1) + 1 \<le> length x" using Cons.prems(2) True by fastforce
  have "length (take (i - 1) x @ drop (2 + (i - 1)) x) = length x - 2" using a b Cons(1)[of "i - 1"] by (metis Cancellation.length_Cons Cons.prems(2) True comm diff_add_inverse2 le_neq_implies_less nat_neq_iff)
  then have "(length (take (i - 1) x @ drop (2 + (i - 1)) x)) + 1 = (length x - 2) + 1" by presburger
  then have "(length (take (i - 1) x @ drop (2 + (i - 1)) x)) + 1 = (length x + 1) - 2" using lx Nat.add_diff_assoc2 Cons.prems(1) True  by (smt (z3) Cons.prems(2) length_Cons comm diff_add diff_diff_left diff_is_0_eq' less_diff_conv nat_1_add_1 nat_less_le zero_less_diff)
  then have "(length (take (i - 1) x @ drop (2 + (i - 1)) x)) + 1 = (length (a#x)) - 2" using length_Cons[of "x" "a"] by argo
  then have "(length (a#(take (i - 1) x @ drop (2 + (i - 1)) x))) = (length (a#x)) - 2" using length_Cons[of  "(take (i - 1) x @ drop (2 + (i - 1)) x)" "a"] by argo
  then have "(length ((a#take (i - 1) x) @ drop (2 + (i - 1)) x)) = (length (a#x)) - 2" using assoc_Cons[of "a" "take (i - 1) x" "drop (2 + (i - 1)) x"] by argo
  then have "length ((take i (a#x)) @ drop (2 + (i - 1)) x) = (length (a#x)) - 2" using True take_Cons' [of "i" "a" "x"] by presburger
  then have "length ((take i (a#x)) @ drop (2 + i) (a#x)) = (length (a#x)) - 2" using True drop_Cons' Cons.prems(1) by simp
  then show ?thesis  by blast
  next
    case False
    have i: "i = 0" using Cons.prems(1) False by auto
    then have 1: "length ((take i (a#x)) @ drop (2 + i) (a#x)) = length (drop (2 + i) (a#x))" by simp
    have 2: "... = length (drop 2 (a#x))"  using i by simp
    have 3: "... = length (drop 1 (a#x)) - 1"  by simp
    have 4: "... = length (drop 0 (a#x)) - 2" by simp
    have 5: "... = (length (a#x)) - 2" by auto
    then show ?thesis using "1" "2" "3" "4" by presburger
  qed
  next
    case False
    then have 1: "length x < 1" by linarith
    then have 2: "length x = 0"  by auto
    then have 3: "x = []" by auto
    then have 4: "(a#x) = [a]" by simp
    have "i + 1 \<ge> 1" using Cons.prems(2) by simp
    then have "i + 1 \<ge> length (a#x)" using 4 by simp
    then show ?thesis using Cons(3) by linarith
  qed
qed

lemma rtrancancel:
  assumes "((\<exists>i. cancels_to_1_at i xs ys) \<or> xs = ys)"
    shows "cancels_to xs ys"
  by (metis assms cancels_to_1_def cancels_to_def rtranclp.simps)

text \<open>Some useful term re-writing lemmas. These are directly reproduced from
        Theory Cancellation.\<close> 

theorem lconfluent_confluent:
  "\<lbrakk> wfP (R^--1); \<And>a b c. R a b \<Longrightarrow> R a c \<Longrightarrow> \<exists>d. R^** b d \<and> R^** c d  \<rbrakk> \<Longrightarrow> confluent R"
by(auto simp add: diamond_def commute_def square_def intro: newman)

lemma confluentD:
  "\<lbrakk> confluent R; R^** a b; R^** a c  \<rbrakk> \<Longrightarrow> \<exists>d. R^** b d \<and> R^** c d"
by(auto simp add: commute_def diamond_def square_def)

lemma tranclp_DomainP: "R^++ a b \<Longrightarrow> Domainp R a"
by(auto elim: converse_tranclpE)

lemma confluent_unique_normal_form:
  "\<lbrakk> confluent R; R^** a b; R^** a c; \<not> Domainp R b; \<not> Domainp R c  \<rbrakk> \<Longrightarrow> b = c"
  by(fastforce dest!: confluentD[of R a b c] dest: tranclp_DomainP rtranclpD[where a=b] rtranclpD[where a=c])

subsection\<open>Showing existence of the normal form. This part is original.\<close>

lemma Church_Rosser_unique_normal_form:
  assumes "Church_Rosser R" 
      and "(sup R (R\<inverse>\<inverse>))\<^sup>*\<^sup>* a b"  
      and "\<not> Domainp R a" 
      and "\<not> Domainp R b"
    shows " a = b"
proof-
  have "\<exists>c. R^** a c \<and> R^** b c" using assms(1, 2) 
    using Church_Rosser_def by fastforce
  then obtain c where "R^** a c \<and> R^** b c" by blast
  then have 1: "(a = c \<or> a \<noteq> c \<and> R\<^sup>+\<^sup>+ a c) \<and> (b = c \<or> b \<noteq> c \<and> R\<^sup>+\<^sup>+ b c)" 
    by (simp add: rtranclpD)
  have a: "\<not> (R\<^sup>+\<^sup>+ a c)" using assms(3) tranclp_DomainP by metis
  have b: "\<not> (R\<^sup>+\<^sup>+ b c)" using assms(4) tranclp_DomainP by metis
  have "a = c \<and> b = c" using 1 a b by auto
  then show ?thesis by simp
qed

text\<open>We prove that cancelling terminates, that is, cancellation always returns a 
    reduced word. adapted.\<close> 

lemma canceling_terminates: 
      "wfP (cancels_to_1^--1)"
proof-
  have "wf (measure length)" by auto
  moreover
  have "{(x, y). cancels_to_1 y x} \<subseteq> measure length"
    by (auto simp add: cancels_to_1_def cancel_at_def cancels_to_1_at_def)
  ultimately
  have "wf {(x, y). cancels_to_1 y x}"
    by(rule wf_subset)
  thus ?thesis by (simp add:wfP_def)
qed

text\<open>Showing confluence for cancels to 1. This statement is adapted from 
Theory cancellation.\<close> 

lemma diamond_cancel: 
  shows "diamond (\<lambda> xs ys. (cancels_to_1 xs ys) \<or> xs = ys)"
  unfolding  diamond_def cancels_to_1_def commute_def square_def 
  apply (rule allI, rule allI, rule impI, rule allI, rule impI)
proof-
  fix xs ys zs:: "('a,'b) word"
  assume 1:"(\<exists>i. cancels_to_1_at i xs ys) \<or> xs = ys"
  assume 2:"(\<exists>i. cancels_to_1_at i xs zs) \<or> xs = zs"
  show "\<exists>us. ((\<exists>i. cancels_to_1_at i ys us) \<or> ys = us) \<and> ((\<exists>i. cancels_to_1_at i zs us) \<or> zs = us)"
  proof(cases "xs = ys \<or> xs = zs")
    case True
    then have "(\<exists>i. cancels_to_1_at i ys zs) \<or> (\<exists>i. cancels_to_1_at i zs ys) \<or> ys = zs" using 1 2 by blast
  then show ?thesis by blast
  next
    case False
    have 3: "(\<exists>i. cancels_to_1_at i xs ys) \<and> (\<exists>j. cancels_to_1_at j xs zs)" using 1 2 False by blast
    obtain i where i:"cancels_to_1_at i xs ys" using 3 by auto
    obtain j where j:"cancels_to_1_at j xs zs" using 3 by auto
  then show ?thesis 
    proof(cases "ys = zs")
      case True
    then show ?thesis by auto
    next
      case False
      then show ?thesis
      proof(cases "i \<in> {j, j + 1} \<or> j \<in> {i, i+1}")
        case True
        have a: "ys \<noteq> zs"  by (simp add: False)
      then show ?thesis
        proof(cases "i = j")
          case True
          have y: "ys = cancel_at i xs" using cancels_to_1_at_def using i by auto
          have z: "zs = cancel_at i xs" using cancels_to_1_at_def True using j by auto
          have cont: "ys = zs" using y z by simp
        then show ?thesis using a by auto 
        next
          case False
          then have ij: "i = j + 1 \<or> j = i + 1" using True by blast
          have xi: "inverse (xs!i) = (xs!(1+i))" using cancels_to_1_at_def i by auto
          have xj: "inverse (xs!j) = (xs!(1+j))" using cancels_to_1_at_def j by auto
        then show ?thesis
          proof(cases "i = 1 + j")
            case True
            have xij: "((nth xs j) = (nth xs (2+j)))" using True xi xj inverse_of_inverse by (metis add_2_eq_Suc plus_1_eq_Suc)
            have y1: "ys = cancel_at (j+1) xs" by (metis True i add.commute cancels_to_1_at_def)
            have z1: "zs = cancel_at j xs" using cancels_to_1_at_def j by (simp add: cancels_to_1_at_def)
            have contr1: "ys = zs" using y1 z1 a1 z1 xij by (smt (z3) True i a2 add.commute cancel_at_def cancels_to_1_at_def group_cancel.add1 nat_1_add_1 zero_le)
          show ?thesis using a contr1 by auto
          next
            case False
            have "j = i + 1" using False ij by auto
            then have xji: "((nth xs i) = (nth xs (2+i)))" by (metis Suc_1 add.commute add_Suc_right inverse_of_inverse plus_1_eq_Suc xi xj)
            have y2: "ys = cancel_at i xs" using cancels_to_1_at_def i by auto
            have z2: "zs = cancel_at (i+1) xs" using xji cancels_to_1_at_def j by (simp add: cancels_to_1_at_def \<open>j = i + 1\<close>)
            have contr2: "ys = zs" using y2 z2 a2 z2 xji  by (smt (verit) j \<open>j = i + 1\<close> a1 add.left_commute cancel_at_def cancels_to_1_at_def le_add2 le_add_same_cancel2 nat_1_add_1)
          then show ?thesis using a contr2 by auto
          qed
        qed
      next
        case False
        then have ij: " \<not> (i \<in> {j, j + 1} \<or> j \<in> {i, i + 1})" by auto
        have xi: "inverse (xs!i) = (xs!(1+i))" using cancels_to_1_at_def i by auto
        have xj: "inverse (xs!j) = (xs!(1+j))" using cancels_to_1_at_def j by auto
        then show ?thesis
        proof(cases "i \<le> j")
          case True
           then have l: "i + 1 < j"  by (metis False discrete insert_iff le_neq_implies_less)
          then have j1: "i + 1 < j + 1" by linarith
          have i0: "i\<ge>0" by simp
          have j0: "j \<ge> 0"  by simp
          then have j20: "j - 2 \<ge> 0" by simp
          have z: "zs = cancel_at j xs" using j cancels_to_1_at_def by auto
          have y: "ys = cancel_at i xs" using i cancels_to_1_at_def by auto
          have il: "1 + i < length xs" using i by (simp add: cancels_to_1_at_def)
          have m: "1 + j  < length xs" using j cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          then have jl: "j + 1 < length xs" by auto
          then have "i + 1 + 2 < length xs" using l  by linarith
          then have zz: "i + 1 < length xs - 2" by simp
          have "length xs - 2 = length (cancel_at i xs)" using cancel_at_length[of "i" "xs"] il i0 by presburger
          then have "length xs - 2 = length ys" using y by simp
          then have "j + 1 < length ys + 2" using jl  by linarith
          then have j2y: "(j - 2) + 1 < length ys" using l by linarith
          have "length xs - 2 = length (cancel_at j xs)" using cancel_at_length[of "j" "xs"]  jl j0 by metis
          then have "length xs - 2 = length zs" using z by simp
          then have iz: "i + 1 < length zs" using zz  by simp
          have j: "j < length xs" using m by linarith
          then have n: "cancel_at i (cancel_at j xs) = cancel_at (j-2) (cancel_at i xs)" using cancel_order l m by (metis add.commute)
          then have eq: "cancel_at i zs = cancel_at (j-2) ys" using \<open>cancels_to_1_at j xs zs\<close> \<open>cancels_to_1_at i xs ys\<close> cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          have take: "take j zs = take j xs" using take_assoc cancel_at_def l m by (metis \<open>cancels_to_1_at j xs zs\<close> add.commute cancels_to_1_at_def eq_imp_le)
          then have o: "(nth xs i) = (nth zs i)" using l i0 by (metis add_lessD1 nth_take)
          have p: "(nth xs (i+1)) = (nth zs (i+1))" using l i0 take takenth by (metis True order.trans)
          then have "inverse (nth zs i) = (nth xs (i+1))" using xi o by (smt (z3) add.commute) 
          then have "inverse (nth zs i) = (nth zs (i+1))" using p by (smt (z3))
          then have inv1: "inverse (nth zs i) = (nth zs (1+i))" by simp
          have zeq: "(cancel_at i zs) = cancel_at i zs" by simp
          have zu: "cancels_to_1_at i zs (cancel_at i zs)"  using i0 iz inv1 zeq unfolding cancels_to_1_at_def by linarith
          have ys:"ys = cancel_at i xs" using  \<open>cancels_to_1_at i xs ys\<close> cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          then have q: "(nth xs j) = (nth ys (j - 2))" using cancel_atnth l j by blast
          have r: "(nth xs (j + 1)) = (nth ys ((j - 2) + 1))"  using cancel_atnth j1 m by (smt (verit) ys add.commute comm diff_add_inverse diff_diff_left diff_is_0_eq' l le_add2 nat_1_add_1 nat_less_le zero_less_diff)
          have s: "inverse (nth ys (j - 2)) = (nth xs (j + 1))" using xj q  by auto
          then have inv2:"inverse (nth ys (j - 2)) = (nth ys ((j - 2) + 1))" using r  by fastforce
          have yeq: "cancel_at (j - 2) ys = cancel_at (j - 2) ys" by simp
          have yu: "cancels_to_1_at (j - 2) ys (cancel_at (j - 2) ys)" using j20 j2y  inv2 yeq unfolding cancels_to_1_at_def by auto
          then show ?thesis using yu zu eq by auto
        next
          case False
          then have j1i: "j + 1 < i" using ij by (metis discrete insertCI leI le_neq_implies_less)
          then have j1i1: "j + 1 < i + 1" by linarith
          have i0: "i\<ge>0" by simp
          then have i20: "i - 2 \<ge> 0" by simp
          have j0: "j \<ge> 0"  by simp
          have z: "zs = cancel_at j xs" using j cancels_to_1_at_def by auto
          have y: "ys = cancel_at i xs"  using i cancels_to_1_at_def by auto
          have jl: "1 + j  < length xs" using j cancels_to_1_at_def by (simp add: cancels_to_1_at_def)
          have il: "1 + i < length xs" using i by (simp add: cancels_to_1_at_def)
          have "length xs - 2 = length (cancel_at j xs)" using cancel_at_length[of "j" "xs"] jl j0 by presburger
          then have  "length xs = length (cancel_at j xs) + 2" using jl by linarith
          then have "i + 1 < (length zs) + 2" using il i0 z by auto
          then have i2z: "(i - 2) + 1 < length zs" using j1i by linarith
          have "length xs - 2 = length (cancel_at i xs)" using cancel_at_length[of "i" "xs"] il i0 by presburger
          then have xy: "length xs - 2 = length ys" using y by simp
          have "j + 1 + 2 < length xs" using j1i il  by linarith
          then have "j + 1 < length xs - 2" using jl  by linarith
          then have jy: "j + 1 < length ys" using xy by simp
          have "cancel_at j (cancel_at i xs) = cancel_at (i-2) (cancel_at j xs)" using j1i il cancel_order by auto
          then have eq: "cancel_at j ys = cancel_at (i-2) zs" using y z by simp
          have take: "take i xs = take i ys" using take_assoc cancel_at_def j1i by (metis add_diff_inverse_nat diff_add_inverse diff_add_inverse2 diff_le_self less_imp_diff_less less_nat_zero_code y zero_less_diff)
          have nth: "(nth xs j) = (nth ys j)" using takenth i0 j1i1 add_less_imp_less_right take by blast
          have nth1: "(nth xs (j+1)) = (nth ys (j+1))" using takenth i0 j1i1 j1i take by auto
          have "inverse (nth ys j) = (nth xs (j+1))" using xj nth by fastforce
          then have invj: "inverse (nth ys j) = (nth ys (j+1))" using nth1 by (smt (z3))
          have yu:  "cancels_to_1_at j ys (cancel_at j ys)" using j0 jy invj cancels_to_1_at_def by fastforce
          have nthi: "(nth xs i) = (nth zs (i - 2))" using z j1i  il cancel_atnth by (metis trans_le_add2 verit_comp_simplify1(3))
          have nthi1: "(nth xs (i+1)) = (nth zs ((i - 2) + 1))"  using z j1i1 il by (metis Nat.add_diff_assoc2 add.commute add_lessD1 cancel_atnth discrete j1i nat_1_add_1)
          then have "inverse (nth zs (i - 2)) = (nth xs (i + 1))" using xi nthi by fastforce
          then have invi: "inverse (nth zs (i - 2)) = (nth zs ((i - 2) + 1))" using nthi1 by (smt (z3))
          have zu: "cancels_to_1_at (i - 2) zs (cancel_at (i - 2) zs)" using i20 i2z invi cancels_to_1_at_def by (metis add.commute)
          then show ?thesis using eq yu zu by auto
        qed
      qed
    qed
  qed
qed

lemma cancels_to_1_reduced :
  assumes "cancels_to_1 xs ys"  
      and "cancels_to_1 xs zs" 
      and "reduced ys" 
      and "reduced zs" 
    shows "ys = zs"
    using assms
  unfolding cancels_to_1_def
proof-
  have 1: "(\<exists>i. cancels_to_1_at i xs ys) \<or> xs = ys" using assms(1) cancels_to_1_def by blast
  have 2: "(\<exists>i. cancels_to_1_at i xs zs) \<or> xs = zs" using assms(2) cancels_to_1_def by blast
  have "diamond (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" using diamond_cancel by simp
  then have "commute (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" using diamond_def by auto
  then have "square (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)  (\<lambda> x y . (cancels_to_1 x y) \<or> x = y)  (\<lambda> x y . (cancels_to_1 x y) \<or> x = y)" using commute_def by blast
  then have "(\<forall>xs ys. (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) xs ys --> (\<forall>zs. (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) xs zs --> (\<exists>us. (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) ys us \<and> (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) zs us)))" using square_def[of "(\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" "(\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" "(\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" "(\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)"] by blast
  then have "(\<exists>us. (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) ys us \<and> (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) zs us)" using 1 2 assms(1) assms(2) by blast
  then have "\<exists>us. (ys = us \<and> zs = us)" using cancels_to_1_red assms(3) assms(4) by (simp add: cancels_to_1_red)
  then show ?thesis by simp
qed

lemma diamondlemmaapp: 
  assumes "(\<exists>i. cancels_to_1_at i xs ys) \<or> xs = ys" 
      and "(\<exists>i. cancels_to_1_at i xs zs) \<or> xs = zs"
    shows "\<exists>us. ((\<exists>i. cancels_to_1_at i ys us) \<or> ys = us) \<and> ((\<exists>i. cancels_to_1_at i zs us) \<or> zs = us)"
proof-
  have "diamond (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" using diamond_cancel by simp
  then have "commute (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" using diamond_def by auto
  then have "square (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" using commute_def by blast
  then have "(\<forall>xs ys. (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) xs ys --> (\<forall>zs. (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) xs zs --> (\<exists>us. (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) ys us \<and> (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) zs us)))" using square_def[of "(\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" "(\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" "(\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)" "(\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys)"] by blast
  then have "(\<exists>us. (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) ys us \<and> (\<lambda>xs ys. (cancels_to_1 xs ys) \<or> xs = ys) zs us)" by (metis assms(1) assms(2) cancels_to_1_def)
  then show ?thesis by (simp add: cancels_to_1_def)
qed

text \<open>This lemma is adapted from Theory Cancelation.\<close> 

lemma confluent_cancels_to_1: 
        "confluent cancels_to_1"
proof(rule lconfluent_confluent)
  show "wfP cancels_to_1\<inverse>\<inverse>" by (rule canceling_terminates)
next
  fix a b c
  assume "cancels_to_1 a b"
  then have 1: "(\<exists>i. cancels_to_1_at i a b)" by (simp add: cancels_to_1_def)
  assume "cancels_to_1 a c"
  then have 2: "\<exists>j. cancels_to_1_at j a c" by (simp add: cancels_to_1_def)
  show "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d"
  proof-
    have "\<exists>d. ((\<exists>i. cancels_to_1_at i b d) \<or> b = d) \<and> ((\<exists>i. cancels_to_1_at i c d) \<or> c = d)" using 1 2 diamondlemmaapp by blast
    then obtain d where "((\<exists>i. cancels_to_1_at i b d) \<or> b = d) \<and> ((\<exists>i. cancels_to_1_at i c d) \<or> c = d)" by force
    then have "((\<exists>i. cancels_to_1_at i b d) \<or> b = d) \<and> ((\<exists>i. cancels_to_1_at i c d) \<or> c = d)"  by simp
    then have "(cancels_to b d) \<and> (cancels_to c d)" by (simp add: rtrancancel)
    then have "cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" using cancels_to_def by metis      
    then show ?thesis by auto
  qed
qed

text \<open>Finally, we show each reduced word has a unique normal form. 
      This lemma is adapted from Theory Cancelation.\<close> 

lemma unique_reduced_cancel:
  assumes "cancels_to xs ys" 
      and "cancels_to xs zs" 
      and "reduced ys" "reduced zs"
    shows "ys = zs"
proof(rule confluent_unique_normal_form)
  have "cancels_to_1^** = cancels_to" using cancels_to_def  by metis
  show "confluent cancels_to_1" using confluent_cancels_to_1 by simp
next
  show "cancels_to_1\<^sup>*\<^sup>* xs ys" using assms(1) cancels_to_def by metis
next
  show "cancels_to_1\<^sup>*\<^sup>* xs zs" using assms(2) cancels_to_def by metis
next
  show "\<not> Domainp cancels_to_1 ys" using assms(3) reduced_normal by blast
next
  show "\<not> Domainp cancels_to_1 zs" using assms(4) reduced_normal by blast
qed  

lemma reduced_cancel_eq:
  assumes "cancels_eq xs ys" 
      and "reduced xs" 
      and "reduced ys"
    shows "xs = ys"
proof-
  have "confluent cancels_to_1" using confluent_cancels_to_1 by blast
  then have 1: "Church_Rosser cancels_to_1" 
    using Church_Rosser_confluent by (simp add: Church_Rosser_confluent)
  have "(symclp cancels_to)^** xs ys" using assms(1) eq_symp by metis
  then have "(symclp cancels_to_1)^** xs ys" using sympstar by metis
  then have 2: "(sup cancels_to_1 cancels_to_1^--1)^** xs ys" 
    using symclp_pointfree[of "cancels_to_1"] by metis
  have 3: "\<not> Domainp cancels_to_1 xs" using assms(2) reduced_normal by blast
  have 4: "\<not> Domainp cancels_to_1 ys" using assms(3) reduced_normal by blast
  show ?thesis 
    using 1 2 3 4 Church_Rosser_unique_normal_form[of "cancels_to_1" "xs" "ys"] by blast
qed

end

