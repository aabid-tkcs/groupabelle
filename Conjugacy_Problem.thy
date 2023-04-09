theory Conjugacy_Problem
imports "FreeGroupMain" "UniversalProperty" "Word_Problem"
begin

text\<open>This file contains a proof of decidability of the conjugacy problem on 
free groups\<close>

subsection \<open>Defining Cyclic Reduction.\<close>

fun uncyclic :: "('a,'b) word \<Rightarrow> bool"
  where
"uncyclic [] = True" |
"uncyclic [x] = True" |
"uncyclic (x#xs) =  (x \<noteq> inverse (last xs))"

definition cyclic_reduced :: "('a,'b) word \<Rightarrow> bool"
  where "cyclic_reduced xs = (reduced xs \<and> uncyclic xs)"

fun uncycle :: "('a,'b) word \<Rightarrow> ('a,'b) word"
  where
"uncycle [] = []"|
"uncycle [x] = [x]"|
"uncycle (x#xs) = (if (x = inverse (last xs)) 
                    then uncycle (take (length xs - 1) xs)
                    else (x#xs))"

definition cyclic_reduce :: "('a,'b) word \<Rightarrow> ('a,'b) word"
  where "cyclic_reduce xs =  uncycle ((reduce^^(length xs)) xs)"

text \<open>Some basic properties of the above functions.\<close>

lemma take_last:
  assumes "xs \<noteq> []"
    shows  "xs = (take (length xs - 1) xs) @ [last xs]"
  using assms
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case
  proof(cases "xs = []")
    case True
    then have 1: "(a#xs) = [a]" by simp
    have 2: "(take (length (a#xs) - 1) (a#xs)) = []" using True by simp
    have 3: "[last (a#xs)] = [a]" using True by simp
then show ?thesis using 1 2 3  by simp
next
  case False
  then have 1: "xs = take (length xs - 1) xs @ [last xs]" using Cons.IH by auto
  then have "(a#xs) = (a#( take (length xs - 1) xs @ [last xs]))" by simp
  then have "(a#xs) = (take (length (a#xs) - 1)(a#xs) @ [last xs])" using False by (metis Cons.prems butlast_conv_take last_ConsR snoc_eq_iff_butlast)
  then have "(a#xs) = (take (length (a#xs) - 1)(a#xs) @ [last (a#xs)])" using False by auto
  then show ?thesis by simp
qed
qed

lemma reduced_take_last: 
  assumes "reduced (x#xs)"
    shows "reduced (take (length xs - 1) xs)"
proof(cases "xs = []")
  case True
  then show ?thesis by simp
next
  case False
  have "(x#xs) = [x] @ xs"  by simp
  then have a: "reduced xs" using assms reduced_leftappend by metis
  moreover have "xs = (take (length xs - 1) xs) @ [last xs]"using False take_last by blast
  ultimately show ?thesis using reduced_rightappend by metis
qed

lemma reduced_uncycle: 
  assumes "reduced xs"
    shows "reduced (uncycle xs)"
  using assms
proof(induction xs rule: uncycle.induct)
  case 1
  then have "uncycle [] = []" by simp
  then show ?case by simp 
next
  case (2 x)
 then have "uncycle [x] = [x]" by simp
  then show ?case by simp 
next
  case (3 x v va)
  then show ?case 
  proof(cases "x \<noteq> inverse (last (v#va))")
    case True
    then have "uncycle (x#v#va) = (x#v#va)" by auto
then show ?thesis using 3 by metis
next
  case False
  have "reduced (v#va)" using 3 by (metis reduced.simps(3))
  then have " reduced (take (length (v # va) - 1) (v # va))" using reduced_take_last "3.prems" by blast
  then have "reduced (uncycle (take (length (v # va) - 1) (v # va)))" using 3 False by blast
  moreover have "uncycle (x#v#va) = uncycle (take (length (v # va) - 1) (v # va))" using False by auto
  ultimately show ?thesis by presburger
qed
qed

lemma reduced_cyclic_reduce:
  "reduced (cyclic_reduce xs)"
proof(induction xs rule: reduced.induct)
  case 1
  have "((reduce^^(length [])) []) = []" by simp
  moreover have "uncycle [] = []" by simp
  ultimately have a: "cyclic_reduce [] = []" by (simp add: cyclic_reduce_def)
  have 1: "reduced []" by simp
  show ?case using 1 by (simp add: a cyclic_reduced_def)
next
  case (2 x)
  have "((reduce^^(length [x])) [x]) = [x]" by simp
  moreover have "uncycle [x] = [x]" by simp
  ultimately have a: "cyclic_reduce [x] = [x]" by (simp add: cyclic_reduce_def)
  have 1: "reduced [x]" by simp
  show ?case using 1 by (simp add: a cyclic_reduced_def)
next
  case (3 g h wrd)
  have "cyclic_reduce xs = uncycle ((reduce^^(length xs)) xs)"  by (simp add: cyclic_reduce_def)
  then show ?case using reduced_uncycle 3 
    by (metis cyclic_reduce_def reduced_iter_length)
qed

lemma uncylic_uncycle: 
  "uncyclic (uncycle xs)"
proof(induction xs rule: uncycle.induct)
  case 1
  then have "uncycle [] = []" by simp
  then show ?case by simp
next
  case (2 x)
   then have "uncycle [x] = [x]" by simp
  then show ?case by simp
next
  case (3 x v va)
  then show ?case
proof(cases "x = inverse(last (v#va))")
  case True
  then have "uncyclic (uncycle (take (length (v # va) - 1) (v # va)))"  using "3.IH" by blast
  moreover have "uncycle (x#v#va) = uncycle (take (length (v # va) - 1) (v # va))" using True by simp
  ultimately show ?thesis by presburger
next
  case False
  then show ?thesis using False by auto
qed
qed

lemma uncyclic_cyclic_reduce : 
  "uncyclic (cyclic_reduce xs)"
  by (simp add: cyclic_reduce_def uncylic_uncycle)

lemma cyclic_reduced_cyclic_reduce: 
  "cyclic_reduced (cyclic_reduce xs)"
proof-
  have "reduced (cyclic_reduce xs)" by (simp add: reduced_cyclic_reduce)
  moreover have "uncyclic (cyclic_reduce xs)" by (simp add: uncyclic_cyclic_reduce)
  ultimately show ?thesis by (simp add: cyclic_reduced_def)
qed

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
  then show ?case using 1  by auto
qed

lemma wordinverse_append: 
  "(wordinverse xs) @ (wordinverse ys) = (wordinverse (ys@xs))"
proof(induction ys)
  case Nil
  have "wordinverse [] = []" by simp
  then show ?case by simp
next
  case (Cons x ys)
  have "(wordinverse xs) @ (wordinverse (x # ys)) = (wordinverse xs) @ (wordinverse ys) @ [inverse x]" by simp
  moreover have "(wordinverse ((x#ys)@xs)) = (wordinverse (ys@xs)) @ [inverse x]" by simp
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
  have "wordinverse [inverse a] = [a]" using inverse_of_inverse  by (metis append.left_neutral wordinverse.simps(1) wordinverse.simps(2))
  then have 2:"wordinverse ((wordinverse xs) @ [inverse a]) = [a] @ wordinverse (wordinverse xs)" using wordinverse_append by metis
  then have "[a] @ wordinverse (wordinverse xs) = [a] @ xs" using Cons by auto
  moreover have "[a] @ xs = (a#xs)" by simp
  ultimately show ?case using 1 2 by simp
qed

subsection \<open>Conjugacy relation and Cyclic Permutations.\<close>

definition conj_rel :: "('a,'b) monoidgentype set 
          \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "conj_rel S xs ys = (xs \<in> \<langle>S\<rangle> \<and> ys \<in> \<langle>S\<rangle> \<and> (\<exists>us \<in>\<langle>S\<rangle> . 
                              (us @ xs @ (wordinverse us)) ~ ys))" 

text \<open>Proving conjugacy is an equivalence relation.\<close>

lemma conj_rel_refl:
  assumes "xs \<in> \<langle>S\<rangle>"
    shows "conj_rel S xs xs"
  using assms
proof-
  have 1: "[] \<in> \<langle>S\<rangle>" unfolding freewords_on_def by (simp add: words_on.empty)
  have "[] @ xs @ [] = xs" by simp
  moreover then have "xs ~ xs" by auto
  ultimately  have "([] @ xs @ []) ~ xs" by simp
  then show ?thesis using assms conj_rel_def 1 by force
qed
 
lemma conj_rel_symm:
  assumes "conj_rel S xs ys" 
    shows "conj_rel S ys xs"
  using assms
proof-
  obtain us where 1: "us \<in> \<langle>S\<rangle> \<and> (us @ xs @ (wordinverse us)) ~ ys" using assms(1) conj_rel_def by blast
  let ?b = "wordinverse us"
  have inv: "wordinverse ?b = us" by (simp add: wordinverse_of_wordinverse)
  have b: "?b \<in> \<langle>S\<rangle>" by (simp add: 1 span_wordinverse)
  have "(?b @ us @ xs @ (wordinverse us)) ~ (?b @ ys)" by (simp add: 1 mult reln.refl)
  moreover have "([] @ xs @ (wordinverse us)) ~ (?b @ us @ xs @ (wordinverse us))" using inverse_wordinverse append_assoc mult reln.refl reln.sym by metis
  ultimately have "([] @ xs @ (wordinverse us)) ~ (?b @ ys)" using  reln.trans by blast
  then have "(xs @ (wordinverse us) @ us) ~ (?b @ ys @ (wordinverse ?b))" using inv mult by fastforce
  moreover have "(xs @ []) ~ (xs @ (wordinverse us) @ us)" using wordinverse_inverse reln.refl inv mult reln.sym by metis
  ultimately have "xs ~ (?b @ ys @(wordinverse ?b))" using reln.trans by auto
  then show ?thesis  using b assms reln.sym unfolding conj_rel_def  by blast
qed

lemma conj_rel_trans: 
  assumes "conj_rel S xs ys" 
      and "conj_rel S ys zs"
    shows "conj_rel S xs zs"
  using assms
proof-
  obtain us where 1: "us \<in> \<langle>S\<rangle> \<and> (us @ xs @ (wordinverse us)) ~ ys" using assms(1) conj_rel_def by blast
  obtain ws where 2: "ws \<in> \<langle>S\<rangle> \<and>(ws @ ys @ (wordinverse ws)) ~ zs" using assms(2) conj_rel_def by blast
  have "(ws @ (us @ xs @ (wordinverse us))) ~ (ws @ ys)"  by (simp add: 1 mult reln.refl)
  then have  "(ws @ us @ xs @ (wordinverse us) @ wordinverse ws)~ (ws @ ys @ wordinverse ws)"  using mult by fastforce
  then have "(ws @ us @ xs @ (wordinverse us) @ wordinverse ws) ~ zs" using 2 using reln.trans by blast
  then have "((ws @ us) @ xs @ (wordinverse (ws @ us))) ~ zs" by (simp add: wordinverse_append)
  moreover have "(ws @ us) \<in>  \<langle>S\<rangle>" using "2" "1"  using span_append freewords_on_def  by blast
  ultimately show ?thesis using assms unfolding conj_rel_def by blast
qed
                           
definition conj_class ::"('a,'b) monoidgentype set \<Rightarrow> ('a,'b) word \<Rightarrow> ('a,'b) word set"
  where "conj_class S xs = {ys. conj_rel S xs ys}"

text \<open>Cyclic Permutations\<close>

definition cycle_at_i :: "('a,'b) word \<Rightarrow> nat \<Rightarrow> ('a,'b) word"
  where
"cycle_at_i xs i = (drop i xs)@(take i xs)"

definition cyclicp_at_i :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> nat \<Rightarrow> bool"
  where "cyclicp_at_i xs ys i = (cycle_at_i xs i = ys)"

definition cyclicp :: "('a,'b) word \<Rightarrow> ('a,'b) word \<Rightarrow> bool"
  where "cyclicp xs ys = (\<exists>i. cyclicp_at_i xs ys i)"

text \<open>Lemmas relating conjugacy with cyclic permutations and cyclic reduction.\<close>

lemma cycle_at_conj: 
  assumes "xs \<in>  \<langle>S\<rangle>" 
    shows "conj_rel S xs (cycle_at_i xs i)"
proof-
  have 1: "xs = (take i xs) @ (drop i xs)" by simp
  have d: "(drop i xs) \<in>  \<langle>S\<rangle>" using 1 rightappend_span assms unfolding freewords_on_def by metis
  have t: "(take i xs) \<in>  \<langle>S\<rangle>" using 1 leftappend_span assms unfolding freewords_on_def  by metis
  let ?as = "wordinverse (take i xs)"
  have a: "?as \<in>  \<langle>S\<rangle>" using t by (simp add: span_wordinverse)
  have "(wordinverse (take i xs) @ (take i xs)) ~ []" using inverse_wordinverse by fast
  then have "(wordinverse (take i xs) @ (take i xs) @ (drop i xs)) ~ (drop i xs)" using mult reln.refl by (metis append.left_neutral append_assoc)
  then have "(wordinverse (take i xs) @ (take i xs) @ (drop i xs) @ (take i xs)) ~ (drop i xs) @ (take i xs)" using mult reln.refl by (metis append.assoc)
  then have "(wordinverse (take i xs) @ xs @ (take i xs)) ~ (drop i xs) @ (take i xs)" using 1 by (metis append.assoc)
  then have "(?as @ xs @ wordinverse ?as) ~ (drop i xs) @ (take i xs)" by (simp add: wordinverse_of_wordinverse)
  then have "(?as @ xs @ wordinverse ?as) ~ (cycle_at_i xs i)"by (simp add: cycle_at_i_def)
  moreover have "(cycle_at_i xs i) \<in>  \<langle>S\<rangle>" unfolding cycle_at_i_def using d t span_append freewords_on_def  by blast
  ultimately show ?thesis unfolding conj_rel_def using assms a by blast
qed

lemma conj_cyclcip: 
  assumes "xs \<in> \<langle>S\<rangle>" "ys \<in> \<langle>S\<rangle>" 
      and "cyclicp xs ys" 
    shows "conj_rel S xs ys"
proof-
  obtain i where "ys = cycle_at_i xs i" by (metis assms(3) cyclicp_at_i_def cyclicp_def)
  then have "conj_rel S xs ys" by (simp add: assms(1) cycle_at_conj)
  then show ?thesis by simp
qed

lemma reduce_span: 
  assumes "xs \<in> \<langle>S\<rangle>" 
    shows "reduce xs \<in> \<langle>S\<rangle>"
  using assms
proof(induction xs rule:reduce.induct)
  case 1
  then have "reduce [] = []" by simp
  then show ?case using 1  by simp
next
  case (2 x)
  then have "reduce [x] = [x]" by simp
  then show ?case using 2  by simp
next
  case (3 x y xs)
  then show ?case
  proof(cases "x = inverse y")
    case True
    then have "reduce (x # y # xs) = xs" by simp
    moreover have "xs \<in> \<langle>S\<rangle>" using 3 span_cons unfolding freewords_on_def  by blast
    ultimately show ?thesis  by simp
next
  case False
  then have 1: "reduce (x # y # xs) = (x#(reduce (y # xs)))" by simp
  have "(y # xs) \<in> \<langle>S\<rangle>" using 3 span_cons unfolding freewords_on_def by blast
  then have "reduce (y # xs) \<in> \<langle>S\<rangle>" using 3 False by simp
  moreover have "[x] \<in> \<langle>S\<rangle>" using False using 3 cons_span unfolding freewords_on_def by blast
  ultimately show ?thesis using 1 span_append unfolding freewords_on_def by fastforce
qed
qed

lemma iter_reduce_span : 
  assumes "xs \<in> \<langle>S\<rangle>" 
    shows "((reduce^^n) xs) \<in>  \<langle>S\<rangle>"
  using assms
proof(induction n)
  case 0
  then have "(reduce^^0) xs = xs" by simp
  then show ?case by (simp add: assms)
next
  case (Suc n)
  then have "(reduce^^n) xs \<in> \<langle>S\<rangle>" by simp
  then have "reduce ((reduce^^n) xs) \<in> \<langle>S\<rangle>" using reduce_span by auto
then show ?case by simp
qed

lemma conj_iter :
  assumes "xs \<in>  \<langle>S\<rangle>" 
    shows "conj_rel S ((reduce^^(length xs)) xs) xs"
  using assms
proof-
  have "cancels_to xs ((reduce^^(length xs)) xs)" using iter_cancels_to  by auto
  then have "xs ~  ((reduce^^(length xs)) xs)" using cancels_imp_rel  by blast
  then have "([] @ ((reduce^^(length xs)) xs) @ (wordinverse [])) ~ xs" by (simp add: reln.sym)
  moreover have "((reduce^^(length xs)) xs) \<in>  \<langle>S\<rangle>" using assms iter_reduce_span by blast
  ultimately show ?thesis unfolding conj_rel_def using assms words_on.empty 
    unfolding freewords_on_def by blast
qed

lemma conj_uncycle: 
  assumes "xs \<in>  \<langle>S\<rangle>" 
    shows "conj_rel S (uncycle xs) xs"
  using assms
proof(induction xs rule: uncycle.induct)
  case 1
  then have "uncycle [] = []" by simp
  moreover have "([] @ [] @ wordinverse [])~[]" by auto
  ultimately show ?case unfolding conj_rel_def using 1 words_on.empty by force
next
  case (2 x)
then have "uncycle [x] = [x]" by simp
  moreover have "([] @ [x] @ wordinverse [])~[x]" by auto
  ultimately show ?case unfolding conj_rel_def unfolding freewords_on_def using 2 by (metis span_cons freewords_on_def)
next
case (3 x v va)
  then show ?case
  proof(cases "x = inverse (last (v#va))")
    case True
    have b:"(x#v # va)\<in>  \<langle>S\<rangle>" using 3 by simp
    then have "(v # va)\<in>  \<langle>S\<rangle>" using span_cons unfolding freewords_on_def by blast
    then have "take (length (v # va) - 1) (v # va) \<in> \<langle>S\<rangle>" unfolding freewords_on_def by (metis append_take_drop_id leftappend_span)
    then have 1: "conj_rel S (uncycle (take (length (v # va) - 1) (v # va))) (take (length (v # va) - 1) (v # va))" using 3 True  by blast
    have a: "uncycle (x # v # va) = uncycle (take (length (v # va) - 1) (v # va))" using True by simp
    then have "([] @ uncycle (x # v # va) @ wordinverse []) ~ uncycle (take (length (v # va) - 1) (v # va))" by (simp add: reln.refl)
    moreover have "uncycle (take (length (v # va) - 1) (v # va)) \<in>  \<langle>S\<rangle>" using 1 unfolding conj_rel_def by simp
    ultimately have 2: "conj_rel S (uncycle (x # v # va)) (uncycle (take (length (v # va) - 1) (v # va)))" unfolding conj_rel_def using a empty unfolding freewords_on_def by metis
    have x: "[x] \<in>  \<langle>S\<rangle>" using b cons_span unfolding freewords_on_def by blast
    have "(last (v#va)) = inverse x" using True inverse_of_inverse by blast
    then have "[x] @ (take (length (v # va) - 1) (v # va)) @ wordinverse [x] = (x # v # va)" using take_last 
      by (metis (no_types, lifting) append_eq_Cons_conv list.simps(3) wordinverse.simps(1) wordinverse.simps(2))
    moreover have "(take (length (v # va) - 1) (v # va)) \<in>  \<langle>S\<rangle>" using 1 unfolding conj_rel_def by simp
    ultimately  have "conj_rel S (take (length (v # va) - 1) (v # va)) (x # v # va)" unfolding conj_rel_def using  b x reln.refl by metis
    then have "conj_rel S (uncycle (take (length (v # va) - 1) (v # va))) (x # v # va)" using 1 conj_rel_trans  by blast
    then show ?thesis using 2 conj_rel_trans by fast
next
  case False
  then have "uncycle (x#v#va) = (x#v#va)" by simp
  moreover then have "([] @ uncycle (x#v#va) @ wordinverse []) ~ (x#v#va)" using reln.refl by auto
  ultimately show ?thesis unfolding conj_rel_def unfolding freewords_on_def using 3 
    by (metis words_on.empty freewords_on_def)
qed
qed

text \<open>Every word is conjugate to its cyclic reduction.\<close>

lemma conj_cyclicreduce:
  assumes "xs \<in>  \<langle>S\<rangle>" 
    shows "conj_rel S (cyclic_reduce xs) xs"
proof-
  have "conj_rel S ((reduce^^(length xs)) xs) xs" using assms by (simp add: conj_iter)
  moreover have "conj_rel S (uncycle ((reduce^^(length xs)) xs)) ((reduce^^(length xs)) xs)" using assms iter_reduce_span conj_uncycle by fast
  ultimately show ?thesis  unfolding cyclic_reduce_def  using conj_rel_trans by blast
qed

subsection \<open>The Conjugacy Problem.\<close>

text \<open>A few general results that we will use below.\<close>

lemma reduced_iter_eq: 
  assumes "reduced xs" 
    shows "((reduce^^n) xs) = xs"
  by (metis assms funpow_0 iter_cancels_to le0 not_reduced_iter_suc unique_reduced_cancel)

lemma hd_last_wordinverse: 
  assumes "length xs > 0" 
    shows "hd xs = inverse (last (wordinverse xs))"
  using assms
proof(induction xs)
  case Nil
  then have False by auto
  then show ?case by simp
next
  case (Cons a xs)
  have 1:"hd (a#xs) = a" by simp
  have " wordinverse (a#xs) = wordinverse xs @ [inverse a]" by simp 
  then have "last (wordinverse (a#xs)) = inverse a" by simp
  then have "inverse (last (wordinverse (a#xs))) = inverse (inverse a)" by simp
  then have "inverse (last (wordinverse (a#xs))) = a"  by (metis inverse_of_inverse)
  then show ?case using 1  by simp
qed

lemma reduced_rev: 
  assumes "reduced xs" 
    shows "reduced (rev xs)"
proof(rule ccontr)
  assume "\<not> reduced (rev xs)"
  then obtain i where ixs:"i<length (rev xs)-1 \<and>(rev xs)!i = inverse ((rev xs)!(i+1))" using not_reduced_cancels_to_1_at by blast
  then have "(rev xs)!i = xs!((length xs - 1)- i)"  by (metis add_lessD1 diff_Suc_eq_diff_pred length_rev less_diff_conv rev_nth)
  moreover have "((rev xs)!(i+1)) = xs!((length xs - 1)- (i+1))" by (metis diff_diff_left ixs length_rev less_diff_conv plus_1_eq_Suc rev_nth)
  ultimately have "xs!((length xs - 1)- i) = inverse (xs!((length xs - 1)- (i+1)))" using ixs by presburger
  then have j:"(xs!((length xs - 1)- (i+1))) = inverse (xs!((length xs - 1)- i))" using inverse_of_inverse by blast
  let ?j = "((length xs - 1)- (i+1))"
   have "?j + 1 = ((length xs - 1)- i)"by (metis Suc_diff_Suc add.commute ixs length_rev plus_1_eq_Suc)
   moreover have "?j <length xs-1" using calculation by linarith
   ultimately have "(?j <length xs-1) \<and> (xs!?j = inverse (xs!(?j+1)))" using j by presburger
   then have "\<not> reduced xs" using cancels_to_1_at_not_reduced by blast
   then show False using assms by simp
 qed

lemma reduced_inverse: 
  assumes "reduced xs" 
    shows "reduced (map inverse xs)"
proof(rule ccontr)
  assume "\<not> reduced (map inverse xs)"
  then obtain i where ixs:"i<length (map inverse xs)-1 \<and>(map inverse xs)!i = inverse ((map inverse xs)!(i+1))" using not_reduced_cancels_to_1_at by blast
  then have "xs!i = inverse (xs!(i+1))"  by (metis add_lessD1 inverse_of_inverse length_map less_diff_conv nth_map)
  moreover have "i<length  xs-1" using ixs by auto
  ultimately have "\<not> reduced xs" using cancels_to_1_at_not_reduced by blast
 then show False using assms by simp
 qed

lemma reduced_wordinverse: 
  assumes "reduced xs" 
    shows "reduced (wordinverse xs)"
proof-
  have "reduced (rev xs)" using assms by (simp add: reduced_rev)
  then have "reduced (map inverse (rev xs))" by (simp add: reduced_inverse)
  then show ?thesis by (simp add: wordinverse_redef2)
qed


lemma append_notreduced: 
  assumes "reduced xs" 
      and "reduced ys" 
      and "xs \<noteq> []" 
      and "ys \<noteq> []" 
    shows "last xs = inverse (hd ys) \<Longrightarrow> \<not>(reduced (xs@ys))"
  using assms
proof(induction xs rule: reduced.induct)
  case 1
  then show ?case  by blast
next
  case (2 x)
  then show ?case by (metis append_Cons append_self_conv2 last_ConsL list.exhaust_sel reduced.simps(3))
next
  case (3 x y xys)
then have 1: "x \<noteq> inverse y" by auto
  moreover have  "last (y # xys) = inverse (hd ys)" using 3 by auto
  ultimately have "\<not> reduced ((y # xys) @ ys)" using 3 assms reduced_rightappend by blast
  then show ?case by auto
qed

lemma append_reduced: 
  assumes "reduced xs" 
      and "reduced ys" 
    shows "last xs \<noteq> inverse (hd ys) \<Longrightarrow> (reduced (xs@ys))"
  using assms
proof(induction xs rule:reduced.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case using reduced.elims(3) by fastforce
next
  case (3 x y xys)
  then have 1: "x \<noteq> inverse y" by auto
  moreover have  "last (y # xys) \<noteq> FreeGroupMain.inverse (hd ys)" using 3 by auto
  ultimately have "reduced ((y # xys) @ ys)" using 3  by auto
  then show ?case using 1 by auto
qed

lemma onesidecancel: 
  assumes "reduced xs" 
      and "reduced ys" 
      and "reduced zs" 
      and "ys \<noteq> []" 
      and "\<not> reduced (xs@ys@zs)" 
    shows "(\<not> reduced (xs@ys)) \<or> (\<not> reduced (ys@zs))"
proof(rule ccontr)
  assume "\<not>((\<not> reduced (xs@ys)) \<or> (\<not> reduced (ys@zs)))"
  then have assm: "(reduced (xs@ys) \<and> reduced (ys@zs))"  by simp
  have "reduced (xs@ys@zs)"
  proof(rule ccontr)
    assume assmassm:"\<not> reduced (xs@ys@zs)"
    then show False
    proof(cases "xs = []")
      case True
      then have "\<not> reduced (ys@zs)" using assmassm by auto
      then show ?thesis using assm by simp
    next
      case False
      have "last xs = inverse (hd (ys@zs))" using append_reduced assm assms by blast
      then have "last xs = inverse (hd ys)" using assms by simp
      then have "\<not> reduced (xs @ ys)" using append_notreduced using False assms by blast
      then show ?thesis using assm by blast
    qed
  qed
  then show False using assms  by simp
qed

lemma tlempty: 
  assumes "length xs > 1" 
    shows "tl xs \<noteq> []"
proof(rule ccontr)
  assume "\<not> tl xs \<noteq> []" 
  then have tl: "tl xs = []" by auto
  then have "xs = [hd xs] @ tl xs" using assms by (metis append_Nil2 hd_Cons_tl list.size(3) not_one_less_zero)
  then have "xs = [hd xs]" using tl by simp
  then have "length xs = 1" by (metis BNF_Greatest_Fixpoint.length_Cons One_nat_def list.size(3))
  then show False using assms by simp
qed

lemma not_uncyclic:
  assumes "length xs > 1" 
      and "hd xs = inverse (last xs)" 
    shows "\<not> uncyclic xs"
proof-
  let ?x = "hd xs"
  let ?s = "tl xs"
  have 1:"?s \<noteq> []" using assms tlempty by blast
  have xs:"xs = (?x#?s)" using assms by (metis hd_Cons_tl list.size(3) not_one_less_zero)
  then have "?x = inverse (last ?s)" using assms  by (metis last_ConsR length_tl less_numeral_extra(3) list.size(3) zero_less_diff)
  then show ?thesis using 1 uncyclic.elims(2) by fastforce
qed

lemma inverse_not_refl: 
  assumes "xs = ys" 
    shows "xs \<noteq> inverse ys"
proof-
  show ?thesis using assms  inverse.elims by blast
qed

lemma onesidenotcancel:
  assumes "reduced xs" 
      and "cyclic_reduced ys" 
    shows "(reduced (xs@ys) \<or> reduced (ys@ wordinverse xs))"
proof(rule ccontr)
  have xs:"reduced ys" using assms(2) using cyclic_reduced_def by auto
  assume "\<not>(reduced (xs@ys) \<or> reduced (ys@ wordinverse xs))"
  then have assm:"(\<not> reduced (xs@ys)) \<and> (\<not> reduced (ys@ wordinverse xs))" by simp
  then show False
  proof(cases "length ys > 1") 
  case True
  then have 1:"last xs = inverse (hd ys)" using append_reduced assm assms(1) xs  by auto
  have 2:"last ys = inverse (hd (wordinverse xs))" using append_reduced assms(1) xs assm reduced_wordinverse by auto
  have "last xs = inverse (hd (wordinverse xs))" by (metis append_Nil2 assm last_snoc list.exhaust list.sel(1) wordinverse.simps(2) wordinverse_symm xs)
  then have "hd ys = inverse (last ys)" using 1 2 inverse_of_inverse by metis
  then have "\<not> uncyclic ys" using True not_uncyclic by auto
  then show ?thesis using assms(2) cyclic_reduced_def by auto
next
  case False
  then have F:"length ys \<le> 1" by simp
  show ?thesis
  proof(cases "ys = []")
    case True
    then have "reduced (xs@ys)" using assms(1) by simp
then show ?thesis using assm by simp
next
  case False
  then have "length ys = 1" using F by (metis One_nat_def append_eq_conv_conj div_by_Suc_0 div_less nat_less_le take0)
  then obtain y where b:"ys = [y]" using reduced.elims(2) xs by fastforce
  then have "last xs = inverse y" using assm xs append_reduced assms(1) by (metis list.sel(1))
  moreover have "y = inverse (hd (wordinverse xs))" using assms(1)  reduced_wordinverse xs assm b append_reduced by (metis last.simps)
  ultimately have "last xs = (hd (wordinverse xs))" by (metis inverse_of_inverse)
  moreover have "last xs = inverse (hd (wordinverse xs))" using assm wordinverse.simps(1) wordinverse_redef2  wordinverse_of_wordinverse xs by (metis append_Nil2 calculation hd_map hd_rev rev.simps(1))
  ultimately show ?thesis using inverse_not_refl by blast
qed
qed
qed

lemma middleterm: 
  assumes "(xs@ys) = (zs@xs)" 
    shows "(\<exists>us ws. (ws@us@ws) = (xs@ys) \<and> (ws@us@ws) = (zs@xs))"
  by (metis append_eq_append_conv2 append_self_conv assms)

lemma overlapleftexist:
  assumes "(xs@ys) = (ws@us)" 
      and "length ws > length xs" 
    shows "(\<exists>zs.(xs@zs) = ws)"
proof-
let ?v = "take (length ws) (xs@ys)"
  have "?v = ws" by (simp add: assms(1))
  moreover then have "take ( length xs) ?v = xs" by (metis append_eq_append_conv_if assms(1) assms(2) less_imp_le_nat)
  ultimately have "xs @ (drop (length xs) ?v)= ws" by (metis append_take_drop_id)
  then show ?thesis  by blast
qed

lemma append_cyclicp: 
  assumes "xs = us@ws" 
      and "ys = ws@us" 
    shows "cyclicp xs ys"
proof-
  have "take (length us) xs = us" using assms(1) by simp
  moreover have "drop (length us) xs = ws" using assms(1) by simp
  ultimately have "ys = (drop (length us) xs) @ (take (length us) xs)" using assms(2) by simp
  then show ?thesis unfolding cyclicp_def cyclicp_at_i_def cycle_at_i_def by blast
qed

primrec power :: "('a, 'b) word \<Rightarrow> nat \<Rightarrow> ('a, 'b) word"
  where
"power xs 0 = []"|
"power xs (Suc n) = (xs@(power xs n))"

lemma powerrightappend:
  assumes "n>0" 
    shows "(power xs (n - 1))@xs = power xs n"
  using assms
proof(induction n)
  case 0
  then show ?case by blast
next
  case (Suc n)
  then show ?case
  proof(cases "0<n")
    case True
    then have "(power xs (n - 1))@xs = power xs n" using Suc.IH  by auto
    then have "xs@(power xs (n - 1))@xs = xs@power xs n" by simp
  then show ?thesis  by (metis power.simps(2) Suc_pred True append_assoc diff_Suc_1)
next
  case False
  then have n: "n=0" by simp
  moreover have "(power xs 0)@xs = power xs 1" by simp
  ultimately show ?thesis by simp
qed
qed

lemma divassm: 
  assumes "(a::nat) = (b * n) + k" 
      and "a<b" 
    shows "n=0"
  by (metis Euclidean_Division.div_eq_0_iff assms(1) assms(2) div_mult_self4 less_nat_zero_code zero_eq_add_iff_both_eq_0)

lemma overlappower:  
  assumes "(ys@xs) = (xs@zs)"  
      and "length xs \<ge>  length ys" 
      and "length xs = ((length ys) * n) + k   \<and> k<(length ys)"
    shows "take ((length ys) * n) xs = power ys n"
  using assms
proof( induction n arbitrary: xs ys zs)
  case 0 
  then show ?case by simp
next
  case (Suc n)
  let ?x = "drop (length ys) xs"
  have ba:"ys@?x = xs" by (metis Suc.prems(1) Suc.prems(2) append_eq_append_conv_if append_take_drop_id)
  have "length ?x = length ys * Suc n + k - (length ys) \<and> k < (length ys)" by (simp add: Suc.prems(3))
  then have 1: "length ?x = length ys * n + k  \<and> k < (length ys)" by simp
  then show ?case
  proof(cases "length ?x < length ys")
    case True
    then have 0: "n = 0" using "1" divassm by blast
    have "take (length ys) xs = ys"  by (metis append_eq_conv_conj ba)
    moreover have "power ys 1 = ys" by simp
    ultimately show ?thesis using 0 by simp
next
  case False
  then have "length ?x \<ge> length ys" by simp
  moreover have "ys@?x = ?x@zs" by (metis Suc.prems(1) Suc.prems(2) append.right_neutral append_eq_append_conv_if)
  ultimately have "take (length ys * n) ?x = power ys n" using "1" Suc.IH by blast
  then have "ys@take (length ys * n) ?x = ys@power ys n" by simp
  then have "take (length ys * Suc n) xs = ys@power ys n" using ba by (metis append_eq_conv_conj mult_Suc_right take_add)
  then show ?thesis by simp
qed
qed

definition divmod_nat_rel :: "nat => nat => nat \<times> nat => bool" where
  "divmod_nat_rel m n qr \<longleftrightarrow>
    m = fst qr * n + snd qr \<and>
      (if n = 0 then fst qr = 0  else if n > 0 then 0 \<le> snd qr \<and> snd qr < n \<and> fst qr \<ge> 0 else n < snd qr \<and> snd qr \<le> 0)"

lemma divmod_nat_rel_ex:
  obtains q r where "divmod_nat_rel m n (q, r)"
proof (cases "n = 0")
  case True  with that show thesis
    by (auto simp add: divmod_nat_rel_def)
next
  case False
  have "\<exists>q r. m = q * n + r \<and> r < n"
  proof (induct m)
    case 0 with `n \<noteq> 0`
    have "(0::nat) = 0 * n + 0 \<and> 0 < n" by simp
    then show ?case by blast
  next
    case (Suc m) then obtain q' r'
      where m: "m = q' * n + r'" and n: "r' < n" by auto
    then show ?case proof (cases "Suc r' < n")
      case True
      from m n have "Suc m = q' * n + Suc r'" by simp
      with True show ?thesis by blast
    next
      case False then have "n \<le> Suc r'" by auto
      moreover from n have "Suc r' \<le> n" by auto
      ultimately have "n = Suc r'" by auto
      with m have "Suc m = Suc q' * n + 0" by simp
      with `n \<noteq> 0` show ?thesis by blast
    qed
  qed
  with that show thesis
    using `n \<noteq> 0` by (auto simp add: divmod_nat_rel_def)
qed

lemma unfolddiv: 
  assumes "(a::nat) \<ge>(b::nat)" 
      and "b>0" 
    shows "\<exists>n k . a = (b * n)+k  \<and> k<b"
proof-
  obtain n k  where 1:"divmod_nat_rel a b (n, k)" using divmod_nat_rel_ex by blast
  then have "a = (n*b)+k" using divmod_nat_rel_def by simp
  moreover have "0 \<le> k \<and> k < b \<and> 0 \<le> n" using divmod_nat_rel_def assms(2)using "1" by auto
  ultimately show ?thesis by (metis mult.commute)
qed

lemma obtainpoweroverlap: 
  assumes "(ys@xs) = (xs@zs)"  
      and "length xs \<ge>  length ys" 
      and "length ys > 0" 
    shows "\<exists>us n. ((power ys n)@us) = xs \<and> (length us < length ys)"
proof-
 obtain m k where length:  "length xs = ((length ys) * m) + k \<and> k<(length ys)" using unfolddiv assms(2)assms(3) by blast
  then have "take ((length ys) * m) xs = power ys m"using overlappower assms(1) assms(2) by blast
  then have "xs = power ys m@ drop ((length ys) * m) xs" by (metis append_take_drop_id)
  moreover have "length (drop ((length ys) * m) xs) < (length ys)" using length by simp 
  ultimately show ?thesis by metis
qed

lemma centrelength: 
  assumes "(ys@xs) = (xs@zs)"  
      and "length xs > length ys"  
    shows "cyclicp zs ys"
proof-
  have leq:"length ys = length zs" by (metis add_left_imp_eq assms(1) length_append length_rotate rotate_append)
  have eq: "(ys@xs) = (xs@zs)" using assms(1) by simp
  have length: "length xs > length ys" using assms(2) by simp
  then obtain us where bx:"(ys@us) = xs" using eq overlapleftexist by blast
   have "length xs > length ys" using length by auto
   then have xc: "(us@zs) = xs" using bx eq by fastforce
   then show ?thesis
   proof(cases "length us < length zs")
     case True
     then obtain ws where "ws@us = zs" by (metis bx overlaprightexist xc)
     moreover then have "us@ws = ys" using bx xc by auto
     ultimately show ?thesis using append_cyclicp by blast
next
  case False
  then have "length us \<ge> length zs" by simp
  then have F1:"length us \<ge> length ys" by (simp add: leq)
  have eq2: "ys@us = us@zs" by (simp add: bx xc)
  then show ?thesis
  proof(cases "length ys > 0")
    case True
    then obtain ts n where A:"power ys n @ ts = us \<and> length ts < length ys" using F1 eq2 obtainpoweroverlap[of "ys" "us" "zs"] by auto
    then show ?thesis
    proof(cases "n\<le>0")
      case True
      then have "n=0" by simp
      then have xz: "us = ts" using A by auto
      then obtain u1 where c:"zs = u1@ts" using A xc bx False leq by auto
      obtain u2 where "ys = ts@u2" using A xc bx False leq xz by auto
      moreover have "u1 = u2" using xc bx A False leq xz by auto
      ultimately have "ys = ts@u1" by simp
      then show ?thesis using c by (simp add: append_cyclicp)
    next
      case False
      then have n: "n>0" by auto
      then have "us = (power ys (n - 1))@ys@ts" using A powerrightappend by (metis append_assoc)
      then have o:"ys@(power ys (n - 1))@ys@ts = (power ys (n - 1))@ys@ts@zs" using eq2 by auto
      have "ys@(power ys (n - 1)) = (power ys n)" 
        by (metis power.simps(2) One_nat_def Suc_pred n)
      moreover have "(power ys (n - 1))@ys = (power ys n)" using n powerrightappend by auto
      ultimately have  "(power ys n)@ys@ts = (power ys n)@ts@zs" by (metis append.assoc o)
      then have o2: "ys@ts = ts@zs" by simp
      then obtain u1 where c:"zs = u1@ts" by (metis A leq overlaprightexist)
      obtain u2 where "ys = ts@u2" by (metis A o2 overlapleftexist)
      moreover then have "u1 = u2" using c o2 by auto
      ultimately have "ys = ts@u1" by simp
      then show ?thesis using c by (simp add: append_cyclicp)
qed
  next
    case False
    then have "ys=[]" by simp
    moreover then have "zs=[]" using leq by simp
    ultimately show ?thesis by (simp add: append_cyclicp)
  qed
qed
qed

lemma cyclicsym: 
  assumes "cyclicp xs ys" 
    shows "cyclicp ys xs"
proof-
  obtain i where i: "drop i xs @ take i xs = ys" using assms unfolding cyclicp_def cyclicp_at_i_def cycle_at_i_def by blast
  then have "take (length(drop i xs)) ys = drop i xs" by (metis append_eq_conv_conj)
  moreover have "drop (length(drop i xs)) ys = take i xs" using i  by (metis append_eq_conv_conj)
  ultimately have "drop (length(drop i xs)) ys @ take (length(drop i xs)) ys = xs" by simp
  then show ?thesis   unfolding cyclicp_def cyclicp_at_i_def cycle_at_i_def by blast
qed

lemma middleexist: 
  assumes "(xs@ys) = (zs@xs)" "length xs \<le> length zs" 
    shows "\<exists>us. (xs@us@xs) = (xs@ys)"
proof-
  obtain us where "zs = xs@us" using assms by (metis append_Nil2 append_eq_append_conv le_eq_less_or_eq overlapleftexist)
  then show ?thesis  by (simp add: assms(1))
qed

lemma middletermcycle:  
  assumes "(xs@ys) = (zs@xs)" 
    shows "cyclicp zs ys"
proof-
  obtain us ws where A:"(ws@us@ws) = (xs@ys) \<and> (ws@us@ws) = (zs@xs)" using assms middleterm[of "xs" "ys" "zs"] by blast
  then show ?thesis
  proof(cases "length ws > length xs")
    case True
    then obtain z1 where z1:"xs@z1 = ws" using A  by (metis append_eq_append_conv2 length_append not_add_less1) 
    moreover obtain z2 where z2: "z2@xs = ws" using A True  by (metis append.assoc overlaprightexist)
    ultimately have b:"(xs@ys) = xs@z1@us@z2@xs" using A by auto
    then have c:"(zs@xs) = xs@z1@us@z2@xs" using A by auto
    have "ys = (z1@us@z2)@xs" using b by auto
    moreover have "zs = xs@(z1@us@z2)" using c by auto
    ultimately show ?thesis by (simp add: append_cyclicp)
next
  case False
  then obtain z1 where z1:"ws@z1 = xs" using A overlapleftexist  by (metis append_eq_append_conv append_eq_append_conv2 nat_neq_iff)
  moreover obtain z2 where z2: "z2@ws = xs" using A False overlaprightexist    
    by (metis (no_types, opaque_lifting) append.assoc append.right_neutral nat_neq_iff rotate_append z1)
  have z12:"length z1 = length z2" by (metis diff_add_inverse diff_add_inverse2 length_append z1 z2)
  have bc:"length ys = length zs"  by (metis assms diff_add_inverse diff_add_inverse2 length_append)
    show ?thesis
  proof(cases "\<exists>ts. (xs@ts@xs) = (xs@ys)")
    case True
    then obtain ts where ts: "(xs@ts@xs) = (xs@ys)" by blast
    then have "ys = (ts@xs)" by simp
    moreover have "zs = (xs@ts)" using ts assms by simp
    ultimately show ?thesis by (simp add: append_cyclicp)
  next
    case False
    then have "length xs > length zs" using middleexist  assms not_le by blast
    then show ?thesis using centrelength by (metis assms cyclicsym)
  qed
qed
qed

lemma largestcancel: 
  assumes "reduced xs" 
      and "reduced ys" 
    shows "(\<exists> (us)(ws)(ts) . (us@ws) = 
                 xs \<and> ((wordinverse ws)@ts) = ys \<and> reduced(us@ts))"
  using assms
proof(induction xs  rule:reduced.induct)
  case 1
  have "reduced ys" using assms(2) by simp
  then show ?case by simp
next
  case (2 g)
  then show ?case
  proof(cases "ys = []")
    case True
    then show ?thesis by force
  next
    case False
    then show ?thesis
proof(cases "g = inverse (hd ys)")
    case True
    then have 1:"[(hd ys)] = wordinverse [g]" by (simp add: inverse_of_inverse)
    then have 2:"([hd ys] @ (tl ys)) = ys" using False hd_Cons_tl by fastforce
    have "reduced (tl ys)" using assms(2) 2 reduced_leftappend by metis
    then show ?thesis using 1 2 by force
  next
    case False
    then have "reduced ([g] @ ys)" using assms(2) append_reduced by (metis last_ConsL reduced.simps(2))
then show ?thesis using wordinverse.simps by blast
qed
  qed
next
  case (3 g h gs)
  then have rdh:"reduced (h#gs)" by (metis reduced.simps(3))
  moreover have gh:"g \<noteq> inverse h" using 3 by auto
  ultimately have "\<exists>a b c. a @ b = h # gs \<and> wordinverse b @ c = ys \<and> reduced (a @ c)" using assms(2) "3.IH" by blast
  then obtain a b c  where i:" a @ b = h # gs \<and> wordinverse b @ c = ys \<and> reduced (a @ c)"  by auto
  then have ga:"((g#a)@b) = g#h#gs" by simp
  then show ?case
  proof(cases "a = []")
    case True
    then have a: "a = []" by simp
    then have gb: "[g] @ b = g#h#gs" using ga by auto
    then have b:"b = h#gs"  by simp
    then have ib:"wordinverse b = (wordinverse gs)@[inverse h]"  by simp 
    have rc :"reduced c" using a i by auto
    then show ?thesis
    proof(cases "c = []")
case True
  then show ?thesis using a i ga by (metis  append_Nil2 ga reduced.simps(2))
next
  case False
  then have c:"c \<noteq> []" by simp
  then have "inverse h \<noteq> inverse (hd c)" using b rdh a  append_notreduced assms(2) i ib reduced_wordinverse  by (metis append.left_neutral snoc_eq_iff_butlast)
  then show ?thesis
  proof(cases "g = inverse (hd c)")
    case True
    have cc:"[(hd c)] @ (tl c) = c" using c by simp
      moreover have "wordinverse (g#h#gs) = (wordinverse gs)@[inverse h]@[inverse g]" using True by auto
      ultimately have "wordinverse (g#h#gs) @ (tl c) = ys" using i cc True ib inverse_of_inverse by (metis append.assoc)
      moreover have "reduced([]@(tl c))" using rc  assms(2) calculation reduced_leftappend by (metis append.left_neutral)
      ultimately show ?thesis  by blast
  next
    case False
    then have "reduced ([g]@c)" using rc  append_reduced by (metis last_ConsL reduced.simps(2))
    then show ?thesis using gb i by blast
  qed
qed
next
  case False
  then have "g \<noteq> inverse (hd a)" using  gh  i  by (metis hd_append2 list.sel(1))
  then have "reduced ([g]@a@c)" using False append_reduced i by (metis  hd_append2 last_ConsL reduced.simps(2))
  then have "reduced ((g#a)@c)" by auto
  then show ?thesis using i ga by blast
qed
qed

lemma wordinverseiterrel: 
  "wordinverse ((reduce^^(length a)) a) ~ wordinverse a"
proof-
  let ?b = "((reduce^^(length a)) a)"
  have 1:"a ~ ?b" by (simp add: cancels_imp_rel iter_cancels_to)
  have a: "(a @wordinverse a) ~ []" by (simp add: wordinverse_inverse)
  have b:"(?b@wordinverse?b) ~ []" by (simp add: wordinverse_inverse)
  have "(?b@wordinverse?b) ~ (a@wordinverse?b)" using 1 mult reln.sym by blast
  then have 1: "(wordinverse a@?b@wordinverse?b) ~ (wordinverse a@a@wordinverse?b)"  by (simp add: mult reln.refl)
  then have "(wordinverse a@?b@wordinverse?b) ~ (wordinverse a)" by (metis append.right_neutral b mult reln.refl)
  moreover have "(wordinverse a@a@wordinverse?b) ~ (wordinverse?b)" using inverse_wordinverse mult by fastforce
  ultimately show ?thesis using 1 reln.sym reln.trans by blast
qed

text \<open>Proving two cyclically reduced words that are conjugate are 
        cyclically equivalent.\<close>

lemma conj_red: 
  assumes "conj_rel S xs ys"
      and "cyclic_reduced xs" 
      and "cyclic_reduced ys" 
    shows "cyclicp xs ys"
proof-
  have uxs: "uncyclic xs" using assms(2) cyclic_reduced_def by auto
  have rxs: "reduced xs" using assms(2) cyclic_reduced_def by auto
  have uys: "uncyclic ys" using assms(3) cyclic_reduced_def by auto
  have rys: "reduced ys" using assms(3) cyclic_reduced_def by auto
  obtain a where 1: "a \<in>  \<langle>S\<rangle> \<and> (a @ xs @ (wordinverse a)) ~ ys" using assms(1) unfolding conj_rel_def by auto
  let ?b = "(reduce^^(length a)) a"
  have rb:"reduced ?b" by (simp add: reduced_iter_length)
  have sb:"?b \<in>  \<langle>S\<rangle>" using 1 iter_reduce_span by blast
  have "?b ~ a" by (simp add: cancels_imp_rel iter_cancels_to reln.sym)
  moreover have "(wordinverse ?b) ~ wordinverse a" using wordinverseiterrel by (simp add: wordinverseiterrel)
  ultimately have brela: "(?b @ xs @ (wordinverse ?b)) ~ (a @ xs @ (wordinverse a))" by (simp add: mult reln.refl)
  then have A: "(?b @ xs @ (wordinverse ?b)) ~ ys" using 1 using reln.trans by auto
  let ?x = "(?b @ xs @ (wordinverse ?b))"
  have rx:"reduced ((reduce^^(length ?x)) ?x)"  using reduced_iter_length by blast
  have "((reduce^^(length ?x)) ?x) ~ ys" using A using cancels_imp_rel iter_cancels_to reln.sym reln.trans by blast
  then have "cancels_eq ((reduce^^(length ?x)) ?x)  ys" by (simp add: reln_imp_cancels)
  then  have B:"(reduce^^(length ?x)) ?x = ys" using reduced_cancel_eq rys rx  by auto
  then show ?thesis
  proof(cases "reduced ?x")
    case True
    then have "(reduce^^(length ?x)) ?x = ?x" by (simp add: reduced_iter_eq)
    then have 1:"?x = ys" using B by auto
    then show ?thesis
    proof(cases "?b = []")
      case True
      then have "?x = xs" by simp
      then have "xs = ys" using 1 by simp
      then have "cycle_at_i xs 0 = ys" unfolding cycle_at_i_def by auto
  then show ?thesis unfolding cyclicp_def cyclicp_at_i_def by blast
next
      case False
      then have F: "?b \<noteq> []" by simp
      then show ?thesis
      proof(cases "length ?b = 1")
        case True
        then obtain ba where "?b = [ba]" using False
          by (metis One_nat_def add_diff_cancel_left' append_eq_Cons_conv plus_1_eq_Suc take0 take_last) 
        then have "?x = ([ba] @ xs @ [inverse ba])" by simp
        then have "ys = ([ba] @ xs @ [inverse ba])" using 1 by auto
        then have "ys = (ba#(xs @ [inverse ba]))" by simp
        moreover have "ba = inverse (last (xs @ [inverse ba]))" by (simp add: inverse_of_inverse)
        ultimately have False using  uys  uncyclic.simps(3) by (metis neq_Nil_conv snoc_eq_iff_butlast)
then show ?thesis  by simp
next
  case False
  then have ln: "length ?b > 1" using F  using nat_neq_iff by auto
  let ?ba = "hd ?b"
  have contr:"?ba = inverse ( last (wordinverse ?b))" using  ln F  hd_last_wordinverse by simp
  have ys:"ys = (?b @ xs @ wordinverse ?b)" using 1 by simp
  then have hd:"hd ys = ?ba" using F by auto
  moreover have "last ys = last (wordinverse ?b)" using ys F by (metis Nil_is_append_conv last_appendR wordinverse.simps(1) wordinverse_of_wordinverse)
  ultimately have contrr:"hd ys = inverse (last ys)" using contr by simp
  moreover have ls:"last ys = last (hd (tl ys)#(tl(tl ys)))" using hd ys F wordinverse.simps(2)  contrr by (metis Nil_is_append_conv last_ConsL last_tl list.collapse tl_append2)
  ultimately have "hd ys = inverse (last (hd (tl ys)#(tl(tl ys))))" by simp
  moreover then have "ys = (hd ys#hd (tl ys)#(tl(tl ys)))" using ys ln ls hd wordinverse.simps(2) by (metis F Nil_is_append_conv hd_Cons_tl last_ConsL tl_append2)
  ultimately have False using uys uncyclic.simps(3) by metis
  then show ?thesis by simp
qed
qed
next
  case False
  then have nredx: "\<not> reduced ?x" by blast
  then have red: "(reduced (?b@xs)) \<or> (reduced (xs@(wordinverse ?b)))" using rb assms(2) onesidenotcancel by (simp add: onesidenotcancel)
  then show ?thesis
  proof(cases "xs = []")
    case True
    then have "?x = ?b @ wordinverse ?b" by simp
    then have "?x ~ []"  by (simp add: wordinverse_inverse)
    then have "(reduce^^(length ?x)) ?x = []" using 1 B True  reduced.simps(1) reduced_cancel_eq reln.sym reln.trans reln_imp_cancels rys wordinverse_inverse by (metis append.left_neutral)
    then have "ys = xs" using B True by auto
    then have "cycle_at_i xs 0 = ys" using cycle_at_i_def by (simp add: cycle_at_i_def)
    then show ?thesis  unfolding cyclicp_def cyclicp_at_i_def by blast
next
  case False
  then have xsnnil:"xs \<noteq> []" by simp
  then have nred:"(\<not> reduced (?b@xs)) \<or> (\<not> reduced (xs@wordinverse?b))" using reduced_wordinverse rb rxs   nredx onesidecancel[of "?b" "xs" "wordinverse ?b"]  by blast
  then show ?thesis
  proof(cases "?b = []")
    case True
    then have "?x = xs" by simp
    then show ?thesis using nredx  rxs by auto
  next
    case False
    then have bnnil: "?b \<noteq> []" by simp
    then have ibnnil: "wordinverse ?b \<noteq> []"  by (metis wordinverse.simps(1) wordinverse_of_wordinverse)
    show ?thesis
    proof(cases "\<not> reduced (?b@xs)")
      case True
      then have "reduced (xs@wordinverse ?b)" using red by auto
      then have lsxs:"last xs \<noteq> inverse (hd (wordinverse ?b))" using rxs append_notreduced rb reduced_wordinverse False xsnnil by (metis wordinverse.simps(1) wordinverse_symm)
      obtain x y z where ob:"(x@y) = ?b \<and> ((wordinverse y)@z) = xs \<and> reduced(x@z)" using largestcancel[of "?b" "xs"] rxs rb by auto
      then have xsb:"?b@xs = (x@y@wordinverse y@z)" by simp
      have "(y@wordinverse y) ~ []" by (simp add: wordinverse_inverse)
      then have "(x@y@wordinverse y) ~ x"  by (metis append_Nil2 mult reln.refl)
      then have "(x@y@wordinverse y@z) ~ (x@z)"  using mult by fastforce
      then have xsbrel:"(?b@xs) ~ (x@z)" using xsb by simp
      then have "((?b@xs)@(wordinverse ?b)) ~ (x@z)@(wordinverse ?b)"using mult by blast
      moreover have "ys ~ (?b@xs)@(wordinverse ?b)"  by (simp add: A reln.sym)
      ultimately have ysrel: "ys ~ (x@z)@(wordinverse ?b)" using reln.trans by blast
      show ?thesis 
      proof(cases "z \<noteq> []")
        case True
        then have "last z  \<noteq> inverse (hd (wordinverse ?b))" using ob lsxs by auto
        then have "last (x@z) \<noteq> inverse (hd (wordinverse ?b))" using True by simp
        then have "reduced (x@z@(wordinverse ?b))" using ob rb append_reduced[of "(x@z)" "wordinverse ?b"] by (simp add: reduced_wordinverse)
        then have nys:"ys = (x@z@(wordinverse ?b))" using rys ysrel using reduced_cancel_eq reln_imp_cancels by auto
        then show ?thesis
        proof(cases "x\<noteq>[]")
         case True
          then have "hd ?b = hd x" using bnnil ob by (metis hd_append)
          then have "(hd x) = inverse (last (wordinverse ?b))" using hd_last_wordinverse[of "?b"] bnnil by simp
          then have "(hd ys) = inverse (last ys)" using nys by (simp add: True ibnnil)
          moreover have "length ys > 1" using True ibnnil nys using  rxs 
            by (metis Nil_is_append_conv \<open>hd x = FreeGroupMain.inverse (last (wordinverse ((reduce^^(length a)) a)))\<close> append.left_neutral diff_is_0_eq' hd_append2 inverse_not_refl last_appendR le_numeral_extra(4) length_0_conv less_one linorder_neqE_nat list.sel(1) take_eq_Nil take_last)
          ultimately have "\<not> uncyclic ys" using not_uncyclic  by blast
            then show ?thesis using uys by auto
        next
          case False
          then have "x = []" by simp
          then have "?b = y" using ob  by auto
          then have "wordinverse ?b = wordinverse y"  by simp
          then have "ys = z@(wordinverse y)" using nys using False by auto
          moreover have "xs = (wordinverse y)@z" using ob by simp
          ultimately show ?thesis  by (simp add: append_cyclicp) 
        qed
      next
        case False
        then have znil:"z = []" by simp
        then show ?thesis
        proof(cases "x = []")
          case True
          then have "ys ~ wordinverse ?b" using ysrel znil  by auto
          then have 1: "ys = wordinverse ?b" using rb reduced_wordinverse[of "?b"]reduced_cancel_eq reln_imp_cancels rys by auto
          have "?b = y" using True ob by simp
          then have "wordinverse ?b = wordinverse y"  by simp
          then have "xs = wordinverse ?b" using ob znil by simp
          then have "xs = ys" using 1 by simp
          then have "cycle_at_i xs 0 = ys" using cycle_at_i_def by (simp add: cycle_at_i_def)
          then show ?thesis  unfolding cyclicp_def cyclicp_at_i_def by blast
        next
          case False
          then have xnnil: "x \<noteq> []" by simp
          then have ysxb:"ys ~ x@wordinverse ?b" using znil ysrel by auto
          have xsy:"xs = wordinverse y" using znil ob by auto
          have lxb:"length x < length ?b" by (metis append_Nil2 append_eq_append_conv le_add1 length_append nat_less_le ob wordinverse_append xsnnil znil)
          obtain d e f where ob2:"(d@e) = x \<and> ((wordinverse e)@f) = wordinverse ?b \<and> reduced(d@f)" using largestcancel[of "x" "wordinverse ?b"] rb reduced_wordinverse[of "?b"] ob znil by auto
          then have fnnil:"f \<noteq> []" using lxb by (metis add_less_same_cancel2 append_Nil2 length_append less_nat_zero_code wordinverse_of_wordinverse)
          have xf:"hd x = inverse (last f)"  by (metis bnnil fnnil hd_append2 hd_last_wordinverse last_appendR length_greater_0_conv ob ob2 xnnil)
          have "(d@e @ (wordinverse e)) ~ d" by (metis append.right_neutral mult reln.refl wordinverse_inverse)
          then have "(d@e @ (wordinverse e)@f) ~ (d@f)"using mult by fastforce
          moreover have "ys ~ (d@e) @ ((wordinverse e)@f)" using ob2 ysxb by simp
          ultimately have "ys ~ (d@f)" using reln.trans by auto
          then have ysdf:"ys = (d@f)" using rys ob2  by (simp add: reduced_cancel_eq reln_imp_cancels)
          show ?thesis
          proof(cases "d\<noteq>[]")
            case True
            have "length d > 0" using True by simp
            moreover have "length f > 0" using fnnil by simp
            ultimately have lys:"length ys > 1" using ysdf by (metis append_eq_append_conv fnnil le_iff_add length_append less_one linorder_neqE_nat self_append_conv verit_comp_simplify1(3))
            have "hd d = hd x" using ob2 True  by force
            then have "hd d = inverse (last f)" using xf by simp
            then have "hd ys = inverse (last ys)" using ysdf True fnnil by auto
            then have "\<not> uncyclic ys"  using lys not_uncyclic by auto
            then show ?thesis using uys by blast
          next
            case False
            then have "?b = (e@y)" using ob ob2  by auto
            then have "wordinverse ?b = (wordinverse y) @ (wordinverse e)"by (simp add: wordinverse_append)
            moreover have "wordinverse ?b = (wordinverse e) @ f" by (simp add: ob2)
            ultimately have "cyclicp (wordinverse y) f " by (metis cyclicsym middletermcycle)
            then show ?thesis using False xsy ysdf by force
          qed
        qed
qed
next
  case False
 then have "reduced (?b@xs)" using red by auto
      then have lsxs:"last ?b \<noteq> inverse (hd (xs))" using rxs append_notreduced rb False xsnnil bnnil by auto
      obtain x y z where ob:"(x@y) = xs \<and> ((wordinverse y)@z) = wordinverse ?b \<and> reduced(x@z)" using largestcancel[of "xs" "wordinverse ?b"] rxs rb reduced_wordinverse by blast
      then have xsb:"xs@wordinverse ?b = (x@y@wordinverse y@z)" by simp
      have "(y@wordinverse y) ~ []" by (simp add: wordinverse_inverse)
      then have "(x@y@wordinverse y) ~ x"  by (metis append_Nil2 mult reln.refl)
      then have "(x@y@wordinverse y@z) ~ (x@z)"  using mult by fastforce
      then have xsbrel:"(xs@wordinverse ?b) ~ (x@z)" using xsb by simp
      then have "((?b@xs@wordinverse ?b)) ~ ?b@(x@z)"using mult by blast
      moreover have "ys ~ (?b@xs@wordinverse ?b)"  by (simp add: A reln.sym)
      ultimately have ysrel: "ys ~ ?b@(x@z)" using reln.trans by blast
      show ?thesis 
proof(cases "x \<noteq> []")
  case True
  then have xnnil: "x\<noteq>[]" by simp
        then have "hd x  \<noteq> inverse (last ?b)" by (metis hd_append2 inverse_of_inverse lsxs ob)
        then have "hd (x@z) \<noteq> inverse (last ?b)" using True by simp
        then have "reduced (?b@x@z)" using ob rb append_reduced[of "?b" "wordinverse (x@z)"] by (metis False True append.assoc onesidecancel reduced_leftappend reduced_rightappend)
        then have nys:"ys = (?b@x@z)" using rys ysrel using reduced_cancel_eq reln_imp_cancels by auto
        then show ?thesis
proof(cases "z\<noteq>[]")
          case True
          then have "last (wordinverse ?b) = last z" using bnnil ob by (metis last_append)
          then have "(hd ?b) = inverse (last z)" by (simp add: bnnil hd_last_wordinverse)
          then have "(hd ys) = inverse (last ys)" by (simp add: True bnnil nys)
          moreover have "length ys > 1" using bnnil True xnnil nys by (metis Nil_is_append_conv cancel_comm_monoid_add_class.diff_cancel length_greater_0_conv length_tl less_irrefl_nat less_one linorder_neqE_nat tl_append2)
          ultimately have "\<not> uncyclic ys" using not_uncyclic  by blast
            then show ?thesis using uys by auto
        next
          case False
          then have "z = []" by simp
          then have "wordinverse ?b = wordinverse y" using ob  by auto
          then have "?b =  y"  by (metis wordinverse_symm)
          then have "ys = y@x" using nys using False by auto
          moreover have "xs = x@y" using ob by simp
          ultimately show ?thesis  by (simp add: append_cyclicp) 
        qed
      next
        case False
        then have znil:"x = []" by simp
        then show ?thesis
        proof(cases "z = []")
          case True
          then have "ys ~ ?b" using ysrel znil  by auto
          then have 1: "ys =  ?b" using rb reduced_cancel_eq reln_imp_cancels rys by auto
          have "wordinverse ?b = wordinverse y" using True ob by simp
          then have "?b = y"   by (metis wordinverse_symm)
          then have "xs =  ?b" using ob znil by simp
          then have "xs = ys" using 1 by simp
          then have "cycle_at_i xs 0 = ys" using cycle_at_i_def by (simp add: cycle_at_i_def)
          then show ?thesis  unfolding cyclicp_def cyclicp_at_i_def by blast
        next
          case False
          then have xnnil: "z \<noteq> []" by simp
          then have ysxb:"ys ~ ?b@z" using znil ysrel by auto
          have xsy:"xs = y" using znil ob by auto
          have lxb:"length x < length ?b" by (simp add: bnnil znil)
          obtain d e f where ob2:"(d@e) = ?b \<and> ((wordinverse e)@f) = z \<and> reduced(d@f)" using largestcancel[of "?b" "z"] rb  ob znil by auto
          then have fnnil:"d \<noteq> []" using lxb by (metis append_self_conv2 length_append length_greater_0_conv less_add_same_cancel1 not_add_less2 ob wordinverse_append wordinverse_of_wordinverse xsnnil xsy)
          have xf:"hd d = inverse (last z)"  by (metis bnnil fnnil hd_append2 hd_last_wordinverse last_appendR length_greater_0_conv ob ob2 xnnil)
          have "(d@e @ (wordinverse e)) ~ d" by (metis append.right_neutral mult reln.refl wordinverse_inverse)
          then have "(d@e @ (wordinverse e)@f) ~ (d@f)"using mult by fastforce
          moreover have "ys ~ (d@e) @ ((wordinverse e)@f)" using ob2 ysxb by simp
          ultimately have "ys ~ (d@f)" using reln.trans by auto
          then have ysdf:"ys = (d@f)" using rys ob2  by (simp add: reduced_cancel_eq reln_imp_cancels)
          show ?thesis
          proof(cases "f\<noteq>[]")
            case True
            have "length f > 0" using True by simp
            moreover have "length d > 0" using fnnil by simp
            ultimately have lys:"length ys > 1" using ysdf by (smt (verit, ccfv_SIG) int_ops(2) length_append of_nat_0_less_iff of_nat_add of_nat_less_imp_less)
            then have "hd d = inverse (last z)" using xf by simp
            then have "hd d = inverse (last f)" using ob2 True by (metis last_appendR)
            then have "hd ys = inverse (last ys)" using ysdf True fnnil by auto
            then have "\<not> uncyclic ys"  using lys not_uncyclic by auto
            then show ?thesis using uys by blast
          next
            case False
            then have "wordinverse ?b = (wordinverse y@wordinverse e)" using ob ob2 by auto
            then have " ?b = e @ y"using wordinverse_append  wordinverse_of_wordinverse  by (metis)
            moreover have " ?b = d@e" by (simp add: ob2)
            ultimately have "cyclicp d y" by (metis middletermcycle) 
            then show ?thesis using False cyclicsym xsy ysdf by auto
          qed
        qed
      qed
    qed
  qed
qed
qed
qed

text \<open>Proving two cyclically reduced words are cyclically equivalent if and only if they are conjugate.\<close>

lemma CP_OnlyIf_Ex: 
  assumes "conj_rel S xs ys" 
    shows "cyclicp (cyclic_reduce xs) (cyclic_reduce ys)"
proof-
   have xs: "xs\<in>\<langle>S\<rangle>" using assms conj_rel_def by blast
   then have cxs:"conj_rel S xs (cyclic_reduce xs)" by (simp add: conj_cyclicreduce conj_rel_symm)
   have ys: "ys\<in>\<langle>S\<rangle>" using assms conj_rel_def by blast
   then have cys:"conj_rel S ys (cyclic_reduce ys)" by (simp add: conj_cyclicreduce conj_rel_symm)
   have "conj_rel S (cyclic_reduce xs) (cyclic_reduce ys)" using assms conj_cyclicreduce conj_rel_trans cys xs by blast
   moreover have "cyclic_reduced (cyclic_reduce xs) \<and> cyclic_reduced (cyclic_reduce ys)" by (simp add: cyclic_reduced_cyclic_reduce)
   ultimately show ?thesis using conj_red by blast
 qed

lemma CP_If_Ex: 
  assumes "xs\<in>\<langle>S\<rangle>" 
      and "ys\<in>\<langle>S\<rangle>"  
      and "cyclicp (cyclic_reduce xs) (cyclic_reduce ys)" 
    shows "conj_rel S xs ys"
proof-
  have cxs:"conj_rel S xs (cyclic_reduce xs)" using assms(1) by (simp add: conj_cyclicreduce conj_rel_symm)
  have cys:"conj_rel S ys (cyclic_reduce ys)" using assms(2) by (simp add: conj_cyclicreduce conj_rel_symm)
  have "conj_rel S (cyclic_reduce xs) (cyclic_reduce ys)" using assms(3) conj_cyclcip conj_rel_def cxs cys by blast
  then show ?thesis using conj_rel_symm conj_rel_trans cxs cys by blast
qed

subsection \<open>Showing a decision process exists by generating executable code in Haskell.\<close>

fun checkcycleeq :: "nat \<Rightarrow> ('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"checkcycleeq (Suc n) xs ys = ((cycle_at_i xs (Suc n) = ys) \<or> (checkcycleeq n xs ys))"
|"checkcycleeq 0 xs ys = (cycle_at_i xs 0 = ys)"

definition ccyclicp :: "('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where
"ccyclicp xs ys = checkcycleeq (length xs) xs ys"


value "ccyclicp [(((), (1::nat)),True)] [(((),1), True)]"
lemma Ex_Con: 
  assumes "cyclicp xs ys" 
    shows "ccyclicp xs ys"
proof-
  have "(\<exists>i. cycle_at_i xs i = ys)" using assms unfolding cyclicp_def cyclicp_at_i_def by blast
  then obtain i where i:"cycle_at_i xs i = ys" by blast
  then show ?thesis
  proof(cases "i < length xs")
    case False
    then have "cycle_at_i xs (length xs) = ys" using i unfolding cycle_at_i_def  by simp
then show ?thesis using ccyclicp_def checkcycleeq.simps(1) checkcycleeq.simps(2) by (metis not0_implies_Suc)
next
  case True
  then show ?thesis unfolding cyclicp_def cyclicp_at_i_def cycle_at_i_def  ccyclicp_def using  i
  proof(induction rule: checkcycleeq.induct)
    case (1 n x y)
    then show ?case
    proof(cases "n > i")
      case True
      then show ?thesis using 1 by auto
    next
      case False
      then have "n = i" using 1 by auto
      then have "checkcycleeq n x y" using 1 checkcycleeq.elims(3) by auto
      then show ?thesis by simp
    qed
  next
    case (2 x y)
    then show ?case  by auto
  qed
  qed
qed

lemma Con_Ex: 
  assumes "ccyclicp xs ys"
    shows "cyclicp xs ys"
  using assms unfolding ccyclicp_def
proof(induction rule:checkcycleeq.induct)
  case (1 n x y)
  then show ?case
  proof(cases "(cycle_at_i x (Suc n) = y)")
    case True
    then show ?thesis unfolding cyclicp_def cyclicp_at_i_def by auto
  next
    case False
    then have "checkcycleeq n x y" using 1 by auto
    then show ?thesis using 1 by simp
  qed
next
  case (2 x y)
  then have "(cycle_at_i x 0 = y)" by auto
  then show ?case unfolding cyclicp_def cyclicp_at_i_def by auto
qed

lemma eq_of_cyclicity: "ccyclicp xs ys = cyclicp xs ys"
  using Con_Ex Ex_Con by blast

lemma conj_rel_imp_ccylicp:
  assumes "conj_rel S xs ys" 
    shows "ccyclicp (cyclic_reduce xs) (cyclic_reduce ys)"
proof-
  show ?thesis using assms Ex_Con CP_OnlyIf_Ex by blast
qed

lemma ccylicp_imp_conj_rel: 
  assumes "xs\<in>\<langle>S\<rangle>" "ys\<in>\<langle>S\<rangle>"  
      and "ccyclicp (cyclic_reduce xs) (cyclic_reduce ys)"
    shows "conj_rel S xs ys"
proof-
  show ?thesis using assms Con_Ex CP_If_Ex by blast
qed

definition check_conj :: "('a, 'b) word \<Rightarrow> ('a, 'b) word \<Rightarrow> bool"
  where "check_conj xs ys = (ccyclicp (cyclic_reduce xs) (cyclic_reduce ys))"

lemma conjugacy_problem_on_span:
  assumes "xs\<in>\<langle>S\<rangle>" "ys\<in>\<langle>S\<rangle>"
    shows "conj_rel S xs ys \<longleftrightarrow>  check_conj xs ys"
  unfolding check_conj_def using ccylicp_imp_conj_rel[OF assms] conj_rel_imp_ccylicp
  by blast

definition(in group) conjugate::"'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
"conjugate xs ys \<equiv> (\<exists>zs \<in> (carrier G). zs \<otimes> xs \<otimes> inv zs = ys)"

text \<open>The following statement proves the decidability of conjugacy problem in Free 
Grooups.\<close>

theorem conjugacy_problem_in_freegroups:
  assumes "xs \<in> \<langle>S\<rangle>" "ys \<in> \<langle>S\<rangle>"
    shows "group.conjugate (freegroup S) (reln_tuple \<langle>S\<rangle>`` {xs}) (reln_tuple \<langle>S\<rangle>`` {ys}) 
        = check_conj xs ys"
proof
  let ?x = "(reln_tuple \<langle>S\<rangle>`` {xs})"
  let ?y = "(reln_tuple \<langle>S\<rangle>`` {ys})" 
  assume asm:"group.conjugate (freegroup S) ?x ?y"
  then obtain Z where Z:"Z \<in> carrier (freegroup S)" 
         "Z \<otimes>\<^bsub>freegroup S\<^esub> ?x \<otimes>\<^bsub>freegroup S\<^esub> (inv\<^bsub>freegroup S\<^esub> Z) = ?y" 
    unfolding group.conjugate_def 
    by (meson freegroup_is_group group.conjugate_def)   
  then obtain z0 where z0:"z0 \<in> \<langle>S\<rangle>" "Z = reln_tuple \<langle>S\<rangle> `` {z0}"
    by (metis freegroup_def partial_object.simps(1) quotientE)
  have inv_wordinv:"(inv\<^bsub>freegroup S\<^esub> Z) = reln_tuple \<langle>S\<rangle> `` {wordinverse z0}" 
    using group.wordinverse_inv[OF freegroup_is_group Z(1) z0(2)] .
  have wordinv_in:"wordinverse z0 \<in> \<langle>S\<rangle>" using z0(1) 
    by (simp add: span_wordinverse)
  moreover have z0_x_in:"z0@xs \<in> \<langle>S\<rangle>" using z0(1) assms(1) 
    using freewords_on_def span_append by blast
  from z0(2) Z(2) have "Z \<otimes>\<^bsub>freegroup S\<^esub> ?x \<otimes>\<^bsub>freegroup S\<^esub> (inv\<^bsub>freegroup S\<^esub> Z)
               = reln_tuple \<langle>S\<rangle> `` {z0@xs@(wordinverse z0)}" 
    using proj_append_wd[OF z0_x_in wordinv_in] freegroup_def[of S] inv_wordinv
    by (metis  append_assoc assms(1) monoid.select_convs(1) proj_append_wd z0(1))
  with Z(2) have "(z0@xs@(wordinverse z0)) ~ ys" using assms z0(1)
  proof-
    have 1:"(z0@xs@(wordinverse z0)) \<in> \<langle>S\<rangle>" using z0_x_in wordinv_in 
      by (metis assms(1) freewords_on_def span_append z0(1))
    thus ?thesis using Word_Problem.word_problem_eq[OF 1 assms(2)] iter_imp_cancels
        cancels_eq_imp_reln 
      by (metis \<open>Z \<otimes>\<^bsub>F\<^bsub>S\<^esub>\<^esub> reln_tuple \<langle>S\<rangle> `` {xs} \<otimes>\<^bsub>F\<^bsub>S\<^esub>\<^esub> inv\<^bsub>F\<^bsub>S\<^esub>\<^esub> Z = reln_tuple \<langle>S\<rangle> `` {z0 @ xs @ wordinverse z0}\<close> Z(2))
  qed
  thus "check_conj xs ys" using conjugacy_problem_on_span[OF assms] unfolding conj_rel_def 
    using assms z0(1) by blast
next
  let ?x = "(reln_tuple \<langle>S\<rangle>`` {xs})"
  let ?y = "(reln_tuple \<langle>S\<rangle>`` {ys})" 
  assume "check_conj xs ys"
  then obtain z0 where z0:"z0 \<in> \<langle>S\<rangle>" "(z0 @ xs @ wordinverse z0) ~ ys"
    using conjugacy_problem_on_span[OF assms] unfolding conj_rel_def by blast
  hence reln_tuple_eq:"reln_tuple \<langle>S\<rangle> `` {z0 @ xs @ wordinverse z0} = reln_tuple \<langle>S\<rangle> `` {ys}"
    by (smt (verit, ccfv_threshold) assms(1) assms(2) cancels_imp_iter freewords_on_def reln_imp_cancels span_append span_wordinverse word_problem_eq)
  let ?z =  "reln_tuple \<langle>S\<rangle> `` {z0}"
  have z_in:"?z \<in> carrier (freegroup S)" using z0(1) 
    by (simp add: freegroup_def quotientI)
  have inv_is:"inv\<^bsub>freegroup S\<^esub> ?z = reln_tuple \<langle>S\<rangle> `` {wordinverse z0}"
    by (meson freegroup_is_group group.wordinverse_inv z_in)
  have "reln_tuple \<langle>S\<rangle> `` {z0 @ xs @ wordinverse z0}
          = reln_tuple \<langle>S\<rangle> `` {z0 @ xs}\<otimes>\<^bsub>freegroup S\<^esub> reln_tuple \<langle>S\<rangle> `` {wordinverse z0}"
    using z0(1) assms(1) 
    by (metis append.assoc freegroup_def freewords_on_def monoid.select_convs(1) proj_append_wd span_append span_wordinverse)
  moreover have "reln_tuple \<langle>S\<rangle> `` {z0 @ xs}  = reln_tuple \<langle>S\<rangle> `` {z0}\<otimes>\<^bsub>freegroup S\<^esub> reln_tuple \<langle>S\<rangle> `` {xs}"
    using z0(1) assms(1) 
    by (simp add: freegroup_def proj_append_wd)
  ultimately have "(reln_tuple \<langle>S\<rangle> `` {z0})\<otimes>\<^bsub>freegroup S\<^esub>?x \<otimes>\<^bsub>freegroup S\<^esub> reln_tuple \<langle>S\<rangle> `` {wordinverse z0}
                   = ?y"
    using reln_tuple_eq by auto  
  thus "group.conjugate (freegroup S) ?x ?y" 
    using group.conjugate_def[OF "freegroup_is_group"] z_in inv_is by fastforce
qed
   
export_code check_conj in Haskell
module_name CP file_prefix cp

end


