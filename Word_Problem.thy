theory Word_Problem
  imports FreeGroupMain Generators Cancellation 
          
begin


text\<open>reduce xs returns xs with the first instance of an element and its inverse 
      occurring next to each other removed.\<close>

fun reduce :: "('a,'b) word \<Rightarrow> ('a,'b) word"
  where
"reduce [] = []"|
"reduce [x] = [x]"|
"reduce (x#y#xs) = (if (x = inverse y) 
                           then xs 
                           else (x#(reduce (y#xs))))"

text \<open>Some lemmas that required to show that 
      if two words iterated by reduce by their length are equal
      then they are related by cancels_eq\<close>

lemma cons_reduce: 
  assumes "x \<noteq> inverse y" 
  shows "reduce (x#y#xs) = (x#(reduce (y#xs)))"
  by (simp add: assms)

lemma cancel_at_cons:
  assumes "i\<ge>0" 
      and "(1+i) < length xs" 
      and "cancel_at i xs = ys"
    shows "cancel_at (1 + i) (z#xs) = (z#ys)"
proof-
  have "z#(take i xs) = take (1 + i) (z#xs)" using assms(1) assms(2) by auto
  moreover have "drop (i+2) xs = drop (1 + (i+2)) (z#xs)"using assms(1) assms(2) by simp
  ultimately show ?thesis unfolding cancel_at_def by (metis (no_types, lifting) add.commute append_Cons assms(3) cancel_at_def group_cancel.add2)
qed

lemma cancels_to_1_at_cons:
  assumes "i\<ge>0" "(1+i) < length xs" 
      and "cancels_to_1_at i xs ys"
    shows "cancels_to_1_at (1 + i) (z#xs) (z#ys)"
  unfolding cancels_to_1_at_def
proof-
  have 1:"0 \<le> (1 + i)" using assms(1) by simp
  moreover have 2: "1 + (1 + i) < length (z # xs)" using assms(2) by auto
  have "(inverse (xs ! i)) = (xs ! (i+1))" using assms(3) by (metis add.commute cancels_to_1_at_def)
  moreover then have 3: "inverse ((z # xs) ! (1 + i)) = (z # xs) ! (1 + (1 + i))" by simp
  have "(ys = cancel_at i xs)" using assms(3)using cancels_to_1_at_def by auto
  moreover then have 4: "z # ys = cancel_at (1 + i) (z # xs)" using cancel_at_cons assms(1) assms(2) by metis
  ultimately show "0 \<le> 1 + i \<and>
    1 + (1 + i) < length (z # xs) \<and>
    inverse ((z # xs) ! (1 + i)) = (z # xs) ! (1 + (1 + i)) \<and>
    z # ys = cancel_at (1 + i) (z # xs)" using "2" "3" by blast
qed

lemma cancels_to_1_cons:
  assumes "cancels_to_1 xs ys"
  shows "cancels_to_1 (z#xs) (z#ys)"
  using assms
  unfolding cancels_to_1_def
proof-
  obtain i where 1:"cancels_to_1_at i xs ys" using assms cancels_to_1_def by auto
  then have "i\<ge>0 \<and> (1+i) < length xs" using cancels_to_1_at_def by auto
  then have "cancels_to_1_at (1 + i) (z#xs) (z#ys)" using 1 cancels_to_1_at_cons by blast
  then show "\<exists>i. cancels_to_1_at i (z # xs) (z # ys)" by auto
qed

lemma cons_cancel_at: 
  "cancels_to xs ys \<longrightarrow> cancels_to (x#xs) (x#ys)"
  unfolding cancels_to_def
  apply(rule impI)
proof(induction rule: rtranclp.induct)
  case (rtrancl_refl a)
  then show ?case by simp
next
  case (rtrancl_into_rtrancl a b c)
  then have "cancels_to_1 b c" by simp
  then have "cancels_to_1 (x#b) (x#c)" by (simp add: cancels_to_1_cons)
  then show ?case using rtrancl_into_rtrancl.IH by auto 
qed

lemma cancels_to_reduce:
  "cancels_to xs (reduce xs)"
proof(induction xs rule: reduce.induct)
  case 1
  then have "cancels_to [] []"  unfolding cancels_to_def by simp
  then show ?case by simp
next
  case (2 x)
  then have "cancels_to [x] [x]"  unfolding cancels_to_def by simp
  then show ?case by simp
next
  case (3 x y xs)
  then show ?case
  proof (cases "x = inverse y")
    case True
    have a: "(reduce (x # y # xs)) = xs" using True by simp
    then have 1: "reduce (x # y # xs) = cancel_at 0 (x # y # xs)" by (simp add: cancel_at_def)
    have 2: "(inverse ((x # y # xs) ! 0) = ((x # y # xs) ! (1 + 0)))" using True by (metis inverse_of_inverse nth_Cons_0 nth_Cons_Suc plus_1_eq_Suc)
    have "cancels_to_1_at 0 (x # y # xs) (reduce (x # y # xs))" using cancels_to_1_at_def using "1" "2" by fastforce
    then have "cancels_to_1 (x # y # xs) (reduce (x # y # xs))" using cancels_to_1_def by blast
    then show ?thesis by (simp add: cancels_to_def)
next
  case False
  then have "cancels_to (y # xs) (reduce (y # xs))" by (simp add: "3.IH")
  then have "cancels_to (x # y # xs) (x#(reduce (y # xs)))" by (simp add: cons_cancel_at)
    then show ?thesis using False by (simp add: cons_reduce)
    qed
  qed

lemma iter_cancels_to: "cancels_to xs ((reduce^^n) xs)"
proof(induction n)
  case 0
  have "((reduce^^0) xs) = xs" by simp
  then show ?case unfolding cancels_to_def by simp
next
  case (Suc n)
  then have 1: "cancels_to xs ((reduce^^n) xs)" by auto
  have "((reduce^^(Suc n)) xs) = reduce ((reduce^^n) xs)" by simp
  moreover have "cancels_to ((reduce^^n) xs) (reduce ((reduce^^n) xs))" using cancels_to_reduce by auto
  ultimately have "cancels_to ((reduce^^n) xs) ((reduce^^(Suc n)) xs)" by simp
  then show ?case using 1 unfolding cancels_to_def by auto
qed

lemma cons_reduced:
  assumes "x \<noteq> inverse y"
    shows "reduced (y # xs) \<Longrightarrow> reduced (x#y#xs)"
  using assms
proof-
  assume a: "reduced (y#xs)"
  have "reduced (x#y#xs) = reduced (y#xs)" using assms by simp
  then show ?thesis by (simp add: a)
qed

lemma cons_not_reduced: 
  assumes "x \<noteq> inverse y"
    shows "\<not> reduced (x # y # xs) \<Longrightarrow> \<not> reduced (y # xs)"
  using assms
proof-
  assume a: "\<not> reduced (x # y # xs)"
  have "reduced (y # xs) \<Longrightarrow> reduced (x # y # xs)" using assms cons_reduced by simp
  then show ?thesis using a by blast
qed

lemma reduce_minus: 
  assumes "\<not> (reduced xs)"
    shows "length (reduce xs) = (length xs) - 2"
  using assms
proof(induction xs rule: reduce.induct)
  case 1
then show ?case by simp
next
  case (2 x)
  then have a: "\<not> reduced [x]" by blast
  have "reduced [x]" by auto
  then show ?case using a by blast
next
case (3 x y xs)
  then show ?case
  proof(cases "x = inverse y")
    case True
    then have "reduce (x # y # xs) = xs" by simp
then show ?thesis by simp
next
  case False
  then have 1: "\<not> reduced (y # xs)" using cons_not_reduced "3.prems" by auto
  then have a: "length (reduce (y # xs)) = length (y # xs) - 2" using "3.IH" False by blast
  have b: "length (y # xs)  = length (x # y # xs) - 1" by auto
  have 2:"reduce (x # y # xs) = x#(reduce (y # xs))" using False by simp
  moreover have "length (x#(reduce (y # xs))) - 1 = length (reduce (y # xs))" by simp
  ultimately have c: "length (reduce (y # xs)) = length (reduce (x # y # xs)) - 1" by simp
  then have " length (reduce (x # y # xs)) - 1 = (length (x # y # xs) - 1) - 2" using a b c by argo
  then have "length (reduce (x # y # xs)) - 1 = length (x # y # xs) - 2 - 1" by simp
  then show ?thesis  by (smt (verit, ccfv_SIG) "1" "2" BNF_Greatest_Fixpoint.length_Cons Suc_1 diff_Suc_1 diff_Suc_eq_diff_pred reduced.elims(3))
  qed
qed

lemma reduced_reduce: 
  assumes "reduced xs"
    shows "reduce xs = xs"
  using assms
proof(induction xs rule: reduce.induct)
  case 1
  then have "reduce [] = []" by simp
then show ?case by simp 
next
  case (2 x)
  then have "reduce [x] = [x]" by simp
  then show ?case by simp
next
  case (3 x y xs)
  then have 1: "x \<noteq> inverse y" by auto
  then moreover have "reduced (y # xs)" using cons_reduced "3.prems" by simp
  ultimately have "reduce (y # xs) = (y # xs)" using "3.IH" by blast
  then have "x#(reduce (y # xs)) = (x # y # xs)" by simp
  moreover have "reduce (x # y # xs) = (x#reduce (y # xs))" using 1  by simp
  ultimately show ?case by simp
qed

lemma reduced_imp_reduce: 
  "reduced xs \<Longrightarrow> reduced (reduce xs)"
proof-
  assume assms: "reduced xs"
  then have "reduce xs = xs" using reduced_reduce by auto
  then show ?thesis using assms by simp
qed

lemma length_reduce:
  "length (reduce xs) \<le> length xs"
proof(induction xs rule: reduce.induct)
case 1
  then show ?case by simp
next
case (2 x)
  then show ?case by simp
next
  case (3 x y xs)
  then show ?case 
  proof(cases "x = inverse y")
    case True 
    then show ?thesis using 3 by force
  next
    case False
    then show ?thesis using 3 by auto 
 qed  
qed

lemma length_reduce_iter:  
  "length ((reduce^^n) xs) \<le> length xs"
proof(induction n)
  case 0
  then have "((reduce^^0) xs) = xs" by simp
  then show ?case by simp
next
  case (Suc n)
  have "reduce ((reduce^^n) xs) = ((reduce^^(Suc n)) xs)" by simp
  moreover have "length (reduce ((reduce^^n) xs)) \<le> length ((reduce^^n) xs)" using length_reduce by fast
 ultimately have "length (reduce ((reduce^^n) xs)) \<le> length ((reduce^^n) xs)" by simp
  then show ?case using Suc.IH by simp
qed

lemma reduce_iter_minus: 
  assumes "\<not> reduced ((reduce^^n) xs)"
    shows "length ((reduce^^n) xs) = length xs - (2*n)"
  using assms
proof(induction n)
  case 0
  have 1: "length xs - 2 * 0 = length xs" by simp
  have 2: "((reduce^^0) xs) = xs" by simp
  then show ?case using 1 2 by simp
next
  case (Suc n)
  then have "\<not> reduced ((reduce^^(Suc n)) xs)" by simp
  moreover have b: "((reduce^^(Suc n)) xs) = reduce ((reduce^^n) xs)" by simp
  ultimately have a: "\<not> reduced ((reduce^^n) xs)" using reduced_imp_reduce by auto
  then have " length ((reduce^^n) xs) = length xs - (2 * n)" using Suc.IH by auto
  then have c: "length ((reduce^^n) xs) - 2 = length xs - (2 * n) - 2" by simp
  have "length ((reduce^^n) xs) - 2 = length ((reduce^^(Suc n)) xs)" using a b reduce_minus by (simp add: reduce_minus)
  moreover have "length xs - (2 * n) - 2 = length xs - (2 * Suc n)" by simp
  ultimately show ?case using c  by presburger
qed

lemma 
  assumes "\<not> reduced xs"
    shows "length (reduce xs) < length xs"
  using assms
proof(induction xs rule:reduce.induct)
  case 1
  then have "reduced []" by simp
  then show ?case using "1.prems" by simp
next
  case (2 x)
  then have "reduced [x]" by simp
  then show ?case using "2.prems" by simp
next
  case (3 x y xs)
  have "length (x # y # xs) > 0" by simp
  then show ?case using reduce_minus "3.prems" by force
qed

lemma not_reduced_iter: 
  assumes "reduced ((reduce^^n) xs)"
    shows "reduced ((reduce^^(n+1)) xs)"
  using assms
proof-
  have "((reduce^^(n+1)) xs) = reduce ((reduce^^n) xs)" by simp
  then show ?thesis by (simp add: reduced_imp_reduce assms)
qed

lemma reduced_iter_suc: 
  assumes "reduced ((reduce^^n) xs)"
    shows "reduced ((reduce^^(n+k)) xs)"
  using assms
proof(induction k)
case 0
then show ?case by simp
next
  case (Suc k)
  then have "reduced ((reduce^^(n + k)) xs)" by simp
  then show ?case using  reduced_imp_reduce by auto
qed

lemma not_reduced_iter_suc: 
  assumes "\<not> reduced ((reduce^^n) xs)" "(k::nat) \<le> n"
    shows "\<not> reduced ((reduce^^k) xs)"
proof-
  show ?thesis using reduced_iter_suc  using assms(1) assms(2) le_Suc_ex by blast
qed

lemma reduced_iter_length: 
  "reduced ((reduce^^(length xs)) xs)"
proof(induction xs)
  case Nil
then have "((reduce^^(length [])) []) = []" by simp
  then show ?case by simp
next
  case (Cons a xs)
  have 2: "(((length (a#xs) div 2 + 1))* 2) \<ge> length (a#xs)" by (simp add: nonzero_mult_div_cancel_right)
  have "length (a # xs) > 0" by simp
  then have 1:"length (a # xs) div 2 + 1 \<le> length (a#xs)" by (meson discrete div_less_dividend one_less_numeral_iff semiring_norm(76))
  then show ?case 
  proof(cases "\<not>reduced ((reduce^^(length (a # xs))) (a # xs))")
    case True
  then have a: "\<not>reduced ((reduce^^(length (a # xs))) (a # xs))" by simp
  then have cont:"\<not>reduced ((reduce^^(length (a # xs) div 2 + 1)) (a # xs))" 
    using not_reduced_iter_suc 1 by blast
  then have "length ((reduce^^(length (a # xs) div 2 + 1)) (a # xs)) = length (a#xs) - (((length (a#xs) div 2 + 1))* 2)" using reduce_iter_minus by (metis mult.commute)
  then have "length ((reduce^^(length (a # xs) div 2 + 1)) (a # xs)) = 0" using "2" diff_is_0_eq by presburger
  then have "((reduce^^(length (a # xs) div 2 + 1)) (a # xs)) = []" by simp
  then have "reduced ((reduce^^(length (a # xs) div 2 + 1)) (a # xs))" by simp
   then show ?thesis using cont by blast
  next
    case False
    then show ?thesis by simp
  qed
qed

text \<open>Now we show that cancels_eq xs ys is equivalent to (reduce^^(length xs)) xs = (reduce^^(length ys)) ys,
      and also relating them to ~.\<close>

lemma iter_imp_cancels: 
  assumes "(reduce^^(length xs)) xs = (reduce^^(length ys)) ys"
    shows "cancels_eq xs ys"
proof-
  have "cancels_to xs ((reduce^^(length xs)) xs)" using iter_cancels_to by auto
  then have a: "cancels_eq  xs ((reduce^^(length xs)) xs)" unfolding cancels_eq_def by blast
  have "cancels_to ys ((reduce^^(length ys)) ys)" using iter_cancels_to by auto
  then have b: "cancels_eq ((reduce^^(length ys)) ys) ys" unfolding cancels_eq_def by blast
  then show ?thesis using a b unfolding cancels_eq_def using assms by auto
qed

lemma cancels_imp_iter: 
  assumes "cancels_eq xs ys"
    shows "(reduce^^(length xs)) xs = (reduce^^(length ys)) ys"
proof-
  have "cancels_to xs ((reduce^^(length xs)) xs)" using iter_cancels_to by auto
  then have "cancels_eq  ((reduce^^(length xs)) xs) xs" unfolding cancels_eq_def by blast
  then have a: "cancels_eq ((reduce^^(length xs)) xs) ys" using assms unfolding cancels_eq_def by auto
  have "cancels_to ys ((reduce^^(length ys)) ys)" using iter_cancels_to by auto
  then have b: "cancels_eq ys ((reduce^^(length ys)) ys)" unfolding cancels_eq_def by blast
  have rel: "cancels_eq ((reduce^^(length xs)) xs)  ((reduce^^(length ys)) ys)"  using a b 
    unfolding cancels_eq_def by auto
  have x: "reduced ((reduce^^(length xs)) xs)" using reduced_iter_length by blast
  have y:  "reduced ((reduce^^(length ys)) ys)" using reduced_iter_length by blast
  then show ?thesis using rel x y reduced_cancel_eq by blast
qed

lemma cancels_eq_imp_reln:
  "cancels_eq xs ys \<Longrightarrow> xs ~ ys"
  unfolding cancels_eq_def 
  using cancels_imp_iter[of "xs" "ys"] iter_cancels_to[of "xs" "length xs"] cancels_imp_rel[of "xs" "ys"] 
  by (metis cancels_eq_def cancels_imp_rel iter_cancels_to reln.sym reln.trans)

text\<open>Here, we prove some lemmas about ~ and free group elements needed to
     give a solution to the word problem.\<close>

lemma word_problem_not_eq:
  assumes "xs \<in> \<langle>S\<rangle>" 
      and "ys \<in> \<langle>S\<rangle>"
      and "\<not> (xs ~ ys)"
    shows "reln_tuple \<langle>S\<rangle> `` {xs} \<noteq> reln_tuple \<langle>S\<rangle> `` {ys} "
  using assms unfolding reln_tuple_def by blast

lemma word_problem_not_eq_id:
  assumes "xs \<in> \<langle>S\<rangle>" 
    and "\<not> (xs ~ [])"
  shows "reln_tuple \<langle>S\<rangle> `` {xs} \<noteq> \<one>\<^bsub>(freegroup S)\<^esub> "
  using assms word_problem_not_eq[of "xs" ] 
  by (metis freegroup_def freewords_on_def monoid.select_convs(2) words_on.intros(1))

lemma 
  assumes "xs \<in> \<langle>S\<rangle>" "ys \<in> \<langle>S\<rangle>"
    shows "reln_tuple \<langle>S\<rangle> `` {xs @ ys} = reln_tuple \<langle>S\<rangle> `` {xs} \<otimes>\<^bsub>freegroup S\<^esub> reln_tuple \<langle>S\<rangle> `` {ys}"
  using assms proj_append_wd[OF assms]
  by (simp add: freegroup_def)

lemma reln_tuple_eq:
  assumes "xs \<in> \<langle>S\<rangle>" 
  shows "reln_tuple \<langle>S\<rangle> `` {xs} = monoid.m_concat (freegroup S)  (map (\<lambda>ys. (reln_tuple \<langle>S\<rangle> `` {[ys]})) xs)"
  using assms 
proof(induction xs)
  case (Cons a xs)
  let ?l =  "monoid.m_concat (freegroup S)  (map (\<lambda>ys. (reln_tuple \<langle>S\<rangle> `` {[ys]})) (xs))"
  have "[a] \<in> \<langle>S\<rangle>" 
    using cons_span Cons freewords_on_def by blast
  have " (\<lambda>ys. (reln_tuple \<langle>S\<rangle> `` {[ys]})) a = reln_tuple \<langle>S\<rangle> `` {[a]}" by simp
  have "monoid.m_concat (freegroup S)  (map (\<lambda>ys. (reln_tuple \<langle>S\<rangle> `` {[ys]})) (a#xs))
            =   reln_tuple \<langle>S\<rangle> `` {[a]} \<otimes>\<^bsub>freegroup S\<^esub> ?l"
    by simp
  moreover have "reln_tuple \<langle>S\<rangle> `` {xs} = ?l" using Cons 
    using freewords_on_def span_cons by blast 
  ultimately have 1:"monoid.m_concat (freegroup S)  (map (\<lambda>ys. (reln_tuple \<langle>S\<rangle> `` {[ys]})) (a#xs))
          = (reln_tuple \<langle>S\<rangle> `` {[a]}) \<otimes>\<^bsub>freegroup S\<^esub> (reln_tuple \<langle>S\<rangle> `` {xs})"
    by argo
  hence 2:"... =  (reln_tuple \<langle>S\<rangle> `` {[a]@xs})" using proj_append_wd Cons freegroup_def 
    by (metis \<open>[a] \<in> \<langle>S\<rangle>\<close> freewords_on_def monoid.select_convs(1) span_cons)
  hence 3:"... = (reln_tuple \<langle>S\<rangle> `` {a#xs})" by auto
  then show ?case using 1 2 by argo
qed(simp add: freegroup_def)

text\<open>We use the lemmas equating the different relations
      and those shown above to give a solution to the word problem. The following 
lemma is a formal statement of the word problem\<close>

theorem word_problem_eq:
  assumes "xs \<in> \<langle>S\<rangle>" "ys \<in> \<langle>S\<rangle>"
    shows "(reln_tuple \<langle>S\<rangle> `` {xs}) = (reln_tuple \<langle>S\<rangle> `` {ys}) 
          \<longleftrightarrow> (reduce^^(length xs)) xs = (reduce^^(length ys)) ys"
proof
  assume "reln_tuple \<langle>S\<rangle> `` {xs} = reln_tuple \<langle>S\<rangle> `` {ys}"
  hence "xs ~ ys" using assms 
    by (meson word_problem_not_eq)
  hence "cancels_eq xs ys" using assms reln_imp_cancels by blast
  thus "(reduce^^(length xs)) xs = (reduce^^(length ys)) ys" using cancels_imp_iter[of xs ys] by argo
next
  assume "(reduce^^(length xs)) xs = (reduce^^(length ys)) ys"
  hence "cancels_eq xs ys" using iter_imp_cancels[of xs ys] by argo
  hence "xs ~ ys" using assms 
    by (simp add: cancels_eq_imp_reln)
  thus "(reln_tuple \<langle>S\<rangle> `` {xs}) = (reln_tuple \<langle>S\<rangle> `` {ys})" using assms  
    by (metis (mono_tags, lifting) case_prodI equiv_class_eq mem_Collect_eq reln_equiv reln_tuple_def)
qed

text \<open>Some of the trivial consequences of the word problem are below \<close>

lemma word_problem_neq:
  assumes "xs \<in> \<langle>S\<rangle>"
      and "(reln_tuple \<langle>S\<rangle> `` {xs}) \<noteq> \<one>\<^bsub>freegroup S\<^esub>"
    shows "(reduce^^(length xs)) xs \<noteq> []"
  using word_problem_eq assms freegroup_def freewords_on_def 
  by (metis bot.extremum_uniqueI le0 length_greater_0_conv length_reduce_iter list.size(3) monoid.select_convs(2) words_on.empty)

lemma word_problem_notrel:
  assumes "xs \<in> \<langle>S\<rangle>"
      and "(reln_tuple \<langle>S\<rangle> `` {xs}) \<noteq> \<one>\<^bsub>freegroup S\<^esub>"
    shows "\<not> ((reduce^^(length xs)) xs ~ [])"
  using  assms word_problem_neq 
    reduced.simps(1) reduced_cancel_eq reduced_iter_length reln_imp_cancels by metis

lemma "xs ~ (reduce^^(length xs)) xs" 
  by (simp add: cancels_imp_rel iter_cancels_to)

definition normal_form::"('a,'b) word \<Rightarrow> ('a,'b) word"
  where
"normal_form xs = ((reduce^^(length xs)) xs)"

export_code normal_form in Haskell
module_name WP file_prefix Wp

end