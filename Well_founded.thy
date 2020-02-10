theory Well_founded
  imports Main
begin

locale well_founded =
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 70)
  assumes
    wf: "wfP (\<sqsubset>)"
begin

lemmas induct = wfP_induct_rule[OF wf]

end

section \<open>Lexicographic product\<close>

context
  fixes
    r1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    r2 :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
begin

definition lex_prodp :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "lex_prodp x y \<equiv> r1 (fst x) (fst y) \<or> fst x = fst y \<and> r2 (snd x) (snd y)"

lemma lex_prodp_lex_prod:
  shows "lex_prodp x y \<longleftrightarrow> (x, y) \<in> lex_prod { (x, y). r1 x y } { (x, y). r2 x y }"
  by (auto simp: lex_prod_def lex_prodp_def)

lemma lex_prodp_wfP:
  assumes
    "wfP r1" and
    "wfP r2"
  shows "wfP lex_prodp"
proof (rule wfPUNIVI)
  show "\<And>P. \<forall>x. (\<forall>y. lex_prodp y x \<longrightarrow> P y) \<longrightarrow> P x \<Longrightarrow> (\<And>x. P x)"
  proof -
    fix P
    assume "\<forall>x. (\<forall>y. lex_prodp y x \<longrightarrow> P y) \<longrightarrow> P x"
    hence hyps: "(\<And>y1 y2. lex_prodp (y1, y2) (x1, x2) \<Longrightarrow> P (y1, y2)) \<Longrightarrow> P (x1, x2)" for x1 x2
      by fast
    show "(\<And>x. P x)"
      apply (simp only: split_paired_all)
      apply (atomize (full))
      apply (rule allI)
      apply (rule wfP_induct_rule[OF assms(1), of "\<lambda>y. \<forall>b. P (y, b)"])
      apply (rule allI)
      apply (rule wfP_induct_rule[OF assms(2), of "\<lambda>b. P (x, b)" for x])
      using hyps[unfolded lex_prodp_def, simplified]
      by blast
  qed
qed

end

lemma lex_prodp_well_founded:
  assumes
    "well_founded r1" and
    "well_founded r2"
  shows "well_founded (lex_prodp r1 r2)"
  using well_founded.intro lex_prodp_wfP assms[THEN well_founded.wf] by auto

section \<open>Lexicographic list\<close>

context
  fixes order :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

inductive lex_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  lex_list_head: "order x y \<Longrightarrow> length xs = length ys \<Longrightarrow> lex_list (x # xs) (y # ys)" |
  lex_list_tail: "lex_list xs ys \<Longrightarrow> lex_list (x # xs) (x # ys)"

end

lemma lex_list_prepend: "lex_list order ys zs \<Longrightarrow> lex_list order (xs @ ys) (xs @ zs)"
  by (induction xs) (simp_all add: lex_list_tail)

lemma lex_list_lex: "lex_list order xs ys \<longleftrightarrow> (xs, ys) \<in> lex {(x, y). order x y}"
proof
  assume "lex_list order xs ys"
  thus "(xs, ys) \<in> lex {(x, y). order x y}"
    by (induction xs ys rule: lex_list.induct) simp_all
next
  assume "(xs, ys) \<in> lex {(x, y). order x y}"
  thus "lex_list order xs ys"
    by (auto intro!: lex_list_prepend intro: lex_list_head simp: lex_conv)
qed

lemma lex_list_wfP: "wfP order \<Longrightarrow> wfP (lex_list order)"
  by (simp add: lex_list_lex wf_lex wfP_def)

lemma lex_list_well_founded:
  assumes "well_founded order"
  shows "well_founded (lex_list order)"
  using well_founded.intro assms(1)[THEN well_founded.wf, THEN lex_list_wfP] by auto

end