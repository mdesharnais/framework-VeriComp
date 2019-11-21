theory Plus
  imports Well_founded
begin

inductive plus :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  plus_init: "r x y \<Longrightarrow> plus r x y" |
  plus_step: "r x y \<Longrightarrow> plus r y z \<Longrightarrow> plus r x z"

code_pred plus .

lemma plus_trans:
  "plus r x y \<Longrightarrow> plus r y z \<Longrightarrow> plus r x z"
by (induction rule: plus.induct) (auto intro: plus_step)

lemma plus_append_step:
  assumes
    "plus r x y" and
    "r y z"
  shows "plus r x z"
  by (auto intro: plus_init assms plus_trans[of r x y z])

lemma plus_inv: "plus r x z \<Longrightarrow> \<exists>y. r x y"
  by (metis plus.cases)

lemma plus_tranclp: "plus r = r\<^sup>+\<^sup>+"
proof ((rule ext)+, rule iffI)
  fix x y
  assume "plus r x y"
  thus "r\<^sup>+\<^sup>+ x y"
    by (induction x y rule: plus.induct) simp_all
next
  fix x y
  assume "r\<^sup>+\<^sup>+ x y"
  thus "plus r x y"
    by (induction x y rule: tranclp.induct) (auto intro: plus_init plus_append_step)
qed

lemma plus_wfP: "wfP r \<Longrightarrow> wfP (plus r)"
  using wfP_trancl by (simp add: plus_tranclp)

lemma plus_well_founded:
  assumes "well_founded r"
  shows "well_founded (plus r)"
by (auto intro: well_founded.intro plus_wfP well_founded.wf[OF assms(1)])

end
