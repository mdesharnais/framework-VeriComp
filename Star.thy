theory Star
  imports Plus
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  star_refl: "star r x x" |
  star_step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  by (induction rule: star.induct) (auto intro: star.intros)

lemma star_init: "r x y \<Longrightarrow> star r x y"
  by (auto intro: star.intros)

lemma plus_to_star: "plus r x y \<Longrightarrow> star r x y"
  by (induction x y rule: plus.induct) (auto intro: star.intros)

lemma plus_append_star: "plus step x y \<Longrightarrow> star step y z \<Longrightarrow> plus step x z"
apply (rotate_tac 1)
proof (induction y z arbitrary: x rule: star.induct)
  case (star_refl x)
  then show ?case by simp
next
  case (star_step w y z)
  then show ?case using plus_append_step by metis
qed

end