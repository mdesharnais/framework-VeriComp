theory Semantics
  imports Main Behaviour Plus Star Inf begin

text \<open>
The definition of programming languages is separated into two parts: an abstract semantics and a concrete program representation.
\<close>

definition finished :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "finished r x = (\<nexists>y. r x y)"

lemma finished_star: "finished r x \<Longrightarrow> star r x y \<Longrightarrow> x = y"
  apply (rotate_tac 1)
  by (induction x y rule: star.induct) (auto simp only: finished_def)

locale semantics =
  fixes
    step :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<rightarrow>" 50) and
    final :: "'state \<Rightarrow> bool"
  assumes
    final_finished: "final s \<Longrightarrow> finished step s"
begin

text \<open>
The semantics locale represents the semantics as an abstract machine.
It is expressed by a transition system with a transition relation @{term step}—usually written as an infix (\<rightarrow>) arrow—and final states @{term final}.
\<close>

lemma finished_step:
  "step s s' \<Longrightarrow> \<not>finished step s"
by (auto simp add: finished_def)

abbreviation eval :: "'state \<Rightarrow> 'state \<Rightarrow> bool" (infix "\<rightarrow>\<^sup>*" 50) where
  "eval \<equiv> star step"

abbreviation inf_step :: "'state \<Rightarrow> bool" where
  "inf_step \<equiv> inf step"

notation
  inf_step ("'(\<rightarrow>\<^sup>\<infinity>')" [] 50) and
  inf_step ("_ \<rightarrow>\<^sup>\<infinity>" [55] 50)

lemma finished_inf: "s \<rightarrow>\<^sup>\<infinity> \<Longrightarrow> \<not> finished step s"
  using inf.cases finished_step by metis

(* QUESTION: I would prefer to separate the two `finished` assumption in a `assumes` clause. But by
 doing that, `s2` is not instantiated in the hypothesis and the goal is unprovable. How can I
 achieve this separation? *)
lemma eval_deterministic:
  assumes
    deterministic: "\<And>x y z. step x y \<Longrightarrow> step x z \<Longrightarrow> y = z"
  shows "s1 \<rightarrow>\<^sup>* s2 \<Longrightarrow> s1 \<rightarrow>\<^sup>* s3 \<Longrightarrow> finished step s2 \<Longrightarrow> finished step s3 \<Longrightarrow> s2 = s3"
proof(induction s1 s2 arbitrary: s3 rule: star.induct)
  case (star_refl x)
  then show ?case by (simp add: finished_star)
next
  case (star_step x y z)
    note hyps = star_step.hyps
     and prems = star_step.prems
     and IH = star_step.IH
  show "eval x s3 \<Longrightarrow> z = s3"
  proof(induction rule: star.cases)
    case (star_refl w)
    then show ?case
      using hyps prems by (auto dest: finished_step)
  next
    case (star_step x2 y2 z2)
    then have "y = y2" using hyps by (simp only: deterministic)
    then show ?case using IH prems hyps star_step by auto
  qed
qed

inductive behaves :: "'state \<Rightarrow> 'state behaviour \<Rightarrow> bool" (infix "\<Down>" 50) where
  state_terminates:
    "s1 \<rightarrow>\<^sup>* s2 \<Longrightarrow> finished step s2 \<Longrightarrow> final s2 \<Longrightarrow> s1 \<Down> (Terminates s2)" |
  state_diverges:
    "s1 \<rightarrow>\<^sup>\<infinity> \<Longrightarrow> s1 \<Down> Diverges" |
  state_goes_wrong:
    "s1 \<rightarrow>\<^sup>* s2 \<Longrightarrow> finished step s2 \<Longrightarrow> \<not> final s2 \<Longrightarrow> s1 \<Down> (Goes_wrong s2)"


text \<open>
Even though the @{term step} transition relation in the @{locale semantics} locale need not be deterministic, if it happens to be, then the behaviour of a program becomes deterministic too.
\<close>

lemma behaves_deterministic:
  assumes
    deterministic: "\<And>x y z. step x y \<Longrightarrow> step x z \<Longrightarrow> y = z"
  shows "s \<Down> b1 \<Longrightarrow> s \<Down> b2 \<Longrightarrow> b1 = b2"
proof (induction s b1 rule: behaves.induct)
  case (state_terminates s1 s2)
  show ?case using state_terminates.prems state_terminates.hyps
  proof (induction s1 b2 rule: behaves.induct)
    case (state_terminates s1 s3)
    then show ?case
      using eval_deterministic deterministic by simp
  next
    case (state_diverges s1)
    then show ?case
      using deterministic star_inf[THEN finished_inf] by simp
  next
    case (state_goes_wrong s1 s3)
    then show ?case
      using eval_deterministic deterministic by blast
  qed
next
  case (state_diverges s1)
  show ?case using state_diverges.prems state_diverges.hyps
  proof (induction s1 b2 rule: behaves.induct)
    case (state_terminates s1 s2)
    then show ?case
      using deterministic star_inf[THEN finished_inf] by simp
  next
    case (state_diverges s1)
    then show ?case by simp
  next
    case (state_goes_wrong s1 s2)
    then show ?case
      using deterministic star_inf[THEN finished_inf] by simp
  qed
next
  case (state_goes_wrong s1 s2)
  show ?case using state_goes_wrong.prems state_goes_wrong.hyps
  proof (induction s1 b2)
    case (state_terminates s1 s3)
    then show ?case 
      using eval_deterministic deterministic by blast
  next
    case (state_diverges s1)
    then show ?case
      using deterministic star_inf[THEN finished_inf] by simp
  next
    case (state_goes_wrong s1 s3)
    then show ?case
      using eval_deterministic deterministic by simp
  qed
qed

end

end