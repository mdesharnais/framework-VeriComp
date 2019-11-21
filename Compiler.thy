theory Compiler
  imports Language Simulation
begin

definition option_comp :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('c \<Rightarrow> 'a option) \<Rightarrow> 'c \<Rightarrow> 'b option" (infix "\<Lleftarrow>" 50) where
  "(f \<Lleftarrow> g) x \<equiv> Option.bind (g x) f"

context
  fixes f :: "('a \<Rightarrow> 'a option)"
begin

fun option_comp_pow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "option_comp_pow 0 = (\<lambda>_. None)" |
  "option_comp_pow (Suc 0) = f" |
  "option_comp_pow (Suc n) = (option_comp_pow n \<Lleftarrow> f)"

end

locale compiler =
  L1: language step1 final1 load1 +
  L2: language step2 final2 load2 +
  backward_simulation step1 step2 final1 final2 order match
  for
    step1 and step2 and
    final1 and final2 and
    load1 :: "'prog1 \<Rightarrow> 'state1" and
    load2 :: "'prog2 \<Rightarrow> 'state2" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" and
    match +
  fixes
    compile :: "'prog1 \<Rightarrow> 'prog2 option"
  assumes
    compile_load: "compile p1 = Some p2 \<Longrightarrow> \<exists>i. match i (load1 p1) (load2 p2)"

corollary (in compiler) behaviour_preservation:
  assumes
    compiles: "compile p\<^sub>1 = Some p\<^sub>2" and
    behaves: "L2.behaves (load2 p\<^sub>2) b\<^sub>2" and
    not_wrong: "\<not> is_wrong b\<^sub>2"
  shows "\<exists>b\<^sub>1 i. L1.behaves (load1 p\<^sub>1) b\<^sub>1 \<and> behaviours_match (match i) b\<^sub>1 b\<^sub>2"
  using compile_load[OF compiles] simulation_behaviour[OF behaves not_wrong]
  by blast

lemma compiler_composition:
  assumes
    "compiler step1 step2 final1 final2 load1 load2 order1 match1 compile1" and
    "compiler step2 step3 final2 final3 load2 load3 order2 match2 compile2"
  shows "compiler step1 step3 final1 final3 load1 load3
    (lex_prod (plus order1) order2) (rel_comp match1 match2) (compile2 \<Lleftarrow> compile1)"
proof (rule compiler.intro) 
  show "language step1 final1"
    using assms(1)[THEN compiler.axioms(1)] .
next
  show "language step3 final3"
    using assms(2)[THEN compiler.axioms(2)] .
next
  show "backward_simulation step1 step3 final1 final3
     (lex_prod (plus order1) order2) (rel_comp match1 match2)"
    using backward_simulation_composition[OF assms[THEN compiler.axioms(3)]] .
next
  show "compiler_axioms load1 load3 (rel_comp match1 match2) (compile2 \<Lleftarrow> compile1)"
  proof unfold_locales
    fix p1 p3
    assume "(compile2 \<Lleftarrow> compile1) p1 = Some p3"
    then obtain p2 where "compile1 p1 = Some p2" and "compile2 p2 = Some p3"
      by (auto simp: bind_eq_Some_conv option_comp_def)
    thus "\<exists>i. rel_comp match1 match2 i (load1 p1) (load3 p3)"
      using assms[THEN compiler.compile_load]
      unfolding rel_comp_def
      by fastforce
  qed
qed

lemma compiler_composition_pow:
  assumes
    "compiler step step final final load load order match compile"
  shows "compiler step step final final load load
    (lex_list (plus order)) (rel_comp_pow match) (option_comp_pow compile n)"
proof (induction n rule: option_comp_pow.induct)
  case 1
  show ?case
    using assms
    by (auto intro: compiler.axioms compiler.intro compiler_axioms.intro backward_simulation_pow)
next
  case 2
  show ?case
  proof (rule compiler.intro)
    show "compiler_axioms load load (rel_comp_pow match) (option_comp_pow compile (Suc 0))"
    proof unfold_locales
      fix p1 p2
      assume "option_comp_pow compile (Suc 0) p1 = Some p2"
      thus "\<exists>i. rel_comp_pow match i (load p1) (load p2)"
        using compiler.compile_load[OF assms(1)]
        by (metis option_comp_pow.simps(2) rel_comp_pow.simps(2))
    qed
  qed (auto intro: assms compiler.axioms backward_simulation_pow)
next
  case (3 n')
  show ?case
  proof (rule compiler.intro)
    show "compiler_axioms load load (rel_comp_pow match) (option_comp_pow compile (Suc (Suc n')))"
    proof unfold_locales
      fix p1 p3
      assume "option_comp_pow compile  (Suc (Suc n')) p1 = Some p3"
      then obtain p2 where "compile p1 = Some p2" and "option_comp_pow compile (Suc n') p2 = Some p3"
        by (auto simp: option_comp_def bind_eq_Some_conv)
      then obtain i where "rel_comp_pow match i (load p2) (load p3)"
        using compiler.compile_load[OF "3.IH"] by auto
      then show "\<exists>i. rel_comp_pow match i (load p1) (load p3)"
        using compiler.compile_load[OF assms(1) \<open>compile p1 = Some p2\<close>]
        by (metis neq_Nil_conv rel_comp_pow.simps(1) rel_comp_pow.simps(3))
    qed
  qed (auto intro: assms compiler.axioms backward_simulation_pow)
qed

end