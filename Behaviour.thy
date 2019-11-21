theory Behaviour
  imports Main
begin

datatype 'state behaviour =
  Terminates 'state | Diverges | is_wrong: Goes_wrong 'state

fun behaviours_match :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a behaviour \<Rightarrow> 'b behaviour \<Rightarrow> bool" where
  "behaviours_match f (Terminates s1) (Terminates s2) = f s1 s2" |
  "behaviours_match _ Diverges Diverges = True" |
  "behaviours_match f (Goes_wrong s1) (Goes_wrong s2) = f s1 s2" |
  "behaviours_match _ _ _ = False"

end