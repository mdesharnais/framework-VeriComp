theory Language
  imports Semantics
begin

locale language =
  semantics step final
  for
    step :: "'state \<Rightarrow> 'state \<Rightarrow> bool" and
    final :: "'state \<Rightarrow> bool" +
  fixes
    load :: "'prog \<Rightarrow> 'state"

end