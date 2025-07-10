(* Title: pure/GD.thy
*)

section \<open>Grounded deduction logic\<close>

theory GD
  imports Pure
begin

text \<open>The following theory development formalizes the Grounded Deduction Logic.
      Isabelle/Isar.\<close>

section \<open>GD syntax and axiomatization\<close>

typedecl o

judgment
  Trueprop :: \<open>o \<Rightarrow> prop\<close>

end
