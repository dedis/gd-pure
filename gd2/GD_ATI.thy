theory GD_ATI
  imports GD_Core
begin

text \<open>
  ATI, the one rule OGA adds to RGA: if every numeral instance of a universal
  is decided, the universal is decided.  Sound for the omega clause of M2 (all
  instances are 1, or some instance is 0).

  It is not in the kernel, so that results using it are visible: a theory
  that wants it imports GD_ATI, and thm_deps lists ATI for every result that
  depends on it.  Without it the quantifier rules are RGA's.
\<close>

axiomatization where
  ATI: \<open>(\<forall>x. (Q x) B) \<Longrightarrow> (\<forall>x. Q x) B\<close>    (* all instances decided, so all 1 or some 0 *)

end
