lemma cpy_mono [simp]: "x N ⟹ cpy x ≤ x = 1"
apply (induct x)
proof (simp add: cpy_suc)+
  case (Step xa)
    show "x N ⟹ xa N ⟹ cpy xa ≤ xa = 1 ⟹
      (if cpx xa = 0 then 0 else S(cpy xa)) ≤ (S xa) = 1"
      by (cases bool: "cpx xa = 0", simp+)
qed


lemma cpx_mono [simp]: "x N ⟹ cpx x ≤ x = 1"
