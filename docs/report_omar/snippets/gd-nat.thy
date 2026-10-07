  zero :: ‹num›                        and
  suc :: ‹num ⇒ num›     (‹S(_)› [800]) and
  pred :: ‹num ⇒ num›    (‹P(_)› [800])
where
  nat0: ‹zero N› and
  sucInj: ‹S a = S b ⟹ a = b› and
  sucCong: ‹a = b ⟹ S a = S b› and
  predCong: ‹a = b ⟹ P a = P b› and
  eqBool: ‹⟦a N; b N⟧ ⟹ (a = b) B› and
(*eqBoolB: ‹⟦x B; y B⟧ ⟹ (x = y) B› and*)
  sucNonZero: ‹a N ⟹ S a ≠ zero› and
  predSucInv: ‹a N ⟹ P(S(a)) = a› and
  pred0: ‹P(zero) = zero› and
  eqE: ‹((a = b) B) ⟹ ((a N) ∧ (b N))› and
  predTIE: ‹(P a N) ⟹ (a N)› and
  ind [case_names HQ Base Step]:
           "⟦a N; Q zero; ⋀x. x N ⟹ Q x ⟹ Q S(x)⟧ ⟹ Q a"
