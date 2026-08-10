  cpx :: "num ⇒ num" and
  cpy :: "num ⇒ num"
where
  cpx_def: "cpx x := if x = 0 then 0
                     else if cpx (P x) = 0 then S(cpy P(x))
                     else P(cpx (P x))" and
  cpy_def: "cpy x := if cpx (P x) = 0 then 0
                     else S(cpy (P x))"
