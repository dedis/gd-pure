  add   :: "num ⇒ num ⇒ num"  (infixl "+" 60) and
  sub   :: "num ⇒ num ⇒ num"  (infixl "-" 60) and
  mult  :: "num ⇒ num ⇒ num"  (infixl "*" 70) and
  div   :: "num ⇒ num ⇒ num"                  and
  less  :: "num ⇒ num ⇒ num"  (infix "<" 50)  and
  leq   :: "num ⇒ num ⇒ num"  (infix "≤" 50) and
  omega :: "'a"
where
  add_def:   "add x y  := if y = 0 then x else S(add x (P y))"       and
  sub_def:   "sub x y  := if y = 0 then x else P(sub x (P y))"       and
  mult_def:  "mult x y := if y = 0 then 0 else (x + mult x (P y))"   and
  leq_def:   "leq x y  := if x = 0 then 1
                          else if y = 0 then 0
                          else (leq (P x) (P y))"                    and
  less_def:  "less x y := if y = 0 then 0
                          else if x = 0 then 1
                          else (less (P x) (P y))"                   and
  div_def:   "div x y  := if x < y = 1 then 0 else S(div (x - y) y)" and
  omega_def: "omega    := omega"
