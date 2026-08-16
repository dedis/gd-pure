axiomatization cpair :: "num ⇒ num ⇒ num" where
  cpair_def: "cpair x y := if y = 0 then div (x * S(x)) 2
                           else cpair x P(y) + x + y + 1"
