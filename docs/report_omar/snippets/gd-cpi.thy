  cpi' :: "num ⇒ num ⇒ num"
where
  cpi'_def: "cpi' n x := if n = 0 then 0
                         else if n = 1 then x
                         else cpy (cpi' (n-1) x)"
