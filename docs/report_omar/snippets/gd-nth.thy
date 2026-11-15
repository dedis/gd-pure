axiomatization nth :: "num ⇒ List ⇒ num" where
  nth_def: "nth i xs := if xs = Nil then 0
                        else if i = 0 then list_hd xs
                        else nth (i - 1) (list_tl xs)"
