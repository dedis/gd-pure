axiomatization mem :: "num ⇒ List ⇒ o" (infixr "∈" 75) where
  mem_def: "mem x G := if G = Nil then False
                       else if list_hd G = x then True
                       else mem x (list_tl G)"
