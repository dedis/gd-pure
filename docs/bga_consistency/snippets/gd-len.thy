axiomatization len :: "List ⇒ num" where
  len_def: "len xs := if xs = Nil then 0 else S (len (list_tl xs))"
