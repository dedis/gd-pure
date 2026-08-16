axiomatization subset :: "List ⇒ List ⇒ o" where
  subset_def: "subset G' G :=
    if G' = Nil then True
    else mem (list_hd G') G ∧ subset (list_tl G') G"
