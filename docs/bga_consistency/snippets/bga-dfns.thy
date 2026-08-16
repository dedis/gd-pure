locale bga_dfns = bga_encoding + 
  fixes dfns :: "dfn"
  fixes dfn_is :: "dfn ⇒ num ⇒ tm ⇒ o"
  assumes dfns_N: "dfns N"
  (* lazy range check instea of direct conjunction which makes it kind of awkward to work with *)
  assumes dfn_is_def: "dfn_is d k b := if d < len dfns = 1 then nth d dfns = b ∧ fresh_T k b else False"
