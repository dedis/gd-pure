  fixes check_template :: "fm ⇒ fm ⇒ tm ⇒ tm ⇒ fm ⇒ tm ⇒ o"
(* Counts down p from max_bound to 0. 
     i is fixed to a fresh variable (e.g., f+1)
  f - formula we are trying to see if valid
  phi - premise formula
  p - template formula
  i - id of variable acting as a place holder in p
  a=b - equality being considered
 *)
  assumes check_template_def: "check_template f phi a b p i :=
    if subst_F p i a = phi ∧ subst_F p i b = f then True
    else if p > 0 = 1 then check_template f phi a b (p - 1) i
    else False"
