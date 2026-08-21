  fixes rep_vars_T     :: "tm ⇒ tm ⇒ tm"
(* rep_vars_T t i: Replaces all leaves in term t with variable i *)
  assumes rep_vars_T_def: "rep_vars_T t i :=
    if tag_T t = T_VAR then pack_T T_VAR i
    else if tag_T t = T_ZERO then pack_T T_VAR i
    else if tag_T t = T_SUC then pack_T T_SUC (rep_vars_T (load_T t) i)
    else if tag_T t = T_PRED then pack_T T_PRED (rep_vars_T (load_T t) i)
    else if tag_T t = T_IFZ then 
      pack_T T_IFZ ⟨rep_vars_T (cpx (load_T t)) i, 
               ⟨rep_vars_T (cpx (cpy (load_T t))) i, 
                rep_vars_T (cpy (cpy (load_T t))) i⟩⟩
