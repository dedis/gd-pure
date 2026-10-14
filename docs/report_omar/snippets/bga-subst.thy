locale bga_subst = bga_encoding +
  fixes subst_T        :: "tm ⇒ tm ⇒ tm ⇒ tm"
  (* subst_T t j v: Inside term 't', replace variable index 'j' with term 'v' *)
  assumes subst_T_def: "subst_T t j v := 
    if tag_T t = T_VAR then 
      (if load_T t = j then v else t)
    else if tag_T t = T_ZERO then (pack_T T_ZERO 0)
    else if tag_T t = T_SUC then (pack_T T_SUC (subst_T (load_T t) j v))
    else if tag_T t = T_PRED then (pack_T T_PRED (subst_T (load_T t) j v))
    else if tag_T t = T_IFZ then 
      (pack_T T_IFZ ⟨subst_T (cpx (load_T t)) j v 
            , ⟨(subst_T (cpx (cpy (load_T t))) j v), 
            (subst_T (cpy (cpy (load_T t))) j v)⟩⟩)
    else 
      (pack_T T_APP ⟨(cpx (load_T t)), ⟨ 
             (subst_T (cpx (cpy (load_T t))) j v), 
             (subst_T (cpy (cpy (load_T t))) j v)⟩⟩)"

    fixes subst_F        :: "fm ⇒ tm ⇒ tm ⇒ fm"
  (* subst_F f j v: Inside formula 'f', replace variable index 'j' with term 'v' *)
  assumes subst_F_def: "subst_F f j v :=
    if tag_F f = F_EQ then
      pack_F F_EQ ⟨(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)⟩
    else
      pack_F F_NEQ ⟨(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)⟩"

  fixes subst_body :: "tm ⇒ tm ⇒ tm ⇒ tm"    
  (* subst_body b x y  =  b[0↦x, 1↦y] simultaneously *)
  assumes subst_body_def: "subst_body b x y :=
    if tag_T b = T_VAR then
      (if load_T b = 0 then x else if load_T b = 1 then y else b)
    else if tag_T b = T_ZERO then b
    else if tag_T b = T_SUC  then pack_T T_SUC  (subst_body (load_T b) x y)
    else if tag_T b = T_PRED then pack_T T_PRED (subst_body (load_T b) x y)
    else if tag_T b = T_IFZ  then
      pack_T T_IFZ ⟨subst_body (cpx (load_T b)) x y,
               ⟨subst_body (cpx (cpy (load_T b))) x y,
                subst_body (cpy (cpy (load_T b))) x y⟩⟩
