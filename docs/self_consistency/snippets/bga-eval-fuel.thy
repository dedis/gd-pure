locale bga_fuel_semantics = bga_dfns +
  fixes eval_fuel :: "num ⇒ tm ⇒ asn ⇒ val"
  assumes eval_fuel_def: "eval_fuel k t A :=
    if k = 0 then 0
    else if tag_T t = T_VAR then S (nth (load_T t) A)
    else if tag_T t = T_ZERO then S 0
    else if tag_T t = T_SUC then
      if eval_fuel (P k) (load_T t) A = 0 then 0
      else S (S (P (eval_fuel (P k) (load_T t) A)))
    else if tag_T t = T_PRED then
      if eval_fuel (P k) (load_T t) A = 0 then 0
      else S (P (P (eval_fuel (P k) (load_T t) A)))
    else if tag_T t = T_IFZ then
      if eval_fuel (P k) (hyp_of (load_T t)) A = 0 then 0
      else if P (eval_fuel (P k) (hyp_of (load_T t)) A) = 0
      then eval_fuel (P k) (hyp_of (conc_of (load_T t))) A
      else eval_fuel (P k) (conc_of (conc_of (load_T t))) A
    else
      if eval_fuel (P k) (hyp_of (conc_of (load_T t))) A = 0 then 0
      else if eval_fuel (P k) (conc_of (conc_of (load_T t))) A = 0 then 0
      else eval_fuel (P k) (nth (hyp_of (load_T t)) dfns)
        (P (eval_fuel (P k) (hyp_of (conc_of (load_T t))) A) ▹
         P (eval_fuel (P k) (conc_of (conc_of (load_T t))) A) ▹ Nil)"
