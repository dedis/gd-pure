fixes check_list :: "pf ⇒ o"
assumes check_list_def: "check_list pf := 
    if pf = Nil then True
    else if valid_step (list_hd pf) (list_tl pf) then check_list (list_tl pf)
    else False"
