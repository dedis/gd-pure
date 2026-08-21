assumes is_valid_proof_def: "is_valid_proof pf J := 
    if pf = Nil then False
    else if list_hd pf = J then check_list pf
    else False"
