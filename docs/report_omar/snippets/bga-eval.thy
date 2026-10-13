  assumes eval_def: "eval t A :=
    if tag_T t = T_VAR then nth (load_T t) A                          
    else if tag_T t = T_ZERO then 0                                    
    else if tag_T t = T_SUC then S(eval (load_T t) A)              
    else if tag_T t = T_PRED then P(eval (load_T t) A)               
    else if tag_T t = T_IFZ then                                     
      (if eval (cpx (load_T t)) A = 0 
         then eval (cpx (cpy (load_T t))) A
         else eval (cpy (cpy (load_T t))) A)
    else
      (if eval (cpx (cpy (load_T t))) A = eval (cpx (cpy (load_T t))) A
       then (if eval (cpy (cpy (load_T t))) A = eval (cpy (cpy (load_T t))) A
             then eval (nth (cpx (load_T t)) dfns)
                    ((eval (cpx (cpy (load_T t))) A)▹ ((eval (cpy (cpy (load_T t))) A) ▹ Nil))
             else 0)
       else 0)"
