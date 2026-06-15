theory BGA_on_GA
  imports GD
begin

(* Tags *)

definition tag_trmVar  :: num where "tag_trmVar  \<equiv> 1"
definition tag_trm0    :: num where "tag_trm0    \<equiv> 2"
definition tag_trmSuc  :: num where "tag_trmSuc  \<equiv> 3"
definition tag_trmPred :: num where "tag_trmPred \<equiv> 4"
definition tag_trmIfz  :: num where "tag_trmIfz  \<equiv> 5"
definition tag_trmApp2 :: num where "tag_trmApp2 \<equiv> 6"

definition tag_fmEq    :: num where "tag_fmEq    \<equiv> 7"
definition tag_fmNe    :: num where "tag_fmNe    \<equiv> 8"

(* Constructors *)

definition mk_trmVar :: "num \<Rightarrow> num" where 
  "mk_trmVar v \<equiv> cpair tag_trmVar v"

definition mk_trm0 :: "num" where 
  "mk_trm0 \<equiv> cpair tag_trm0 0"

definition mk_trmSuc :: "num \<Rightarrow> num" where 
  "mk_trmSuc t \<equiv> cpair tag_trmSuc t"

definition mk_trmPred :: "num \<Rightarrow> num" where 
  "mk_trmPred t \<equiv> cpair tag_trmPred t"

definition mk_trmIfz :: "num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num" where 
  "mk_trmIfz c a b \<equiv> cpair tag_trmIfz (cpair c (cpair a b))"

definition mk_trmApp2 :: "num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num" where 
  "mk_trmApp2 d t1 t2 \<equiv> cpair tag_trmApp2 (cpair d (cpair t1 t2))"

definition mk_fmEq :: "num \<Rightarrow> num \<Rightarrow> num" where 
  "mk_fmEq t1 t2 \<equiv> cpair tag_fmEq (cpair t1 t2)"

definition mk_fmNe :: "num \<Rightarrow> num \<Rightarrow> num" where 
  "mk_fmNe t1 t2 \<equiv> cpair tag_fmNe (cpair t1 t2)"


axiomatization 
  is_bga_trm :: "num \<Rightarrow> num" and
  is_bga_fm  :: "num \<Rightarrow> num" and
  lookup_env :: "List \<Rightarrow> num \<Rightarrow> num" and
  lookup_def :: "List \<Rightarrow> num \<Rightarrow> num"
where
  (* checks if a number encodes a BGA term (returns 1 for True, 0 for False) *)
  is_bga_trm_def: "is_bga_trm t := 
    if cpx t = tag_trmVar then 1
    else if cpx t = tag_trm0 then 1
    else if cpx t = tag_trmSuc then is_bga_trm (cpy t)
    else if cpx t = tag_trmPred then is_bga_trm (cpy t)
    else if cpx t = tag_trmIfz then 
       (if is_bga_trm (cpx (cpy t)) = 1 then
           (if is_bga_trm (cpx (cpy (cpy t))) = 1 then is_bga_trm (cpy (cpy (cpy t))) else 0)
        else 0)
    else if cpx t = tag_trmApp2 then
       (if is_bga_trm (cpx (cpy (cpy t))) = 1 then is_bga_trm (cpy (cpy (cpy t))) else 0)
    else 0" and

  (* Verifies if a number correctly a BGA formula *)
  is_bga_fm_def: "is_bga_fm f :=
    if cpx f = tag_fmEq then 
       (if is_bga_trm (cpx (cpy f)) = 1 then is_bga_trm (cpy (cpy f)) else 0)
    else if cpx f = tag_fmNe then
       (if is_bga_trm (cpx (cpy f)) = 1 then is_bga_trm (cpy (cpy f)) else 0)
    else 0" and

  (* Looks up the ith variable in an assignment *)
  lookup_env_def: "lookup_env A i := 
    if A = Nil then omega 
    else if i = 0 then cpi 3 A 
    else lookup_env (cpi' 4 A) (P i)" and

  (* Looks up the ith definition in a definition *)
  lookup_def_def: "lookup_def D i := 
    if D = Nil then omega 
    else if i = 0 then cpi 3 D 
    else lookup_def (cpi' 4 D) (P i)"


axiomatization 
  eval_trm :: "List \<Rightarrow> List \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num" and
  eval_fm  :: "List \<Rightarrow> List \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num"
where
  (*  evaluates term t under defs D, assignment A, for s steps*)
  eval_trm_def: "eval_trm D A s t :=
    if s = 0 then 0
    else if cpx t = tag_trmVar then cpair 1 (lookup_env A (cpy t))
    else if cpx t = tag_trm0 then cpair 1 0
    else if cpx t = tag_trmSuc then
       (if cpx (eval_trm D A (P s) (cpy t)) = 1 
        then cpair 1 (S (cpy (eval_trm D A (P s) (cpy t)))) else 0)
    else if cpx t = tag_trmPred then
       (if cpx (eval_trm D A (P s) (cpy t)) = 1 
        then cpair 1 (P (cpy (eval_trm D A (P s) (cpy t)))) else 0)
    else if cpx t = tag_trmIfz then
       (if cpx (eval_trm D A (P s) (cpx (cpy t))) = 1 then
          (if cpy (eval_trm D A (P s) (cpx (cpy t))) = 0
           then eval_trm D A (P s) (cpx (cpy (cpy t)))
           else eval_trm D A (P s) (cpy (cpy (cpy t))))
        else 0)
    else if cpx t = tag_trmApp2 then
       (if cpx (eval_trm D A (P s) (cpx (cpy (cpy t)))) = 1 then
          if cpx (eval_trm D A (P s) (cpy (cpy (cpy t)))) = 1 then
             eval_trm D 
                      (Cons (cpy (eval_trm D A (P s) (cpx (cpy (cpy t))))) 
                            (Cons (cpy (eval_trm D A (P s) (cpy (cpy (cpy t))))) Nil)) 
                      (P s) 
                      (lookup_def D (cpx (cpy t)))
          else 0
        else 0)
    else 0" and

  (* eval_fm D A s f : evaluates formula f (returns cpair 1 1 for True, cpair 1 0 for False) *)
  eval_fm_def: "eval_fm D A s f :=
    if s = 0 then 0
    else if cpx f = tag_fmEq then
       (if cpx (eval_trm D A (P s) (cpx (cpy f))) = 1 then
          if cpx (eval_trm D A (P s) (cpy (cpy f))) = 1 then
             (if cpy (eval_trm D A (P s) (cpx (cpy f))) = cpy (eval_trm D A (P s) (cpy (cpy f)))
              then cpair 1 1 else cpair 1 0)
          else 0
        else 0)
    else if cpx f = tag_fmNe then
       (if cpx (eval_trm D A (P s) (cpx (cpy f))) = 1 then
          if cpx (eval_trm D A (P s) (cpy (cpy f))) = 1 then
             (if cpy (eval_trm D A (P s) (cpx (cpy f))) \<noteq> cpy (eval_trm D A (P s) (cpy (cpy f)))
              then cpair 1 1 else cpair 1 0)
          else 0
        else 0)
    else 0"




axiomatization 
  subst_trm :: "num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num" and
  subst_fm  :: "num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num" and
  contains  :: "List \<Rightarrow> num \<Rightarrow> num" and
  is_valid_proof :: "List \<Rightarrow> List \<Rightarrow> num" and
  check_rule :: "List \<Rightarrow> List \<Rightarrow> num \<Rightarrow> num"
where

  subst_trm_def: "subst_trm old new t :=
    if t = old then new
    else if cpx t = tag_trmVar then t
    else if cpx t = tag_trm0 then t
    else if cpx t = tag_trmSuc then mk_trmSuc (subst_trm old new (cpy t))
    else if cpx t = tag_trmPred then mk_trmPred (subst_trm old new (cpy t))
    else if cpx t = tag_trmIfz then mk_trmIfz (subst_trm old new (cpx (cpy t))) 
                                              (subst_trm old new (cpx (cpy (cpy t)))) 
                                              (subst_trm old new (cpy (cpy (cpy t))))
    else if cpx t = tag_trmApp2 then mk_trmApp2 (cpx (cpy t))
                                                (subst_trm old new (cpx (cpy (cpy t))))
                                                (subst_trm old new (cpy (cpy (cpy t))))
    else t" and

  subst_fm_def: "subst_fm old new f :=
    if cpx f = tag_fmEq then mk_fmEq (subst_trm old new (cpx (cpy f))) (subst_trm old new (cpy (cpy f)))
    else if cpx f = tag_fmNe then mk_fmNe (subst_trm old new (cpx (cpy f))) (subst_trm old new (cpy (cpy f)))
    else f" and

  contains_def: "contains p f :=
    if (p = Nil) then 0
    else if cpi 3 p = f then 1
    else contains (cpi' 4 p) f" and


  check_rule_def: "check_rule D P_prev f :=
    if f = mk_fmEq mk_trm0 mk_trm0 then 1
    else if cpx f = tag_fmEq then
      (if contains P_prev (mk_fmEq (cpy (cpy f)) (cpx (cpy f))) = 1 then 1
       else 0)
    else if cpx f = tag_fmNe then
      (if contains P_prev (mk_fmNe (cpy (cpy f)) (cpx (cpy f))) = 1 then 1
       else 0)
    else 0" and

  is_valid_proof_def: "is_valid_proof D p :=
    if p = Nil then 1
    else if is_valid_proof D (cpi' 4 p) = 1 then
       check_rule D (cpi' 4 p) (cpi 3 p)
    else 0"



