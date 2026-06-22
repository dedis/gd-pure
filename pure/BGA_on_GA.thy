theory BGA_on_GA
  imports GD
begin

(* The idea is to abstract the encodings into a locale with the minimum assumptions needed to prove consistency. 
And we deal with the arithmetic nightmare exactly once during instantiation. *)

(* Type Aliases for Readability *)
type_synonym tm  = num  (* BGA Term *)
type_synonym fm  = num  (* BGA Formula *)
type_synonym asn = num  (* Assignment *)
type_synonym dfn = num  (* Definition *)
type_synonym pf = num  (* Proof List *)
type_synonym val = num  (* Evaluated Value *)


locale bga_consistent =
  (*Encoding  *)
  fixes mk_eq :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  fixes mk_neq :: "tm \<Rightarrow> tm \<Rightarrow> fm"

  (*Semantics. sat checks whether the encoding of a formula is satisfied by an assignment. eval reduces a term under an assignment*)
  fixes eval :: "tm \<Rightarrow> asn \<Rightarrow> dfn \<Rightarrow> val"
  fixes sat :: "fm \<Rightarrow> asn \<Rightarrow> dfn \<Rightarrow> o"

  (*Provability. is_valid_proof \<lbrace> p \<rbrace> \<lbrace> f \<rbrace> \<equiv> p \<P> \<lbrakk> \<phi> \<turnstile> f \<rbrakk>*)
  fixes is_valid_proof :: "pf \<Rightarrow> fm \<Rightarrow> o"

  (*Assumptions *)
  (*Habeas Quid for Syntax Constructors *)

  assumes mk_eq_N:  "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> mk_eq a b N"
  assumes mk_neq_N: "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> mk_neq a b N"

  (*  Habeas Quid for the Proof Checker *)
  assumes proof_bool: "\<lbrakk>p N; f N\<rbrakk> \<Longrightarrow> ((is_valid_proof p f) B)"
  
  (* Valid proofs yield satisfied formulas *)
  assumes soundness: "is_valid_proof p f \<Longrightarrow> sat f A D"
  
  (*What Equations mean in the model *)
  assumes sat_eqE:  "sat (mk_eq a b) A D \<Longrightarrow> eval a A D = eval b A D"
  assumes sat_neqE: "sat (mk_neq a b) A D \<Longrightarrow> eval a A D \<noteq> eval b A D"
begin

lemma bga_syntactically_consistent:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes p1_nat: "p1 N"
  assumes p2_nat: "p2 N"
  shows " \<not> (is_valid_proof p1 (mk_eq a b) \<and> is_valid_proof p2 (mk_neq a b))"

  apply (rule contradiction[where p="\<not>(is_valid_proof p1 (mk_eq a b) \<and> is_valid_proof p2 (mk_neq a b))"])
   apply simp

proof - 
  have mk_eq_nat: " mk_eq a b N"
    using a_nat b_nat apply (rule mk_eq_N)
    done

  have mk_neq_nat: " mk_neq a b N"
    using a_nat b_nat apply (rule mk_neq_N)
    done

  show " is_valid_proof p1 (mk_eq a b) B"
    using p1_nat mk_eq_nat apply (rule proof_bool)
    done

  show " is_valid_proof p2 (mk_neq a b) B"
    using p2_nat mk_neq_nat apply (rule proof_bool)
    done
  show " \<not> \<not> (is_valid_proof p1 (mk_eq a b) \<and> is_valid_proof p2 (mk_neq a b)) \<Longrightarrow> False "

  proof -

    assume double_neg: " \<not> \<not> (is_valid_proof p1 (mk_eq a b) \<and> is_valid_proof p2 (mk_neq a b))"

      have conj_holds: "is_valid_proof p1 (mk_eq a b) \<and> is_valid_proof p2 (mk_neq a b)"
        apply (rule dNegE)
        apply (rule double_neg)
        done

      have eq_prf: "is_valid_proof p1 (mk_eq a b)"
        apply (rule conjE1)
        apply (rule conj_holds)
        done

      have neq_prf: "is_valid_proof p2 (mk_neq a b)"
        apply (rule conjE2)
        apply (rule conj_holds)
        done

      have eq_sat: "sat (mk_eq a b) zero 0"
        apply (rule soundness)
        apply (rule eq_prf)
        done

      have neq_sat: "sat (mk_neq a b) zero 0"
        apply (rule soundness)
        apply (rule neq_prf)
        done

      have eq_val: "eval a zero 0 = eval b zero 0"
        apply (rule sat_eqE)
        apply (rule eq_sat)
        done

      have neq_val: "eval a zero 0 \<noteq> eval b zero 0"
        apply (rule sat_neqE)
        apply (rule neq_sat)
        done

      show "False"
        apply (rule exF[where P="eval a zero 0 = eval b zero 0"])
         apply (rule eq_val)
        apply (fold neq_def)
        apply (rule neq_val)
        done

    qed
  qed

end

definition list_hd :: "num \<Rightarrow> num" where
" list_hd L \<equiv> cpi 3 L"

definition list_tl :: "num \<Rightarrow> num" where
"list_tl L \<equiv> cpi' 4 L"

type_synonym tmtag = num
type_synonym fmtag = num
type_synonym tmenc = num
type_synonym fmenc = num

(*
Term Tags: Constructor Name : Syntax : Argument
0 : Variable : v_j : j
1 : Zero : 0 : (Ignored)
2 : Successor : S(a) : a encoded term)
3 : Predecessor : P(a) : a
4 : If-Zero : c0?a:b : \<langle>c, \<langle>a, b\<rangle>\<rangle>
5 : Application : d_i(a,b) : \<langle>i, \<langle>a, b\<rangle>\<rangle>

Formula Tags: Constructor Name : Syntax : Argument
0 : Equality : a=b : \<langle>a, b\<rangle>
1 : Inequality : a\<noteq>b : \<langle>a, b\<rangle>
*)
locale bga_bijective_encoding =
  (*Term Encoding *)
  (* Tag of the current Constructor *)
  fixes tag_T :: "tm \<Rightarrow> tmtag"
  (* Encoding of the argument *)
  fixes load_T :: "tm \<Rightarrow> tmenc"
  (* Encodes the term *)
  fixes pack_T :: "tmtag \<Rightarrow> tmenc \<Rightarrow> tm"

  (* Formula Encoding *)
  fixes tag_F :: "fm \<Rightarrow> fmtag"
  fixes load_F :: "fm \<Rightarrow> tmenc"
  fixes pack_F :: "fmtag \<Rightarrow> fmenc \<Rightarrow> fm"

  (* 3. Semantics *)
  fixes eval :: "tm \<Rightarrow> asn \<Rightarrow> dfn \<Rightarrow> val"
  fixes list_in :: "fm \<Rightarrow> pf \<Rightarrow> o"
  fixes valid_step :: "fm \<Rightarrow> pf \<Rightarrow> o"
  fixes check_list :: "pf \<Rightarrow> o"
  fixes is_valid_proof :: "pf \<Rightarrow> fm \<Rightarrow> o"

  (* AXIOMS *)

  (*Habeas Quid for the Encoder *)
  assumes pack_F_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> pack_F t L N"
  assumes tag_F_N:  "f N \<Longrightarrow> tag_F f N"
  assumes load_F_N: "f N \<Longrightarrow> load_F f N"

  assumes pack_T_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> pack_T t L N"
  assumes tag_T_N:  "t N \<Longrightarrow> tag_T t N"
  assumes load_T_N: "t N \<Longrightarrow> load_T t N"

  (*Injective *)
  assumes tag_pack_F:  "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> tag_F (pack_F t L) = t"
  assumes load_pack_F: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> load_F (pack_F t L) = L"
  
  assumes tag_pack_T:  "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> tag_T (pack_T t L) = t"
  assumes load_pack_T: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> load_T (pack_T t L) = L"

  (*Surjective *)
  assumes pack_tag_F:  "f N \<Longrightarrow> pack_F (tag_F f) (load_F f) = f"
  assumes pack_tag_T:  "t N \<Longrightarrow> pack_T (tag_T t) (load_T t) = t"

  (*Structural Decrease (For Induction) *)
  assumes decrease_F: "\<lbrakk>f N; f \<noteq> 0 \<rbrakk> \<Longrightarrow> load_F f < f = 1"
  assumes decrease_T: "\<lbrakk>t N; t \<noteq> 0\<rbrakk> \<Longrightarrow> load_T t < t = 1"

(*Monotone assumptions for Bounding *)
  assumes mono_pack_T: "(x \<le> y = 1) \<Longrightarrow> (pack_T tg x \<le> pack_T tg y =1)"
  assumes mono_pack_F: "(x \<le> y = 1) \<Longrightarrow> (pack_F tg x \<le> pack_F tg y =1)"

(* Note that P does not diverge on 0 due to the implementation 
of P in GD.thy not doing so*)
assumes eval_def: "eval t A D := 
    if tag_T t = 0 then cpi (load_T t) A                          
    else if tag_T t = 1 then 0                                    
    else if tag_T t = 2 then S(eval (load_T t) A D)              
    else if tag_T t = 3 then P(eval (load_T t) A D)               
    else if tag_T t = 4 then                                     
      (if eval (cpx (load_T t)) A D = 0 
         then eval (cpx (cpy (load_T t))) A D
         else eval (cpy (cpy (load_T t))) A D)
    else                                                          
      eval (cpi (cpx (load_T t)) D) 
           \<langle>eval (cpx (cpy (load_T t))) A D, eval (cpy (cpy (load_T t))) A D\<rangle> 
           D"

(* subst_T t j v: Inside term 't', replace variable index 'j' with term 'v' *)
  assumes subst_T_def: "subst_T t j v := 
    if tag_T t = 0 then 
      (if load_T t = j then v else t)
    else if tag_T t = 1 then (pack_T 1 0)
    else if tag_T t = 2 then (pack_T 2 (subst_T (load_T t) j v))
    else if tag_T t = 3 then (pack_T 3 (subst_T (load_T t) j v))
    else if tag_T t = 4 then 
      (pack_T 4 \<langle>subst_T (cpx (load_T t)) j v 
            , \<langle>(subst_T (cpx (cpy (load_T t))) j v), 
            (subst_T (cpy (cpy (load_T t))) j v)\<rangle>\<rangle>)
    else 
      (pack_T 5 \<langle>(cpx (load_T t)), \<langle> 
             (subst_T (cpx (cpy (load_T t))) j v), 
             (subst_T (cpy (cpy (load_T t))) j v)\<rangle>\<rangle>)"

  (* subst_F f j v: Inside formula 'f', replace variable index 'j' with term 'v' *)
  assumes subst_F_def: "subst_F f j v :=
    if tag_F f = 0 then
      pack_F 0 \<langle>(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)\<rangle>
    else
      pack_F 1 \<langle>(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)\<rangle>"

assumes list_in_def: "list_in f p := 
    if p = Nil then False
    else if list_hd p = f then True
    else list_in f (list_tl p)"

(*Counts down p and i from max_bound to 0. 
f - formula we are trying to see if valid
phi - premise formula
p - template formula
i - id of variable acting as a place holder in p
a=b - equality being considered
*)
  assumes check_template_def: "check_template f phi a b p i max_bound :=
    if subst_F p i a = phi \<and> subst_F p i b = f then True
    else if i > 0 = 1 then check_template f phi a b p (i - 1) max_bound
    else if p > 0= 1 then check_template f phi a b (p - 1) max_bound max_bound
    else False"

(* rep_vars_T t i: Replaces all leaves in term t with variable i *)
  assumes rep_vars_T_def: "rep_vars_T t i :=
    if tag_T t = 0 then pack_T 0 i
    else if tag_T t = 1 then pack_T 0 i
    else if tag_T t = 2 then pack_T 2 (rep_vars_T (load_T t) i)
    else if tag_T t = 3 then pack_T 3 (rep_vars_T (load_T t) i)
    else if tag_T t = 4 then 
      pack_T 4 \<langle>rep_vars_T (cpx (load_T t)) i, 
               \<langle>rep_vars_T (cpx (cpy (load_T t))) i, 
                rep_vars_T (cpy (cpy (load_T t))) i\<rangle>\<rangle>
    else 
      pack_T 5 \<langle>cpx (load_T t), 
               \<langle>rep_vars_T (cpx (cpy (load_T t))) i, 
                rep_vars_T (cpy (cpy (load_T t))) i\<rangle>\<rangle>"

  (* rep_vars_F f i: Replaces all leaves in formula f with variable i *)
  assumes rep_vars_F_def: "rep_vars_F f i :=
    if tag_F f = 0 then
      pack_F 0 \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle>
    else
      pack_F 1 \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle>"

(* Scans the proof list (ptr) for a valid premise phi (cpx ptr or ..) *)
  assumes find_phi_def: "find_phi f a b ptr :=
    if ptr = 0 then False
    else if check_template f (cpx ptr) a b (rep_vars_F f (f+1)) (f + 1) (f + 1) then True
    else find_phi f a b (cpy ptr)"

(* Scans the proof list (ptr) for an equality a = b *)
  assumes find_eq_def: "find_eq f rest ptr :=
    if ptr = 0 then False
    else if tag_F (cpx ptr) = 0 then
      if find_phi f (cpx (load_F (cpx ptr))) (cpy (load_F (cpx ptr))) rest then True
      else find_eq f rest (cpy ptr)
    else find_eq f rest (cpy ptr)"

(*checking the substitution rule *)
assumes check_subst_def: "check_subst f rest := find_eq f rest rest"

assumes valid_step_def: "valid_step f rest := 
    if list_in f rest then True
    
    else if check_subst f rest then True

    else if tag_F f = 0 then
      if cpx (load_F f) = (pack_T 1 0) \<and> cpy (load_F f) = (pack_T 1 0) then True
      else if list_in (pack_F 0 \<langle>cpy (load_F f), cpx (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = 2 \<and> tag_T (cpy (load_F f)) = 2 \<and> 
              list_in (pack_F 0 \<langle>load_T (cpx (load_F f)), load_T (cpy (load_F f))\<rangle>) rest then True
      else if list_in (pack_F 0 \<langle>(pack_T 2 (cpx (load_F f))), (pack_T 2 (cpy (load_F f)))\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = 3 \<and> tag_T (load_T (cpx (load_F f))) = 2 \<and> 
              cpx (load_T (load_T (cpx (load_F f)))) = cpy (load_F f) \<and> 
              list_in (pack_F 0 \<langle>cpy (load_F f), cpy (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = 4 \<and> cpx (load_T (cpx (load_F f))) = (pack_T 1 0) \<and> 
              cpy (load_F f) = cpx (cpy (load_T (cpx (load_F f)))) then True
      else if tag_T (cpx (load_F f)) = 4 \<and> tag_T (cpx (load_T (cpx (load_F f)))) = 2 \<and> 
              cpy (load_F f) = cpy (cpy (load_T (cpx (load_F f)))) then True
      else False
      
    else
      if list_in (pack_F 1 \<langle>cpy (load_F f), cpx (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = 2 \<and> cpy (load_F f) = (pack_T 1 0) \<and> 
              list_in (pack_F 0 \<langle>load_T (cpx (load_F f)), load_T (cpx (load_F f))\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = 2 \<and> tag_T (cpy (load_F f)) = 2 \<and> 
              list_in (pack_F 1 \<langle>load_T (cpx (load_F f)), load_T (cpy (load_F f))\<rangle>) rest then True
      else if list_in (pack_F 1 \<langle>(pack_T 2 (cpx (load_F f))), (pack_T 2 (cpy (load_F f)))\<rangle>) rest then True
      else False"

assumes check_list_def: "check_list prf := 
    if prf = Nil then True
    else if valid_step (cpi 3 prf) (cpi' 4 prf) then check_list (cpi' 4 prf)
    else False"

assumes checker_def: "is_valid_proof prf f := 
    if prf = Nil then False
    else if cpi 3 prf = f then check_list prf
    else False"


begin

definition mk_eq :: "num \<Rightarrow> num \<Rightarrow> num" where
    "mk_eq a b \<equiv> pack_F 0 \<langle>a, b\<rangle>"

definition mk_neq :: "num \<Rightarrow> num \<Rightarrow> num" where
    "mk_neq a b \<equiv> pack_F 1 \<langle>a, b\<rangle>"

definition sat :: "num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> o" where
    "sat f A D \<equiv> if tag_F f = 0 
               then eval (cpx (load_F f)) A D = eval (cpy (load_F f)) A D
               else eval (cpx (load_F f)) A D \<noteq> eval (cpy (load_F f)) A D"

lemma proof_is_bool:
    assumes "p N" and "f N"
    shows "is_valid_proof p f B"
  sorry

lemma soundness_bridge:
    assumes "is_valid_proof p f"
    shows "sat f A D"
  sorry

sublocale bga_consistent mk_eq mk_neq eval sat is_valid_proof
proof (unfold_locales)

fix a b
    assume aN: "a N" and bN: "b N"
    thus "mk_eq a b N"
      apply (unfold mk_eq_def)
      apply (rule pack_F_N)
       apply simp
      done

  next

fix a b
    assume aN: "a N" and bN: "b N"
    thus "mk_neq a b N"
      apply (unfold mk_neq_def)
      apply (rule pack_F_N)
       apply simp
      done

  next

fix p f
    assume "p N" and "f N"
    thus "is_valid_proof p f B"
      by (rule proof_is_bool)

  next

    show 
      sorry

  qed

end
end