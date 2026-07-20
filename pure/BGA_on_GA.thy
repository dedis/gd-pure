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
type_synonym pf = num  (* Proof: List of judgements *)
type_synonym val = num  (* Evaluated Value *)

type_synonym hyp = num  (* Hypothesis: list/set of formulas *)
type_synonym jdg = num  (* Judgment: \<langle>hyp, fm\<rangle> *)

abbreviation hyp_of :: "jdg \<Rightarrow> hyp" where "hyp_of J \<equiv> cpx J"
abbreviation conc_of :: "jdg \<Rightarrow> fm" where "conc_of J \<equiv> cpy J"

abbreviation mk_jdg :: "hyp \<Rightarrow> fm \<Rightarrow> jdg" (infix "\<tturnstile>" 50)
  where "G \<tturnstile> c \<equiv> \<langle>G, c\<rangle>"
abbreviation emptyH :: "hyp" ("\<emptyset>")
  where "\<emptyset> \<equiv> Nil"
abbreviation cons  :: "fm \<Rightarrow> List \<Rightarrow> List" (infixr "\<triangleright>" 65)
  where "f \<triangleright> G \<equiv> Cons f G"

abbreviation hyp_in  :: "fm \<Rightarrow> hyp \<Rightarrow> o" (infixr "\<in>" 75)
  where "f \<in> G \<equiv> mem f G"

locale suff_syntax =
  (*Encoding  *)
  fixes mk_eq :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  fixes mk_neq :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  (* Fixed Definition List*)
  fixes dfns :: "dfn"
  (*Provability. is_valid_proof \<lbrace> p \<rbrace> \<lbrace>\<Gamma> \<turnstile> f \<rbrace> \<equiv> p \<P> \<lbrakk> \<Gamma> \<turnstile> f \<rbrakk>*)
  fixes is_valid_proof :: "pf \<Rightarrow> jdg \<Rightarrow> o"

  (*Habeas Quid for Syntax Constructors *)
  assumes mk_eq_N:  "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> mk_eq a b N"
  assumes mk_neq_N: "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> mk_neq a b N"

  (*  Habeas Quid for the Proof Checker *)
  assumes proof_bool: "\<lbrakk>p N; J N\<rbrakk> \<Longrightarrow> ((is_valid_proof p J) B)"

locale suff_semantics = suff_syntax +
  (*Semantics. sat checks whether the encoding of a formula is satisfied by an assignment. eval reduces a term under an assignment*)
  fixes eval :: "tm \<Rightarrow> asn \<Rightarrow> val"
  fixes sat_fm :: "fm \<Rightarrow> asn \<Rightarrow> o"
  fixes sat_hyp :: "hyp \<Rightarrow> asn \<Rightarrow> o"

  assumes sat_hyp_nil: "sat_hyp Nil A"

  (*What Equations mean in the model *)
  assumes sat_eqE:  "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow>sat_fm (mk_eq a b) A \<Longrightarrow> eval a A = eval b A"
  assumes sat_neqE: "\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow>sat_fm (mk_neq a b) A \<Longrightarrow> eval a A \<noteq> eval b A"

locale consistent =  suff_semantics +
  (* Valid proofs yield satisfied formulas *)
  assumes soundness: "\<lbrakk>is_valid_proof p J; sat_hyp (hyp_of J) A\<rbrakk> \<Longrightarrow> sat_fm (conc_of J) A"
begin

lemma syntactically_consistent:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes p1_nat: "p1 N"
  assumes p2_nat: "p2 N"
  shows " \<not> (is_valid_proof p1 \<langle>Nil, (mk_eq a b)\<rangle> \<and> is_valid_proof p2 \<langle>Nil, (mk_neq a b)\<rangle>)"

  apply (rule contradiction[where p=" \<not> (is_valid_proof p1 \<langle>Nil, (mk_eq a b)\<rangle> \<and> is_valid_proof p2 \<langle>Nil, (mk_neq a b)\<rangle>)"])
   apply simp

proof - 
  have mk_eq_nat: " mk_eq a b N"
    using a_nat b_nat apply (rule mk_eq_N)
    done

  have mk_neq_nat: " mk_neq a b N"
    using a_nat b_nat apply (rule mk_neq_N)
    done
  have J_eq_nat: "\<langle>Nil, mk_eq a b\<rangle> N"
    using mk_eq_nat apply simp
    done

  have J_neq_nat: "\<langle>Nil, mk_neq a b\<rangle> N"
    using mk_neq_nat apply simp
    done
  show " is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> B"
    using p1_nat J_eq_nat apply (rule proof_bool)
    done

  show " is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle> B"
    using p2_nat J_neq_nat apply (rule proof_bool)
    done
  show " \<not> \<not> (is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>) \<Longrightarrow> False "

  proof -
    assume double_neg: "\<not> \<not> (is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>)"

    have conj_holds: "is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>"
      apply (rule dNegE)
      apply (rule double_neg)
      done

    have eq_prf: "is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle>"
      apply (rule conjE1)
      apply (rule conj_holds)
      done

    have neq_prf: "is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>"
      apply (rule conjE2)
      apply (rule conj_holds)
      done

    have eq_sat: "sat_fm  (conc_of \<langle>Nil, mk_eq a b\<rangle>) zero"
      apply (rule soundness)
       apply (rule eq_prf)
      using mk_eq_nat apply simp
      apply (rule sat_hyp_nil)
      done

    have eq_sat1: "sat_fm (mk_eq a b) zero"
      using eq_sat mk_eq_nat apply simp
      done

    have neq_sat: "sat_fm  (conc_of \<langle>Nil, mk_neq a b\<rangle>) zero"
      apply (rule soundness)
       apply (rule neq_prf)
      using mk_neq_nat apply simp
      apply (rule sat_hyp_nil)
      done
    have neq_sat1: "sat_fm (mk_neq a b) zero"
      using neq_sat mk_neq_nat apply simp
      done

    have eq_val: "eval a zero = eval b zero"
      apply (rule sat_eqE)
      using a_nat b_nat apply simp+
      apply (rule eq_sat1)
      done

    have neq_val: "eval a zero  \<noteq> eval b zero"
      apply (rule sat_neqE)
      using a_nat b_nat apply simp+
      apply (rule neq_sat1)
      done

    show "False"
      apply (rule exF[where P="eval a zero  = eval b zero "])
       apply (rule eq_val)
      apply (fold neq_def)
      apply (rule neq_val)
      done
  qed
qed

end

type_synonym tmtag = num
type_synonym fmtag = num


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

  (* Term Constructor Tags *)
  abbreviation T_VAR  :: num where "T_VAR \<equiv> 0"
  abbreviation T_ZERO :: num where "T_ZERO \<equiv> 1"
  abbreviation T_SUC  :: num where "T_SUC \<equiv> 2"
  abbreviation T_PRED :: num where "T_PRED \<equiv> 3"
  abbreviation T_IFZ  :: num where "T_IFZ \<equiv> 4"
  abbreviation T_APP  :: num where "T_APP \<equiv> 5"

  (* Formula Constructor Tags *)
  abbreviation F_EQ   :: num where "F_EQ \<equiv> 0"
  abbreviation F_NEQ  :: num where "F_NEQ \<equiv> 1"

(* Using the following convention:
Definitions not fundamental to the logic (like arithmetic, list etc) will be made in locales and not as axioms.
*)

locale bga_bijective_encoding =
  (*Term Encoding *)
  (* Tag of the current Constructor *)
  fixes tag_T :: "tm \<Rightarrow> tmtag"
  (* Encoding of the argument *)
  fixes load_T :: "tm \<Rightarrow> tm"
  (* Encodes the term *)
  fixes pack_T :: "tmtag \<Rightarrow> tm \<Rightarrow> tm"

  (* Formula Encoding *)
  fixes tag_F :: "fm \<Rightarrow> fmtag"
  fixes load_F :: "fm \<Rightarrow> tm"
  fixes pack_F :: "fmtag \<Rightarrow> fm \<Rightarrow> fm"

(* Fixing Definition*)
  fixes dfns :: "dfn"
  assumes dfns_N: "dfns N"
  (* AXIOMS *)
  (*Habeas Quid for the Encoder *)
  assumes pack_F_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> pack_F t L N"
  assumes tag_F_N:  "f N \<Longrightarrow> tag_F f N"
  assumes load_F_N: "f N \<Longrightarrow> load_F f N"

  assumes pack_T_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> (pack_T t L) N"
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
  (* This will require load of atomic terms(without arguments) to return 0 *)
  assumes decrease_F: "\<lbrakk>f N; f \<noteq> 0 \<rbrakk> \<Longrightarrow> load_F f < f = 1"
  assumes decrease_T: "\<lbrakk>t N; t \<noteq> 0\<rbrakk> \<Longrightarrow> load_T t < t = 1"

  assumes tag_T_zero: "tag_T 0 = T_ZERO"

  (*Monotone assumptions for Bounding *)
  assumes mono_pack_T: "(x \<le> y = 1) \<Longrightarrow> (pack_T tg x \<le> pack_T tg y =1)"
  assumes mono_pack_F: "(x \<le> y = 1) \<Longrightarrow> (pack_F tg x \<le> pack_F tg y =1)"


locale bga_semantics = bga_bijective_encoding +
  (* Semantics *)
  (* eval takes in a term, assignments and definition list
 and returns the valuation of that term*)
fixes eval :: "tm \<Rightarrow> asn \<Rightarrow> val"

  (*  Note that P does not diverge on 0 due to the implementation 
  of P in GD.thy not doing so*)
  (* We can write this definition very cleanly and without having to handle non-termination separately or use step counts as we are working in GA *)
(*
1. v_i \<Down> A(i)
2. 0 \<Down> 0
3. S(x) \<Down> S(eval(x))
4. P(x) \<Down> P(eval(x))
5. ifz a? b:c \<Down> (if eval(a)=0 then eval(b) else eval(c))
6. f_i (a, b) \<Down> eval(D(i)) for asn = \<langle>eval(a), eval(b)\<rangle>
*)
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
      eval (nth (cpx (load_T t)) dfns) 
           ((eval (cpx (cpy (load_T t))) A)\<triangleright> ((eval (cpy (cpy (load_T t))) A) \<triangleright> Nil))"
begin
definition sat :: "num \<Rightarrow> num  \<Rightarrow> o" where
    "sat f A \<equiv> if tag_F f = 0 
               then eval (cpx (load_F f)) A = eval (cpy (load_F f)) A
               else eval (cpx (load_F f)) A \<noteq> eval (cpy (load_F f)) A"

definition sat_hyp :: "hyp \<Rightarrow> asn \<Rightarrow> o" where
  "sat_hyp G A \<equiv> \<forall>f. (mem f G) \<longrightarrow> (sat f A)"
end

locale bga_subst = bga_bijective_encoding +
  fixes subst_T        :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"
  (* subst_T t j v: Inside term 't', replace variable index 'j' with term 'v' *)
  assumes subst_T_def: "subst_T t j v := 
    if tag_T t = T_VAR then 
      (if load_T t = j then v else t)
    else if tag_T t = T_ZERO then (pack_T T_ZERO 0)
    else if tag_T t = T_SUC then (pack_T T_SUC (subst_T (load_T t) j v))
    else if tag_T t = T_PRED then (pack_T T_PRED (subst_T (load_T t) j v))
    else if tag_T t = T_IFZ then 
      (pack_T T_IFZ \<langle>subst_T (cpx (load_T t)) j v 
            , \<langle>(subst_T (cpx (cpy (load_T t))) j v), 
            (subst_T (cpy (cpy (load_T t))) j v)\<rangle>\<rangle>)
    else 
      (pack_T T_APP \<langle>(cpx (load_T t)), \<langle> 
             (subst_T (cpx (cpy (load_T t))) j v), 
             (subst_T (cpy (cpy (load_T t))) j v)\<rangle>\<rangle>)"

    fixes subst_F        :: "fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  (* subst_F f j v: Inside formula 'f', replace variable index 'j' with term 'v' *)
  assumes subst_F_def: "subst_F f j v :=
    if tag_F f = F_EQ then
      pack_F F_EQ \<langle>(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)\<rangle>
    else
      pack_F F_NEQ \<langle>(subst_T (cpx (load_F f)) j v), (subst_T (cpy (load_F f)) j v)\<rangle>"

  fixes subst_body :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"    
  (* subst_body b x y  =  b[0\<mapsto>x, 1\<mapsto>y] simultaneously *)
  assumes subst_body_def: "subst_body b x y :=
    if tag_T b = T_VAR then
      (if load_T b = 0 then x else if load_T b = 1 then y else b)
    else if tag_T b = T_ZERO then b
    else if tag_T b = T_SUC  then pack_T T_SUC  (subst_body (load_T b) x y)
    else if tag_T b = T_PRED then pack_T T_PRED (subst_body (load_T b) x y)
    else if tag_T b = T_IFZ  then
      pack_T T_IFZ \<langle>subst_body (cpx (load_T b)) x y,
               \<langle>subst_body (cpx (cpy (load_T b))) x y,
                subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>
    else
      pack_T T_APP \<langle>cpx (load_T b),
               \<langle>subst_body (cpx (cpy (load_T b))) x y,
                subst_body (cpy (cpy (load_T b))) x y\<rangle>\<rangle>"

locale bga_subst_rule = bga_subst +

  fixes check_template :: "fm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> o"
(* Counts down p from max_bound to 0. 
     i is fixed to a fresh variable (e.g., f+1)
  f - formula we are trying to see if valid
  phi - premise formula
  p - template formula
  i - id of variable acting as a place holder in p
  a=b - equality being considered
 *)
  assumes check_template_def: "check_template f phi a b p i :=
    if subst_F p i a = phi \<and> subst_F p i b = f then True
    else if p > 0 = 1 then check_template f phi a b (p - 1) i
    else False"

  fixes rep_vars_T     :: "tm \<Rightarrow> tm \<Rightarrow> tm"
(* rep_vars_T t i: Replaces all leaves in term t with variable i *)
  assumes rep_vars_T_def: "rep_vars_T t i :=
    if tag_T t = T_VAR then pack_T T_VAR i
    else if tag_T t = T_ZERO then pack_T T_VAR i
    else if tag_T t = T_SUC then pack_T T_SUC (rep_vars_T (load_T t) i)
    else if tag_T t = T_PRED then pack_T T_PRED (rep_vars_T (load_T t) i)
    else if tag_T t = T_IFZ then 
      pack_T T_IFZ \<langle>rep_vars_T (cpx (load_T t)) i, 
               \<langle>rep_vars_T (cpx (cpy (load_T t))) i, 
                rep_vars_T (cpy (cpy (load_T t))) i\<rangle>\<rangle>
    else 
      pack_T T_APP \<langle>cpx (load_T t),
               \<langle>rep_vars_T (cpx (cpy (load_T t))) i, 
                rep_vars_T (cpy (cpy (load_T t))) i\<rangle>\<rangle>"

  fixes rep_vars_F     :: "fm \<Rightarrow> tm \<Rightarrow> fm"
  (* rep_vars_F f i: Replaces all leaves in formula f with variable i *)
  assumes rep_vars_F_def: "rep_vars_F f i :=
    if tag_F f = F_EQ then
      pack_F F_EQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle>
    else
      pack_F F_NEQ \<langle>rep_vars_T (cpx (load_F f)) i, rep_vars_T (cpy (load_F f)) i\<rangle>"

(* unconditional version:
  assumes find_phi_def: "find_phi f a b ptr :=
    if ptr = 0 then False
    else if check_template f (cpx ptr) a b (rep_vars_F f (f+1)) (f + 1) then True
    else find_phi f a b (cpy ptr)"
*)

  fixes find_phi       :: "jdg \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o"
(* Scans the proof list (ptr) for a valid premise J_phi = \<langle>\<Gamma>, \<phi>\<rangle>
   such that \<Gamma> matches J's context, and p[v_(f+1) \<mapsto> a] = \<phi> and p[v_(f+1) \<mapsto> b] = f *)
  assumes find_phi_def: "find_phi J a b ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J \<and> 
            check_template (conc_of J) (conc_of (list_hd ptr)) a b 
                           (rep_vars_F (conc_of J) (J + 1)) (J + 1) then True
    else find_phi J a b (list_tl ptr)"

(*unconditional version:
  assumes find_eq_def: "find_eq f rest ptr :=
    if ptr = 0 then False
    else if tag_F (cpx ptr) = 0 then
      if find_phi f (cpx (load_F (cpx ptr))) (cpy (load_F (cpx ptr))) rest then True
      else find_eq f rest (cpy ptr)
    else find_eq f rest (cpy ptr)"
*)

  fixes find_eq        :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
(* Scans the proof list (ptr) for an equality judgment J_eq = \<langle>\<Gamma>, a = b\<rangle>
   such that \<Gamma> matches J's context, and calls find_phi *)
  assumes find_eq_def: "find_eq J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J \<and> tag_F (conc_of (list_hd ptr)) = F_EQ then
      if find_phi J (cpx (load_F (conc_of (list_hd ptr)))) (cpy (load_F (conc_of (list_hd ptr)))) rest then True
      else find_eq J rest (list_tl ptr)
    else find_eq J rest (list_tl ptr)"
  fixes check_subst    :: "jdg \<Rightarrow> pf \<Rightarrow> o"

(* checking the substitution rule *)
assumes check_subst_def: "check_subst J rest := find_eq J rest rest"

locale bga_eq_rule = bga_bijective_encoding +

(*
f - formula we are trying to append to the proof
rest - rest of the proof
Proof Rules:
1. f \<turnstile> f 
2. a=b, p[x=a] \<turnstile> p[x=b]
3. \<turnstile> 0 = 0
4. a=b \<turnstile> b=a
5. a=b \<turnstile> S(a) = S(b)
6. S(a)=S(b) \<turnstile> a=b
7. a=a \<turnstile> P(S(a))=a
8. b=b, c\<noteq>0 \<turnstile> (c 0? a: b) = b
9. a=a, c=0 \<turnstile> (c 0? a: b) = a
10. a\<noteq>b \<turnstile> b\<noteq>a
11. a=a \<turnstile> S(a)\<noteq>0
12. a\<noteq>b \<turnstile> S(a)\<noteq>S(b)

*)

  fixes check_eq_rules  :: "hyp \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tmtag \<Rightarrow> tmtag \<Rightarrow> pf \<Rightarrow> o"
(* Equality Rules
1. \<Gamma> \<turnstile> 0 N
2. \<Gamma> \<turnstile> a=b \<Longrightarrow> \<Gamma> \<turnstile> b=a
3. \<Gamma> \<turnstile> a=b \<Longrightarrow> \<Gamma> \<turnstile> S(a)=S(b)
4. \<Gamma> \<turnstile> S(a)=S(b) \<Longrightarrow> \<Gamma> \<turnstile> a=b
5. \<Gamma> \<turnstile> a N \<Longrightarrow> \<Gamma> \<turnstile> P(S(a))=a
6. \<Gamma> \<turnstile> c\<noteq>0 \<Longrightarrow> \<Gamma> \<turnstile> b N \<Longrightarrow> \<Gamma> \<turnstile> (c 0? a: b)=b
7. \<Gamma> \<turnstile> c=0 \<Longrightarrow> \<Gamma> \<turnstile> a N \<Longrightarrow> \<Gamma> \<turnstile> (c 0? a: b)=a
*)
  assumes check_eq_rules_def: "check_eq_rules G lhs rhs tg_L tg_R rest :=
    if lhs = pack_T T_ZERO 0 \<and> rhs = pack_T T_ZERO 0 then True
    else if mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, lhs\<rangle>) rest then True
    else if tg_L = T_SUC \<and> tg_R = T_SUC \<and> 
            mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T rhs\<rangle>) rest then True
    else if mem (G \<tturnstile> pack_F F_EQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) rest then True
    else if tg_L = T_PRED \<and> tag_T (load_T lhs) = T_SUC \<and> 
            cpx (load_T (load_T lhs)) = rhs \<and> 
            mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest then True
    else if tg_L = T_IFZ \<and> rhs = cpy (cpy (load_T lhs)) \<and> 
            mem (G \<tturnstile> pack_F F_NEQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest \<and>
            mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest then True
    else if tg_L = T_IFZ \<and> rhs = cpx (cpy (load_T lhs)) \<and> 
            mem (G \<tturnstile> pack_F F_EQ \<langle>cpx (load_T lhs), pack_T T_ZERO 0\<rangle>) rest \<and>
            mem (G \<tturnstile> pack_F F_EQ \<langle>rhs, rhs\<rangle>) rest then True
    else False"

  fixes check_neq_rules :: "hyp \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tmtag \<Rightarrow> tmtag \<Rightarrow> pf \<Rightarrow> o"
(* Not-Equality Rules
1. \<Gamma> \<turnstile> a\<noteq>b \<Longrightarrow> \<Gamma> \<turnstile> b\<noteq>a
2. \<Gamma> \<turnstile> a N \<Longrightarrow> \<Gamma> \<turnstile> S(a)\<noteq>0
3. \<Gamma> \<turnstile> a\<noteq>b \<Longrightarrow> \<Gamma> \<turnstile> S(a)\<noteq>S(b)
4. \<Gamma> \<turnstile> S(a)\<noteq>S(b) \<Longrightarrow> \<Gamma> \<turnstile> a\<noteq>b
*)
  assumes check_neq_rules_def: "check_neq_rules G lhs rhs tg_L tg_R rest :=
    if mem (G \<tturnstile> pack_F F_NEQ \<langle>rhs, lhs\<rangle>) rest then True
    else if tg_L = T_SUC \<and> rhs = pack_T T_ZERO 0 \<and> 
            mem (G \<tturnstile> pack_F F_EQ \<langle>load_T lhs, load_T lhs\<rangle>) rest then True
    else if tg_L = T_SUC \<and> tg_R = T_SUC \<and> 
            mem (G \<tturnstile> pack_F F_NEQ \<langle>load_T lhs, load_T rhs\<rangle>) rest then True
    else if mem (G \<tturnstile> pack_F F_NEQ \<langle>pack_T T_SUC lhs, pack_T T_SUC rhs\<rangle>) rest then True
    else False"

locale bga_ind_rule = bga_subst_rule+

fixes check_ind_template :: "fm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> hyp \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o"
(*counts down 'p', testing if it is the valid induction template 
checks for a p such that:
p[v_i \<rightarrow> a] = \<phi>
\<Gamma> \<turnstile> p[v_i \<rightarrow> 0] in proof
[v_i = v_i, p]+\<Gamma> \<turnstile> p[v_i \<rightarrow> S(v_i)] in proof

*)
  assumes check_ind_template_def: "check_ind_template f phi a G p i rest :=
    if subst_F p i a = f \<and> 
       subst_F p i (pack_T T_ZERO 0) = phi \<and>
       mem (pack_F F_EQ \<langle>pack_T T_VAR i, pack_T T_VAR i\<rangle> \<triangleright> p \<triangleright> G \<tturnstile> 
                subst_F p i (pack_T T_SUC (pack_T T_VAR i))) rest
    then True
    else if p > 0 = 1 then check_ind_template f phi a G (p - 1) i rest
    else False"

  fixes find_ind_base   :: "jdg \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
(*scans the proof list for the base case judgment.
J - \<Gamma> \<turnstile> \<phi>

we check if there exists a term of the form p such that 
p[v_i \<rightarrow> a] = \<phi> and
\<Gamma> \<turnstile> p[v_i \<rightarrow> 0] is in the proof list
[v_i = v_i, p]+\<Gamma> \<turnstile> p[v_i \<rightarrow> S(v_i)] in proof

we do this by going over each judgement in the proof list and looking at its conclusion (\<psi>).
we choose i such that v_i is guaranteed to not be used in \<phi> or \<Gamma> (maybe used in \<psi> or its context,
but that doesn't matter). then we pick an upperbound such that if such a p exists it must fall within it.

*)
assumes find_ind_base_def: "find_ind_base J a rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J then
      if check_ind_template (conc_of J) (conc_of (list_hd ptr)) a (hyp_of J) 
                            (rep_vars_F (conc_of J) (J + 1)) (J + 1) rest
      then True
      else find_ind_base J a rest (list_tl ptr)
    else find_ind_base J a rest (list_tl ptr)"

  fixes check_ind       :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  (* check_ind triggers the search if the Habeas Quid premise \<Gamma> \<turnstile> a N (encoded as a=a) exists *)
  assumes check_ind_def: "check_ind J rest :=
    if mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>cpx (load_F (conc_of J)), cpx (load_F (conc_of J))\<rangle>) rest then
       find_ind_base J (cpx (load_F (conc_of J))) rest rest
    else False"

locale bga_struct_rule = bga_bijective_encoding +


fixes find_cut    :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
fixes check_cut   :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  (* Cut Rule:
  \<Gamma> \<turnstile> a \<Longrightarrow> a + \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c
  *)
  assumes find_cut_def: "find_cut J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J then
      if mem ((conc_of (list_hd ptr)) \<triangleright> (hyp_of J) \<tturnstile> (conc_of J)) rest then True
      else find_cut J rest (list_tl ptr)
    else find_cut J rest (list_tl ptr)"

  assumes check_cut_def: "check_cut J rest := find_cut J rest rest"

  fixes find_struct :: "jdg \<Rightarrow> hyp \<Rightarrow> pf \<Rightarrow> o"
  assumes find_struct_def: "find_struct J G ptr :=
    if ptr = Nil then False
    else if conc_of (list_hd ptr) = conc_of J \<and> subset (hyp_of (list_hd ptr)) G then True
    else find_struct J G (list_tl ptr)"

  fixes check_struct :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  assumes check_struct_def: "check_struct J rest := find_struct J (hyp_of J) rest"

locale bga_app_rule = bga_subst_rule +

(*
J d x y
let J = \<Gamma> \<turnstile> f
checks if
1. \<Gamma> \<turnstile> x=x & \<Gamma> \<turnstile> y=y in proof
2. \<Gamma> \<turnstile> f [d(x,y) \<rightarrow> D_d\<langle>x, y\<rangle>] in proof
*)
fixes app_try :: "jdg \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  assumes app_try_def: "app_try J d x y rest :=
    mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest \<and> 
    mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest \<and>  
    find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest"

(* Tries to see if application is satisfied for some y*)
fixes app_y :: "jdg \<Rightarrow> num \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  assumes app_y_def: "app_y J d x y rest :=
    if app_try J d x y rest then True
    else if y > 0 = 1 then app_y J d x (y - 1) rest
    else False"

(* Tries to see if application is satisfied for some x, y with y bounded by f (where J= \<Gamma>\<turnstile>f) *)
  fixes app_x :: "jdg \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  assumes app_x_def: "app_x J d x rest :=
    if app_y J d x (conc_of J) rest then True
    else if x > 0 = 1 then app_x J d (x - 1) rest
    else False"

(*Given a J and an upperbound for def, sees if application can be satisfied by any d,x,y triplet *)
  fixes app_d :: "jdg \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  assumes app_d_def: "app_d J d rest :=
    if d < len dfns = 1 then
      (if app_x J d (conc_of J) rest then True
       else if d > 0 = 1 then app_d J (d - 1) rest else False)
    else
      (if d > 0 = 1 then app_d J (d - 1) rest else False)"

  fixes check_app :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  assumes check_app_def: "check_app J rest := app_d J (len dfns - 1) rest"

locale bga_proof_check = bga_subst_rule+ bga_eq_rule+ bga_ind_rule + bga_struct_rule + bga_app_rule+
(*checks if a judgement can be appended to the proof*)
fixes valid_step :: "jdg \<Rightarrow> pf \<Rightarrow> o"

(* The main step check
1. 1 hyp Rule
2. 1 Cut Rule
3. 1 Subst Rule
4. 1 Induction Rule
5. 7 Equality Rules
6. 4 Not-equality rules
7. 1 app2I rule
8. 1 wk1 rule
sub1
 *)
  assumes valid_step_def: "valid_step J rest :=
    if mem (conc_of J) (hyp_of J) then True
    else if check_cut J rest then True
    else if check_subst J rest then True
    else if check_ind J rest then True
    else if check_app J rest then True
    else if check_struct J rest then True
    else if tag_F (conc_of J) = F_EQ then
      check_eq_rules (hyp_of J) (cpx (load_F (conc_of J))) (cpy (load_F (conc_of J))) 
                     (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest
    else
      check_neq_rules (hyp_of J) (cpx (load_F (conc_of J))) (cpy (load_F (conc_of J))) 
                      (tag_T (cpx (load_F (conc_of J)))) (tag_T (cpy (load_F (conc_of J)))) rest"
(* unconditional version

assumes valid_step_def: "valid_step f rest := 
    if mem f rest then True
    
    else if check_subst f rest then True

    else if tag_F f = F_EQ then
      if cpx (load_F f) = (pack_T T_ZERO 0) \<and> cpy (load_F f) = (pack_T T_ZERO 0) then True
      else if list_in (pack_F F_EQ \<langle>cpy (load_F f), cpx (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_SUC \<and> tag_T (cpy (load_F f)) = T_SUC \<and> 
              list_in (pack_F F_EQ \<langle>load_T (cpx (load_F f)), load_T (cpy (load_F f))\<rangle>) rest then True
      else if list_in (pack_F F_EQ \<langle>(pack_T T_SUC (cpx (load_F f))), (pack_T T_SUC (cpy (load_F f)))\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_PRED \<and> tag_T (load_T (cpx (load_F f))) = T_SUC \<and> 
              cpx (load_T (load_T (cpx (load_F f)))) = cpy (load_F f) \<and> 
              list_in (pack_F F_EQ \<langle>cpy (load_F f), cpy (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_IFZ \<and> 
              cpy (load_F f) = cpy (cpy (load_T (cpx (load_F f)))) \<and> 
              list_in (pack_F F_NEQ \<langle>cpx (load_T (cpx (load_F f))), pack_T T_ZERO 0\<rangle>) rest \<and>
              list_in (pack_F F_EQ \<langle>cpy (load_F f), cpy (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_IFZ \<and> 
              cpy (load_F f) = cpx (cpy (load_T (cpx (load_F f)))) \<and> 
              list_in (pack_F F_EQ \<langle>cpx (load_T (cpx (load_F f))), pack_T T_ZERO 0\<rangle>) rest \<and>
              list_in (pack_F F_EQ \<langle>cpy (load_F f), cpy (load_F f)\<rangle>) rest then True
      else False
    else
      if list_in (pack_F F_NEQ \<langle>cpy (load_F f), cpx (load_F f)\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_SUC \<and> cpy (load_F f) = (pack_T T_ZERO 0) \<and> 
              list_in (pack_F F_EQ \<langle>load_T (cpx (load_F f)), load_T (cpx (load_F f))\<rangle>) rest then True
      else if tag_T (cpx (load_F f)) = T_SUC \<and> tag_T (cpy (load_F f)) = T_SUC \<and> 
              list_in (pack_F F_EQ \<langle>load_T (cpx (load_F f)), load_T (cpy (load_F f))\<rangle>) rest then True
      else if list_in (pack_F F_EQ \<langle>(pack_T T_SUC (cpx (load_F f))), (pack_T T_SUC (cpy (load_F f)))\<rangle>) rest then True
      else False"
*)

(* Checks if the given head of proof is valid*)
fixes check_list :: "pf \<Rightarrow> o"
assumes check_list_def: "check_list prf := 
    if prf = Nil then True
    else if valid_step (list_hd prf) (list_tl prf) then check_list (list_tl prf)
    else False"

(*checks if the given proof is valid for the given judgement*)
fixes is_valid_proof :: "pf \<Rightarrow> jdg \<Rightarrow> o"

assumes is_valid_proof_def: "is_valid_proof prf J := 
    if prf = Nil then False
    else if list_hd prf = J then check_list prf
    else False"

locale bga_full = bga_semantics + bga_proof_check
begin

definition mk_eq :: "num \<Rightarrow> num \<Rightarrow> num" where
    "mk_eq a b \<equiv> pack_F 0 \<langle>a, b\<rangle>"

definition mk_neq :: "num \<Rightarrow> num \<Rightarrow> num" where
    "mk_neq a b \<equiv> pack_F 1 \<langle>a, b\<rangle>"


lemma mk_eq_N':
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  shows "mk_eq a b N"
  unfolding mk_eq_def  apply (rule pack_F_N)
  using a_nat b_nat  apply simp+
  done

lemma mk_neq_N':
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  shows "mk_neq a b N"
  unfolding mk_neq_def  apply (rule pack_F_N)
  using a_nat b_nat  apply simp+
  done

lemma sat_hyp_nil': "sat_hyp Nil A"
  unfolding sat_hyp_def
  apply (rule forallI)
  apply (rule implI)
   apply simp
proof - 
  fix f
  assume f_nat: "f N"
  assume f_in_empty: "f \<in> \<emptyset>"
  show "sat f A"
    apply (rule exF[where P = "f \<in> \<emptyset>"])
     apply (rule f_in_empty)
    apply (rule mem_nil)
    done
qed
lemma sat_hyp_mem: "f N \<Longrightarrow> f \<in> G \<Longrightarrow> sat_hyp G A \<Longrightarrow> sat f A"
  unfolding sat_hyp_def
proof -
  assume f_nat: "f N" and f_in: "f \<in> G" and all: "\<forall>g. g \<in> G \<longrightarrow> sat g A"
  have imp: "f \<in> G \<longrightarrow> sat f A"
    apply (rule forallE[where a = f]) apply (rule all) apply (rule f_nat) done
  show "sat f A"
    apply (rule implE[where a = "f \<in> G"]) apply (rule imp) apply (rule f_in) done
qed

lemma subhyp_mem: "(f N) \<Longrightarrow> subhyp G' G \<Longrightarrow> f \<in> G' \<Longrightarrow> f \<in> G"
  sorry

lemma sat_hyp_subhyp: "subhyp G' G \<Longrightarrow> G' N \<Longrightarrow> sat_hyp G A \<Longrightarrow> sat_hyp G' A"
proof -
  assume sub: "subhyp G' G" and G'_nat: "G' N" and satG: "sat_hyp G A"
  show "sat_hyp G' A"
    unfolding sat_hyp_def
    apply (rule forallI)
    apply (rule implI)
     apply (simp add: G'_nat)
    apply (rule G'_nat)
  proof -
    fix f
    assume f_nat: "f N" and f_in': "f \<in> G'"
    have fG: "f \<in> G" using f_nat sub f_in' by (rule subhyp_mem)
    show "sat f A" using f_nat fG satG by (rule sat_hyp_mem)
  qed
qed

lemma sat_eqE': "a N \<Longrightarrow> b N \<Longrightarrow> sat (mk_eq a b) A \<Longrightarrow> eval a A = eval b A"
proof -
  assume a: "a N" and b: "b N" and h: "sat (mk_eq a b) A"
  have p: "\<langle>a, b\<rangle> N" using a b by simp
  have tg: "tag_F (mk_eq a b) = F_EQ"
    unfolding mk_eq_def apply (rule tag_pack_F)
    using a b apply simp+
    done
  have ld: "load_F (mk_eq a b) = \<langle>a, b\<rangle>"
    unfolding mk_eq_def apply (rule load_pack_F)
    using a b apply simp+
    done
  from h[unfolded sat_def] show "eval a A = eval b A"
  proof -
  have step: "eval (hyp_of (load_F (mk_eq a b))) A
            = eval (conc_of (load_F (mk_eq a b))) A"
    by (rule cond_thenE[OF tg h[unfolded sat_def]])
  from step show "eval a A = eval b A"
    using a b apply (simp add: ld)
    apply (rule eq_impl_term2)
    apply simp
    done
qed
qed


lemma subst_T_N:
  assumes t: "t N" and j: "j N" and v: "v N"
  shows "subst_T t j v N"
proof (rule strong_induction[where a=t])
  show "t N" by (rule t)
next
  show "subst_T 0 j v N"
      proof -
    have zN: "pack_T T_ZERO 0 N"
      apply (rule pack_T_N) 
       apply simp 
      done
    have g1: "\<not> (tag_T 0 = T_VAR)" 
      by (simp add: tag_T_zero)
    have g2: "tag_T 0 = T_ZERO"     
      by (rule tag_T_zero)
    have red: "subst_T 0 j v = pack_T T_ZERO 0"
      apply (rule defE[OF subst_T_def[where t=0 and j=j and v=v]])
      apply (rule condI2Eq[OF g1 zN])
      apply (rule condI1Eq[OF g2 zN])
      using zN apply simp
      done
    show "subst_T 0 j v N" using red zN by simp
  qed
next
  fix x assume x: "x N" and IH: "\<And>y. y N \<Longrightarrow> y \<le> x = 1 \<Longrightarrow> subst_T y j v N"
  have sxN:  "S x N"          
    by (rule natS[OF x])
  have sxnz: "S x \<noteq> 0"        
    by (rule sucNonZero[OF x])
  have L:    "load_T (S x) N" 
    by (rule load_T_N[OF sxN])
  have Lx:   "load_T (S x) \<le> x = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF sxN sxnz] L x])
  have cxL:  "cpx (load_T (S x)) N" 
    by (rule cpx_terminates[OF L])
  have cyL:  "cpy (load_T (S x)) N" 
    by (rule cpy_terminates[OF L])
  have cxLx: "cpx (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cxL L x cpx_mono[OF L] Lx])
  have cyLx: "cpy (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cyL L x cpy_mono[OF L] Lx])
  have cxcyL: "cpx (cpy (load_T (S x))) N" 
    by (rule cpx_terminates[OF cyL])
  have cycyL: "cpy (cpy (load_T (S x))) N" 
    by (rule cpy_terminates[OF cyL])
  have cxcyLx: "cpx (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cxcyL cyL x cpx_mono[OF cyL] cyLx])
  have cycyLx: "cpy (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cycyL cyL x cpy_mono[OF cyL] cyLx])
  have r0: "subst_T (load_T (S x)) j v N"             
    by (rule IH[OF L Lx])
  have r1: "subst_T (cpx (load_T (S x))) j v N"       
    by (rule IH[OF cxL cxLx])
  have r2: "subst_T (cpx (cpy (load_T (S x)))) j v N" 
    by (rule IH[OF cxcyL cxcyLx])
  have r3: "subst_T (cpy (cpy (load_T (S x)))) j v N" 
    by (rule IH[OF cycyL cycyLx])  
    (* guards *)
  have tgN:   "tag_T (S x) N"             
    by (rule tag_T_N[OF sxN])
  have gVAR:  "(tag_T (S x) = T_VAR) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gZERO: "(tag_T (S x) = T_ZERO) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gSUC:  "(tag_T (S x) = T_SUC) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gPRED: "(tag_T (S x) = T_PRED) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gIFZ:  "(tag_T (S x) = T_IFZ) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  (* the six branches are all N *)
  have A1N: "(if load_T (S x) = j then v else S x) N"
    apply (rule condT[OF _ v sxN]) 
    apply (rule eqBool[OF L j]) 
    done
  have A2N: "pack_T T_ZERO 0 N"
    apply (rule pack_T_N) 
     apply simp 
    done
  have A3N: "pack_T T_SUC (subst_T (load_T (S x)) j v) N"
    apply (rule pack_T_N)
     apply simp
    apply (rule r0) 
    done
  have A4N: "pack_T T_PRED (subst_T (load_T (S x)) j v) N"
    apply (rule pack_T_N)
     apply simp
    apply (rule r0)
    done
  have iffN: "\<langle>subst_T (cpx (load_T (S x))) j v,
               \<langle>subst_T (cpx (cpy (load_T (S x)))) j v,
                subst_T (cpy (cpy (load_T (S x)))) j v\<rangle>\<rangle> N"
    using r1 r2 r3
    by simp
  have A5N: "pack_T T_IFZ \<langle>subst_T (cpx (load_T (S x))) j v,
               \<langle>subst_T (cpx (cpy (load_T (S x)))) j v,
                subst_T (cpy (cpy (load_T (S x)))) j v\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule r1)
    apply (rule r2)
    apply (rule r3)
    done

  have A6N: "pack_T T_APP \<langle>cpx (load_T (S x)),
               \<langle>subst_T (cpx (cpy (load_T (S x)))) j v,
                subst_T (cpy (cpy (load_T (S x)))) j v\<rangle>\<rangle> N"
    apply (rule pack_T_N)
     apply simp
    apply (rule L)
    apply (rule r2)
    apply (rule r3)
    done

  show "subst_T (S x) j v N"
    apply (rule defE[OF subst_T_def[where t="S x" and j=j and v=v]])
    apply (rule condT[OF gVAR A1N])
    apply (rule condT[OF gZERO A2N])
    apply (rule condT[OF gSUC A3N])
    apply (rule condT[OF gPRED A4N])
    apply (rule condT[OF gIFZ A5N])
    apply (rule A6N)
    done
qed

lemma subst_body_N:
  assumes b: "b N" and xa: "x N" and ya: "y N"
  shows "subst_body b x y N"
proof (rule strong_induction[where a=b])
  show "b N"
    by (rule b)
next
  show "subst_body 0 x y N"
    by (rule defE[OF subst_body_def[where b=0 and x=x and y=y]],
        simp add: tag_T_zero)
next
  fix w assume w: "w N" and IH: "\<And>z. z N \<Longrightarrow> z \<le> w = 1 \<Longrightarrow> subst_body z x y N"
  have swN:  "S w N"          using w
    by simp
  have swnz: "S w \<noteq> 0"       
    by (rule sucNonZero[OF w])
  have L:    "load_T (S w) N"
    by (rule load_T_N[OF swN])
  have Lw:   "load_T (S w) \<le> w = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF swN swnz] L w])
  have cxL: "cpx (load_T (S w)) N" using L
    by simp
  have cyL: "cpy (load_T (S w)) N" using L
    by simp
  have cxLw: "cpx (load_T (S w)) \<le> w = 1"
    by (rule leq_trans[OF cxL L w cpx_mono[OF L] Lw])
  have cyLw: "cpy (load_T (S w)) \<le> w = 1"
    by (rule leq_trans[OF cyL L w cpy_mono[OF L] Lw])
  have cxcyL: "cpx (cpy (load_T (S w))) N" using cyL
    by simp
  have cycyL: "cpy (cpy (load_T (S w))) N" using cyL
    by simp
  have cxcyLw: "cpx (cpy (load_T (S w))) \<le> w = 1"
    by (rule leq_trans[OF cxcyL cyL w cpx_mono[OF cyL] cyLw])
  have cycyLw: "cpy (cpy (load_T (S w))) \<le> w = 1"
    by (rule leq_trans[OF cycyL cyL w cpy_mono[OF cyL] cyLw])
  have r0: "subst_body (load_T (S w)) x y N"           
    by (rule IH[OF L Lw])
  have r1: "subst_body (cpx (load_T (S w))) x y N"     
    by (rule IH[OF cxL cxLw])
  have r2: "subst_body (cpx (cpy (load_T (S w)))) x y N"
    by (rule IH[OF cxcyL cxcyLw])
  have r3: "subst_body (cpy (cpy (load_T (S w)))) x y N"
    by (rule IH[OF cycyL cycyLw])
  have tgN:   "tag_T (S w) N"            
    by (rule tag_T_N[OF swN])
  have gVAR:  "(tag_T (S w) = T_VAR) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gZERO: "(tag_T (S w) = T_ZERO) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gSUC:  "(tag_T (S w) = T_SUC) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gPRED: "(tag_T (S w) = T_PRED) B"  
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  have gIFZ:  "(tag_T (S w) = T_IFZ) B"   
    apply (rule eqBool[OF tgN]) 
    apply simp 
    done
  
  have ldN: "load_T (S w) N" by (rule L)
  have gL0: "(load_T (S w) = 0) B" 
    apply (rule eqBool[OF ldN]) 
    apply simp 
    done
  have gL1: "(load_T (S w) = 1) B" 
    apply (rule eqBool[OF ldN]) 
    apply simp 
    done
  
  have A1N: "(if load_T (S w) = 0 then x else if load_T (S w) = 1 then y else S w) N"
    apply (rule condT[OF gL0 xa])
    apply (rule condT[OF gL1 ya swN])
    done
  have A2N: "S w N" 
    by (rule swN)
  
  have A3N: "pack_T T_SUC (subst_body (load_T (S w)) x y) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have A4N: "pack_T T_PRED (subst_body (load_T (S w)) x y) N"
    apply (rule pack_T_N) 
     apply simp 
    apply (rule r0) 
    done
    
  have iffN: "\<langle>subst_body (cpx (load_T (S w))) x y,
               \<langle>subst_body (cpx (cpy (load_T (S w)))) x y,
                subst_body (cpy (cpy (load_T (S w)))) x y\<rangle>\<rangle> N"
    using r1 r2 r3 by simp

  have A5N: "pack_T T_IFZ \<langle>subst_body (cpx (load_T (S w))) x y,
               \<langle>subst_body (cpx (cpy (load_T (S w)))) x y,
                subst_body (cpy (cpy (load_T (S w)))) x y\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule r1)
    apply (rule r2)
    apply (rule r3)
    done

  have A6N: "pack_T T_APP \<langle>cpx (load_T (S w)),
               \<langle>subst_body (cpx (cpy (load_T (S w)))) x y,
                subst_body (cpy (cpy (load_T (S w)))) x y\<rangle>\<rangle> N"
    apply (rule pack_T_N)
    apply simp
    apply (rule L)
    apply (rule r2)
    apply (rule r3)
    done

  show "subst_body (S w) x y N"
    apply (rule defE[OF subst_body_def[where b="S w" and x=x and y=y]])
    apply (rule condT[OF gVAR A1N])
    apply (rule condT[OF gZERO A2N])
    apply (rule condT[OF gSUC A3N])
    apply (rule condT[OF gPRED A4N])
    apply (rule condT[OF gIFZ A5N])
    apply (rule A6N)
    done
qed

(* ===================== rep_vars_T_N (same skeleton, no j/v) ===================== *)
lemma rep_vars_T_N:
  assumes t: "t N" and i: "i N"
  shows "rep_vars_T t i N"
proof (rule strong_induction[where a=t])
  show "t N" by (rule t)
next
  show "rep_vars_T 0 i N"
    by (rule defE[OF rep_vars_T_def[where t=0 and i=i]],
        simp add: tag_T_zero pack_T_N)                 (* T_ZERO branch -> pack_T T_VAR i *)
next
  fix x assume x: "x N" and IH: "\<And>y. y N \<Longrightarrow> y \<le> x = 1 \<Longrightarrow> rep_vars_T y i N"
  have sxN:  "S x N"          using x by simp
  have sxnz: "\<not> (S x = 0)"    using x by simp
  have L:    "load_T (S x) N" by (rule load_T_N[OF sxN])
  have Lx:   "load_T (S x) \<le> x = 1"
    by (rule le_suc_implies_leq[OF decrease_T[OF sxN sxnz] L x])
  have cxL: "cpx (load_T (S x)) N" using L by simp
  have cyL: "cpy (load_T (S x)) N" using L by simp
  have cxLx: "cpx (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cpx_mono[OF L] Lx]; simp add: cxL L x)
  have cyLx: "cpy (load_T (S x)) \<le> x = 1"
    by (rule leq_trans[OF cpy_mono[OF L] Lx]; simp add: cyL L x)
  have cxcyL: "cpx (cpy (load_T (S x))) N" using cyL by simp
  have cycyL: "cpy (cpy (load_T (S x))) N" using cyL by simp
  have cxcyLx: "cpx (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cpx_mono[OF cyL] cyLx]; simp add: cxcyL cyL x)
  have cycyLx: "cpy (cpy (load_T (S x))) \<le> x = 1"
    by (rule leq_trans[OF cpy_mono[OF cyL] cyLx]; simp add: cycyL cyL x)
  have r0: "rep_vars_T (load_T (S x)) i N"            by (rule IH[OF L Lx])
  have r1: "rep_vars_T (cpx (load_T (S x))) i N"      by (rule IH[OF cxL cxLx])
  have r2: "rep_vars_T (cpx (cpy (load_T (S x)))) i N" by (rule IH[OF cxcyL cxcyLx])
  have r3: "rep_vars_T (cpy (cpy (load_T (S x)))) i N" by (rule IH[OF cycyL cycyLx])
  show "rep_vars_T (S x) i N"
    apply (rule defE[OF rep_vars_T_def[where t="S x" and i=i]])
    apply (insert x i sxN L cxL r0 r1 r2 r3)
    apply (auto intro: pack_T_N)
    done
qed

(* ===================== the one-step F versions ===================== *)
lemma subst_F_N:
  assumes f: "f N" and j: "j N" and v: "v N"
  shows "subst_F f j v N"
  apply (rule defE[OF subst_F_def[where f=f and j=j and v=v]])
  apply (insert f j v subst_T_N[OF _ j v] pack_F_N)
  apply (auto intro: pack_F_N subst_T_N)
  done

lemma rep_vars_F_N:
  assumes f: "f N" and i: "i N"
  shows "rep_vars_F f i N"
  apply (rule defE[OF rep_vars_F_def[where f=f and i=i]])
  apply (insert f i rep_vars_T_N[OF _ i] pack_F_N)
  apply (auto intro: pack_F_N rep_vars_T_N)
  done

(* ===================== subset_bool (list-rec, mem_bool template) ===================== *)
lemma subset_bool [auto]:
  assumes A: "A N" and G: "G N"
  shows "subset A G B"
proof (rule list_induct[OF A])
  show "subset Nil G B" by (rule defE[OF subset_def[where A=Nil]], simp)
next
  fix h t assume h: "h N" and t: "t N" and IH: "subset t G B"
  show "subset (Cons h t) G B"
    by (rule defE[OF subset_def[where A="Cons h t"]], insert G h t IH, simp+)
qed

lemma subst_F_N:    "\<lbrakk>f N; j N; v N\<rbrakk> \<Longrightarrow> subst_F f j v N"
  sorry

lemma subst_body_N: "\<lbrakk>b N; x N; y N\<rbrakk> \<Longrightarrow> subst_body b x y N"
  sorry

lemma rep_vars_F_N: "\<lbrakk>f N; i N\<rbrakk> \<Longrightarrow> rep_vars_F f i N"
  sorry

lemma check_template_bool [auto]:
  assumes f: "f N" and phi: "phi N" and a: "a N" and b: "b N" and i: "i N" and p: "p N"
  shows "check_template f phi a b p i B"
proof (rule ind[OF p])
  show "check_template f phi a b 0 i B"
    apply (rule defE[OF check_template_def[where p=0]], insert f phi a b i)
    apply simp
    apply (rule condTB[OF _ true_bool false_bool])
    using subst_F_N[OF nat0 i a] subst_F_N[OF nat0 i b] phi f by auto
next
  fix k assume k: "k N" and IH: "check_template f phi a b k i B"
  show "check_template f phi a b (S k) i B"
    apply (rule defE[OF check_template_def[where p="S k"]], insert f phi a b i k IH)
    apply simp
    apply (rule condTB[OF _ true_bool IH])
    using subst_F_N[OF natS[OF k] i a] subst_F_N[OF natS[OF k] i b] phi f by auto

qed

lemma app_try_bool [auto]:
  assumes J: "J N" and d: "d N" and x: "x N" and y: "y N" and r: "rest N"
      and dr: "d < len dfns = 1"
  shows "app_try J d x y rest B"
proof (rule defE[OF app_try_def[where J=J and d=d and x=x and y=y and rest=rest]])
  (* nat-ness of the two equality judgements  (\<TTurnstile> is \<langle>_,_\<rangle>, F_EQ \<equiv> 0) *)
  have hj:  "hyp_of J N"             using J by simp
  have xx:  "\<langle>x, x\<rangle> N"              using x by simp
  have yy:  "\<langle>y, y\<rangle> N"              using y by simp
  have pfx: "pack_F F_EQ \<langle>x, x\<rangle> N"  by (rule pack_F_N[OF _ xx], simp)
  have pfy: "pack_F F_EQ \<langle>y, y\<rangle> N"  by (rule pack_F_N[OF _ yy], simp)
  have jxx: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) N" using hj pfx by simp
  have jyy: "(hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) N" using hj pfy by simp
  (* nat-ness of the find_phi arguments  (T_APP \<equiv> 5) *)
  have ndf: "nth d dfns N"
    using dfns_N dr apply (rule nth_in_range_N)
    done

  have sb:  "subst_body (nth d dfns) x y N" by (rule subst_body_N[OF ndf x y])
  have dxy: "\<langle>d, \<langle>x, y\<rangle>\<rangle> N"                 using d x y by simp
  have pT:  "pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle> N"    by (rule pack_T_N[OF _ dxy], simp)
  (* booleanness of the three conjuncts *)
  have m1: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest B" by (rule mem_bool[OF jxx r])
  have m2: "mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest B" by (rule mem_bool[OF jyy r])
  have fp: "find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest B"
           by (rule find_phi_bool[OF J sb pT r])
  (* combine via the anonymous [auto] conjunction-booleanness lemma (GD.thy line 2981) *)
  show "(mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>x, x\<rangle>) rest
         \<and> mem (hyp_of J \<tturnstile> pack_F F_EQ \<langle>y, y\<rangle>) rest
         \<and> find_phi J (subst_body (nth d dfns) x y) (pack_T T_APP \<langle>d, \<langle>x, y\<rangle>\<rangle>) rest) B"
    using m1 m2 fp by auto
qed

lemma sat_neqE': "a N \<Longrightarrow> b N \<Longrightarrow> sat (mk_neq a b) A \<Longrightarrow> eval a A \<noteq> eval b A"
proof -
  assume a: "a N" and b: "b N" and h: "sat (mk_neq a b) A"
  have p: "\<langle>a, b\<rangle> N" using a b by simp
  have tg: "tag_F (mk_neq a b) = F_NEQ"
    unfolding mk_neq_def apply (rule tag_pack_F)
    using a b apply simp+
    done
  have tg_ne: "\<not> (tag_F (mk_neq a b) = F_EQ)"
    using tg by simp
  have ld: "load_F (mk_neq a b) = \<langle>a, b\<rangle>"
    unfolding mk_neq_def apply (rule load_pack_F)
    using a b apply simp+
    done
  have step: "eval (hyp_of (load_F (mk_neq a b))) A
            \<noteq> eval (conc_of (load_F (mk_neq a b))) A"
    by (rule notcond_thenE[OF tg_ne h[unfolded sat_def]])
  from step show "eval a A \<noteq> eval b A"
    using a b by (simp add: ld)
qed

lemma find_struct_bool [auto]:
  assumes J: "J N" and G: "G N" and ptr: "ptr N"
  shows "find_struct J G ptr B"
proof (rule list_induct[OF ptr])
  show "find_struct J G Nil B" by (rule defE[OF find_struct_def[where ptr=Nil]], simp)
next
  fix h t assume h: "h N" and t: "t N" and IH: "find_struct J G t B"
  show "find_struct J G (Cons h t) B"
    by (rule defE[OF find_struct_def[where ptr="Cons h t"]], insert J G h t IH, simp+)
qed



lemma proof_is_bool: "p N \<Longrightarrow> J N \<Longrightarrow> is_valid_proof p J B"
  sorry

lemma soundness_bridge: "is_valid_proof p J \<Longrightarrow> sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
  sorry

sublocale consistent mk_eq mk_neq dfns is_valid_proof eval sat sat_hyp
proof (unfold_locales)
  show "\<And>a b.   a N \<Longrightarrow> b N \<Longrightarrow> mk_eq a b N"                         by (rule mk_eq_N')
  show "\<And>a b.   a N \<Longrightarrow> b N \<Longrightarrow> mk_neq a b N"                        by (rule mk_neq_N')
  show "\<And>p J.   p N \<Longrightarrow> J N \<Longrightarrow> is_valid_proof p J B"                by (rule proof_is_bool)
  show "\<And>A.     sat_hyp Nil A"                                          by (rule sat_hyp_nil')
  show "\<And>a b A. a N \<Longrightarrow> b N \<Longrightarrow> sat (mk_eq a b) A \<Longrightarrow> eval a A = eval b A"   by (rule sat_eqE')
  show "\<And>a b A. a N \<Longrightarrow> b N \<Longrightarrow> sat (mk_neq a b) A \<Longrightarrow> eval a A \<noteq> eval b A"  by (rule sat_neqE')
  show "\<And>p J A. is_valid_proof p J \<Longrightarrow> sat_hyp (hyp_of J) A \<Longrightarrow> sat (conc_of J) A"
    by (rule soundness_bridge)
qed

end
end