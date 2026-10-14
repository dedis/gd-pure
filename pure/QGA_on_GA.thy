theory QGA_on_GA
  imports GD
begin

(*
  QGA arithmetized inside QGA, as BGA_on_GA.thy does for BGA: formulas and
  proofs are coded as numbers, a proof checker and a semantics are QGA
  recursive definitions, and the aim is to prove the checker sound, giving
  consistency of QGA inside QGA.  Everything is relative to an abstract
  encoding; qga_encode.thy instantiates it.

  Status: unfinished and abandoned (see the appendix of docs/report_omar).
  Many lemmas are sorried, so nothing here is established.

  Two semantic layers:
  (1) evT k t A / evF k f A: fuelled evaluation, total and decided at each
      fuel k.  evF returns 2 (true), 1 (false) or 0 (no verdict yet).
  (2) wsat f A / wunsat f A: a "witnessed" semantics (after RGA's witnessed
      variant): the official verdict plus the facts its quantifier
      certificates promise.  Soundness is proved into this layer.
  The forall-introduction certificate is the tail of the proof being checked,
  so no internal completeness lemma is needed.
*)

section \<open>Type aliases\<close>

type_synonym tm  = num  (* QGA term *)
type_synonym fm  = num  (* QGA formula *)
type_synonym asn = num  (* assignment; entry 0 = bottom, S v = value v *)
type_synonym dfn = num  (* definition list *)
type_synonym pf  = num  (* proof: list of judgments *)
type_synonym val = num  (* evaluated value *)

type_synonym hyp = num  (* hypothesis list *)
type_synonym jdg = num  (* judgment \<langle>hyp, fm\<rangle> *)

abbreviation hyp_of :: "jdg \<Rightarrow> hyp" where "hyp_of J \<equiv> cpx J"
abbreviation conc_of :: "jdg \<Rightarrow> fm" where "conc_of J \<equiv> cpy J"

abbreviation mk_jdg :: "hyp \<Rightarrow> fm \<Rightarrow> jdg" (infix "\<tturnstile>" 50)
  where "G \<tturnstile> c \<equiv> \<langle>G, c\<rangle>"
abbreviation emptyH :: "hyp" ("\<emptyset>")
  where "\<emptyset> \<equiv> Nil"
abbreviation consH :: "fm \<Rightarrow> List \<Rightarrow> List" (infixr "\<triangleright>" 65)
  where "f \<triangleright> G \<equiv> Cons f G"

(* payloads are right-nested tuples *)
abbreviation pfst :: "num \<Rightarrow> num" where "pfst x \<equiv> cpx x"
abbreviation psnd :: "num \<Rightarrow> num" where "psnd x \<equiv> cpx (cpy x)"
abbreviation pthd :: "num \<Rightarrow> num" where "pthd x \<equiv> cpy (cpy x)"


section \<open>The abstract consistency skeleton\<close>

text \<open>
  Unlike BGA, QGA has negation, so consistency is stated directly: no formula
  is both provable and refutable from no hypotheses.
\<close>

locale qga_suff_syntax =
  (* the encoded negation *)
  fixes mk_not :: "fm \<Rightarrow> fm"
  (* the proof checker: \<open>is_valid_proof p J\<close> = "p is a valid proof of J" *)
  fixes is_valid_proof :: "pf \<Rightarrow> jdg \<Rightarrow> o"

  assumes mk_not_N: "f N \<Longrightarrow> mk_not f N"
  assumes proof_bool: "\<lbrakk>p N; J N\<rbrakk> \<Longrightarrow> (is_valid_proof p J) B"

locale qga_suff_semantics = qga_suff_syntax +
  (* the witnessed semantics *)
  fixes wsat    :: "fm \<Rightarrow> asn \<Rightarrow> o"
  fixes wunsat  :: "fm \<Rightarrow> asn \<Rightarrow> o"
  (* official satisfaction of a hypothesis list, used only in antecedents *)
  fixes sat_hyp :: "hyp \<Rightarrow> asn \<Rightarrow> o"

  assumes sat_hyp_nil: "sat_hyp Nil A"

  (* the negation clause *)
  assumes neg_clause: "\<lbrakk>f N; wsat (mk_not f) A\<rbrakk> \<Longrightarrow> wunsat f A"

  (* exclusivity, proved in qga_witnessed by structural induction *)
  assumes excl: "\<lbrakk>f N; A N; wsat f A; wunsat f A\<rbrakk> \<Longrightarrow> False"

locale qga_consistent = qga_suff_semantics +
  assumes soundness:
    "\<lbrakk>is_valid_proof p J; sat_hyp (hyp_of J) A; A N\<rbrakk> \<Longrightarrow> wsat (conc_of J) A"
begin

theorem syntactically_consistent:
  assumes f_nat:  "f N"
  assumes p1_nat: "p1 N"
  assumes p2_nat: "p2 N"
  shows "\<not> (is_valid_proof p1 \<langle>Nil, f\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_not f\<rangle>)"
proof (rule contradiction
    [where p = "\<not> (is_valid_proof p1 \<langle>Nil, f\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_not f\<rangle>)"])
  have nf_nat: "mk_not f N" by (rule mk_not_N[OF f_nat])
  have J1_nat: "\<langle>Nil, f\<rangle> N" using f_nat by simp
  have J2_nat: "\<langle>Nil, mk_not f\<rangle> N" using nf_nat by simp
  have b1: "is_valid_proof p1 \<langle>Nil, f\<rangle> B" by (rule proof_bool[OF p1_nat J1_nat])
  have b2: "is_valid_proof p2 \<langle>Nil, mk_not f\<rangle> B" by (rule proof_bool[OF p2_nat J2_nat])
  have cB: "(is_valid_proof p1 \<langle>Nil, f\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_not f\<rangle>) B"
    using b1 b2 by auto
  show "(\<not> (is_valid_proof p1 \<langle>Nil, f\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_not f\<rangle>)) B"
    by (rule notB[OF cB])
next
  assume nn: "\<not> \<not> (is_valid_proof p1 \<langle>Nil, f\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_not f\<rangle>)"
  have conj: "is_valid_proof p1 \<langle>Nil, f\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_not f\<rangle>"
    by (rule dNegE[OF nn])
  have pr1: "is_valid_proof p1 \<langle>Nil, f\<rangle>"    by (rule conjE1[OF conj])
  have pr2: "is_valid_proof p2 \<langle>Nil, mk_not f\<rangle>" by (rule conjE2[OF conj])
  have nf_nat: "mk_not f N" by (rule mk_not_N[OF f_nat])

  have s1: "wsat (conc_of \<langle>Nil, f\<rangle>) zero"
    apply (rule soundness)
      apply (rule pr1)
     using f_nat apply simp
     apply (rule sat_hyp_nil)
    apply (rule nat0)
    done
  have s1': "wsat f zero" using s1 f_nat by simp

  have s2: "wsat (conc_of \<langle>Nil, mk_not f\<rangle>) zero"
    apply (rule soundness)
      apply (rule pr2)
     using nf_nat apply simp
     apply (rule sat_hyp_nil)
    apply (rule nat0)
    done
  have s2': "wsat (mk_not f) zero" using s2 nf_nat by simp

  have u: "wunsat f zero" by (rule neg_clause[OF f_nat s2'])
  show "False" by (rule excl[OF f_nat nat0 s1' u])
qed

text \<open>The pairwise form of \<open>BGA_on_GA.thy\<close> is the special case at an equation.\<close>

corollary no_proof_of_false:
  assumes f_nat: "f N" and p_nat: "p N"
      and refut: "is_valid_proof pn \<langle>Nil, mk_not f\<rangle>" and pn_nat: "pn N"
  shows "\<not> is_valid_proof p \<langle>Nil, f\<rangle>"
proof (rule contradiction[where p = "\<not> is_valid_proof p \<langle>Nil, f\<rangle>"])
  have J1_nat: "\<langle>Nil, f\<rangle> N" using f_nat by simp
  show "(\<not> is_valid_proof p \<langle>Nil, f\<rangle>) B" by (rule notB, rule proof_bool[OF p_nat J1_nat])
next
  assume nn: "\<not> \<not> is_valid_proof p \<langle>Nil, f\<rangle>"
  have pr: "is_valid_proof p \<langle>Nil, f\<rangle>" by (rule dNegE[OF nn])
  have both: "is_valid_proof p \<langle>Nil, f\<rangle> \<and> is_valid_proof pn \<langle>Nil, mk_not f\<rangle>"
    by (rule conjI[OF pr refut])
  show "False"
    by (rule exF[OF both syntactically_consistent[OF f_nat p_nat pn_nat]])
qed

end



section \<open>The encoded vocabulary\<close>

text \<open>
  The coded system is the object logic of \<open>GD.thy\<close>: one tag per primitive,
  defined connectives as abbreviations.

  Terms: 0 variable, 1 zero, 2 suc, 3 pred, 4 conditional (guard is a
  formula), 5 application of a definition to two arguments.
  Formulas: 0 equality, 1 negation, 2 disjunction, 3 forall, 4 exists,
  5 conditional.

  Terms and formulas are mutually recursive because \<open>cond\<close> has a formula as
  guard.  Rules over a context \<open>Q\<close> are checked by a matcher that walks premise
  and conclusion in parallel, so no template search is needed.

  \<open>eq_reflection\<close> and \<open>iff_reflection\<close> are about Pure and are not coded;
  \<open>eqSubst\<close> covers the first, nothing covers the second.
\<close>

  abbreviation T_VAR  :: num where "T_VAR  \<equiv> 0"
  abbreviation T_ZERO :: num where "T_ZERO \<equiv> 1"
  abbreviation T_SUC  :: num where "T_SUC  \<equiv> 2"
  abbreviation T_PRED :: num where "T_PRED \<equiv> 3"
  abbreviation T_COND :: num where "T_COND \<equiv> 4"
  abbreviation T_APP  :: num where "T_APP  \<equiv> 5"

  abbreviation F_EQ   :: num where "F_EQ   \<equiv> 0"
  abbreviation F_NOT  :: num where "F_NOT  \<equiv> 1"
  abbreviation F_OR   :: num where "F_OR   \<equiv> 2"
  abbreviation F_ALL  :: num where "F_ALL  \<equiv> 3"
  abbreviation F_EX   :: num where "F_EX   \<equiv> 4"
  abbreviation F_COND :: num where "F_COND \<equiv> 5"

text \<open>A disequality transported along an equation.\<close>

lemma eq_ne_trans:
  assumes x: "x N" and n: "n N" and h: "x = m" and mn: "\<not> (m = n)"
  shows "\<not> (x = n)"
proof (rule contradiction[where p = "\<not> (x = n)"])
  show "(\<not> (x = n)) B" by (rule notB, rule eqBool[OF x n])
next
  assume nn: "\<not> \<not> (x = n)"
  have e: "x = n" by (rule dNegE[OF nn])
  have mn2: "m = n" by (rule eq_trans[OF eqSym[OF h] e])
  show "False" by (rule exF[OF mn2 mn])
qed


section \<open>The encoder interface\<close>

text \<open>
  As \<open>bga_encoding\<close>: a retraction pair with structural decrease, so recursion
  over syntax becomes numerical recursion.
\<close>

locale qga_encoding =
  fixes tag_T  :: "tm \<Rightarrow> num"
  fixes load_T :: "tm \<Rightarrow> num"
  fixes pack_T :: "num \<Rightarrow> num \<Rightarrow> tm"
  fixes tag_F  :: "fm \<Rightarrow> num"
  fixes load_F :: "fm \<Rightarrow> num"
  fixes pack_F :: "num \<Rightarrow> num \<Rightarrow> fm"

  assumes pack_T_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> pack_T t L N"
  assumes tag_T_N:  "t N \<Longrightarrow> tag_T t N"
  assumes load_T_N: "t N \<Longrightarrow> load_T t N"
  assumes pack_F_N: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> pack_F t L N"
  assumes tag_F_N:  "f N \<Longrightarrow> tag_F f N"
  assumes load_F_N: "f N \<Longrightarrow> load_F f N"

  assumes tag_pack_T:  "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> tag_T (pack_T t L) = t"
  assumes load_pack_T: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> load_T (pack_T t L) = L"
  assumes pack_tag_T:  "t N \<Longrightarrow> pack_T (tag_T t) (load_T t) = t"
  assumes tag_pack_F:  "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> tag_F (pack_F t L) = t"
  assumes load_pack_F: "\<lbrakk>t N; L N\<rbrakk> \<Longrightarrow> load_F (pack_F t L) = L"
  assumes pack_tag_F:  "f N \<Longrightarrow> pack_F (tag_F f) (load_F f) = f"

  assumes decrease_T: "\<lbrakk>t N; t \<noteq> 0\<rbrakk> \<Longrightarrow> load_T t < t = 1"
  assumes decrease_F: "\<lbrakk>f N; f \<noteq> 0\<rbrakk> \<Longrightarrow> load_F f < f = 1"
  assumes tag_T_zero: "tag_T 0 = T_ZERO"
  assumes tag_F_zero: "tag_F 0 = F_EQ"

  assumes mono_pack_T: "\<lbrakk>tg N; x N; y N; x \<le> y = 1\<rbrakk> \<Longrightarrow> pack_T tg x \<le> pack_T tg y = 1"
  assumes mono_pack_F: "\<lbrakk>tg N; x N; y N; x \<le> y = 1\<rbrakk> \<Longrightarrow> pack_F tg x \<le> pack_F tg y = 1"
begin

abbreviation tVar  :: "num \<Rightarrow> tm"            where "tVar i  \<equiv> pack_T T_VAR i"
abbreviation tZero :: "tm"                    where "tZero    \<equiv> pack_T T_ZERO 0"
abbreviation tSuc  :: "tm \<Rightarrow> tm"              where "tSuc a  \<equiv> pack_T T_SUC a"
abbreviation tPred :: "tm \<Rightarrow> tm"              where "tPred a \<equiv> pack_T T_PRED a"
abbreviation tCond :: "fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"  where "tCond c a b \<equiv> pack_T T_COND \<langle>c, \<langle>a, b\<rangle>\<rangle>"
abbreviation tApp  :: "num \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm" where "tApp d a b \<equiv> pack_T T_APP \<langle>d, \<langle>a, b\<rangle>\<rangle>"

abbreviation mkEq  :: "tm \<Rightarrow> tm \<Rightarrow> fm"        where "mkEq a b  \<equiv> pack_F F_EQ \<langle>a, b\<rangle>"
abbreviation mkNot :: "fm \<Rightarrow> fm"              where "mkNot p   \<equiv> pack_F F_NOT p"
abbreviation mkOr  :: "fm \<Rightarrow> fm \<Rightarrow> fm"        where "mkOr p q  \<equiv> pack_F F_OR \<langle>p, q\<rangle>"
abbreviation mkAll :: "num \<Rightarrow> fm \<Rightarrow> fm"       where "mkAll i p \<equiv> pack_F F_ALL \<langle>i, p\<rangle>"
abbreviation mkEx  :: "num \<Rightarrow> fm \<Rightarrow> fm"       where "mkEx i p  \<equiv> pack_F F_EX \<langle>i, p\<rangle>"
abbreviation mkFCond :: "fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm" where "mkFCond c p q \<equiv> pack_F F_COND \<langle>c, \<langle>p, q\<rangle>\<rangle>"

text \<open>The abbreviations of \<open>GD.thy\<close>, coded as \<open>GD.thy\<close> defines them.\<close>

abbreviation mkNeq   :: "tm \<Rightarrow> tm \<Rightarrow> fm" where "mkNeq a b \<equiv> mkNot (mkEq a b)"
abbreviation mkNat   :: "tm \<Rightarrow> fm"       where "mkNat a   \<equiv> mkEq a a"
abbreviation mkBool  :: "fm \<Rightarrow> fm"       where "mkBool p  \<equiv> mkOr p (mkNot p)"
abbreviation mkAnd   :: "fm \<Rightarrow> fm \<Rightarrow> fm" where "mkAnd p q \<equiv> mkNot (mkOr (mkNot p) (mkNot q))"
abbreviation mkImp   :: "fm \<Rightarrow> fm \<Rightarrow> fm" where "mkImp p q \<equiv> mkOr (mkNot p) q"
abbreviation mkIff   :: "fm \<Rightarrow> fm \<Rightarrow> fm" where "mkIff p q \<equiv> mkAnd (mkImp p q) (mkImp q p)"
abbreviation mkTrue  :: "fm"             where "mkTrue     \<equiv> mkEq tZero tZero"
abbreviation mkFalse :: "fm"             where "mkFalse    \<equiv> mkEq (tSuc tZero) tZero"

end


section \<open>Freshness, substitution, closure\<close>

text \<open>
  \<open>fresh_T k t\<close>: every variable index in \<open>t\<close> is below \<open>k\<close> (so \<open>fresh_T 0 t\<close>
  means \<open>t\<close> is closed).  This gives the eigenvariable conditions.
  \<open>subst_T\<close>/\<open>subst_F\<close>/\<open>subst_H\<close> substitute a term for a variable; \<open>subst_body\<close>
  unfolds a definition.  \<open>close_F f Pv A\<close> replaces the free variables of \<open>f\<close>
  not in \<open>Pv\<close> by the numerals \<open>A\<close> assigns, or by \<open>tBot\<close> where \<open>A\<close> gives
  bottom.
\<close>

locale qga_subst = qga_encoding +
  fixes fresh_T :: "num \<Rightarrow> tm \<Rightarrow> o"
  fixes fresh_F :: "num \<Rightarrow> fm \<Rightarrow> o"
  fixes fresh_H :: "num \<Rightarrow> hyp \<Rightarrow> o"

  fixes subst_T  :: "tm \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> tm"
  fixes subst_F  :: "fm \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> fm"
  fixes subst_H  :: "hyp \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> hyp"
  fixes subst_body :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"

  fixes asn_put    :: "asn \<Rightarrow> num \<Rightarrow> val \<Rightarrow> asn"
  fixes numeral_of :: "val \<Rightarrow> tm"
  fixes tBot       :: "tm"
  fixes close_T :: "tm \<Rightarrow> hyp \<Rightarrow> asn \<Rightarrow> tm"
  fixes close_F :: "fm \<Rightarrow> hyp \<Rightarrow> asn \<Rightarrow> fm"
  fixes close_H :: "hyp \<Rightarrow> hyp \<Rightarrow> asn \<Rightarrow> hyp"

  assumes fresh_T_def: "fresh_T k t :=
      if tag_T t = T_VAR  then load_T t < k = 1
      else if tag_T t = T_ZERO then True
      else if tag_T t = T_SUC  then fresh_T k (load_T t)
      else if tag_T t = T_PRED then fresh_T k (load_T t)
      else if tag_T t = T_COND then
             fresh_F k (pfst (load_T t)) \<and> fresh_T k (psnd (load_T t)) \<and> fresh_T k (pthd (load_T t))
      else if tag_T t = T_APP then
             fresh_T k (psnd (load_T t)) \<and> fresh_T k (pthd (load_T t))
      else False"

  assumes fresh_F_def: "fresh_F k f :=
      if tag_F f = F_EQ  then fresh_T k (cpx (load_F f)) \<and> fresh_T k (cpy (load_F f))
      else if tag_F f = F_NOT then fresh_F k (load_F f)
      else if tag_F f = F_OR  then fresh_F k (cpx (load_F f)) \<and> fresh_F k (cpy (load_F f))
      else if tag_F f = F_ALL then (cpx (load_F f) < k = 1) \<and> fresh_F k (cpy (load_F f))
      else if tag_F f = F_EX  then (cpx (load_F f) < k = 1) \<and> fresh_F k (cpy (load_F f))
      else if tag_F f = F_COND then
             fresh_F k (pfst (load_F f)) \<and> fresh_F k (psnd (load_F f)) \<and> fresh_F k (pthd (load_F f))
      else False"

  assumes fresh_H_def: "fresh_H k G :=
      if G = Nil then True else fresh_F k (list_hd G) \<and> fresh_H k (list_tl G)"

  assumes subst_T_def: "subst_T t j v :=
      if tag_T t = T_VAR  then (if load_T t = j then v else t)
      else if tag_T t = T_ZERO then t
      else if tag_T t = T_SUC  then tSuc  (subst_T (load_T t) j v)
      else if tag_T t = T_PRED then tPred (subst_T (load_T t) j v)
      else if tag_T t = T_COND then
             tCond (subst_F (pfst (load_T t)) j v)
                   (subst_T (psnd (load_T t)) j v)
                   (subst_T (pthd (load_T t)) j v)
      else if tag_T t = T_APP then
             tApp (pfst (load_T t))
                  (subst_T (psnd (load_T t)) j v)
                  (subst_T (pthd (load_T t)) j v)
      else t"

  assumes subst_F_def: "subst_F f j v :=
      if tag_F f = F_EQ  then mkEq (subst_T (cpx (load_F f)) j v) (subst_T (cpy (load_F f)) j v)
      else if tag_F f = F_NOT then mkNot (subst_F (load_F f) j v)
      else if tag_F f = F_OR  then mkOr (subst_F (cpx (load_F f)) j v) (subst_F (cpy (load_F f)) j v)
      else if tag_F f = F_ALL then
             (if cpx (load_F f) = j then f
              else mkAll (cpx (load_F f)) (subst_F (cpy (load_F f)) j v))
      else if tag_F f = F_EX then
             (if cpx (load_F f) = j then f
              else mkEx (cpx (load_F f)) (subst_F (cpy (load_F f)) j v))
      else if tag_F f = F_COND then
             mkFCond (subst_F (pfst (load_F f)) j v)
                     (subst_F (psnd (load_F f)) j v)
                     (subst_F (pthd (load_F f)) j v)
      else f"

  assumes subst_H_def: "subst_H G j v :=
      if G = Nil then Nil else subst_F (list_hd G) j v \<triangleright> subst_H (list_tl G) j v"

  (* Two-argument definition bodies use v_0 and v_1, as in BGA. *)
  assumes subst_body_def: "subst_body b x y := subst_T (subst_T b 0 x) 1 y"

  assumes asn_put_def: "asn_put A i v :=
      if i = 0 then (if A = Nil then v \<triangleright> Nil else v \<triangleright> list_tl A)
      else if A = Nil then 0 \<triangleright> asn_put Nil (i - 1) v
      else list_hd A \<triangleright> asn_put (list_tl A) (i - 1) v"

  assumes numeral_of_def: "numeral_of v := if v = 0 then tZero else tSuc (numeral_of (v - 1))"

  assumes close_T_def: "close_T t Pv A :=
      if tag_T t = T_VAR then
        (if load_T t \<in> Pv then t
         else if nth (load_T t) A = 0 then tBot
         else numeral_of (P (nth (load_T t) A)))
      else if tag_T t = T_ZERO then t
      else if tag_T t = T_SUC  then tSuc  (close_T (load_T t) Pv A)
      else if tag_T t = T_PRED then tPred (close_T (load_T t) Pv A)
      else if tag_T t = T_COND then
             tCond (close_F (pfst (load_T t)) Pv A)
                   (close_T (psnd (load_T t)) Pv A)
                   (close_T (pthd (load_T t)) Pv A)
      else if tag_T t = T_APP then
             tApp (pfst (load_T t))
                  (close_T (psnd (load_T t)) Pv A)
                  (close_T (pthd (load_T t)) Pv A)
      else t"

  assumes close_F_def: "close_F f Pv A :=
      if tag_F f = F_EQ  then mkEq (close_T (cpx (load_F f)) Pv A) (close_T (cpy (load_F f)) Pv A)
      else if tag_F f = F_NOT then mkNot (close_F (load_F f) Pv A)
      else if tag_F f = F_OR  then mkOr (close_F (cpx (load_F f)) Pv A) (close_F (cpy (load_F f)) Pv A)
      else if tag_F f = F_ALL then
             mkAll (cpx (load_F f)) (close_F (cpy (load_F f)) (cpx (load_F f) \<triangleright> Pv) A)
      else if tag_F f = F_EX then
             mkEx (cpx (load_F f)) (close_F (cpy (load_F f)) (cpx (load_F f) \<triangleright> Pv) A)
      else if tag_F f = F_COND then
             mkFCond (close_F (pfst (load_F f)) Pv A)
                     (close_F (psnd (load_F f)) Pv A)
                     (close_F (pthd (load_F f)) Pv A)
      else f"

  assumes close_H_def: "close_H G Pv A :=
      if G = Nil then Nil else close_F (list_hd G) Pv A \<triangleright> close_H (list_tl G) Pv A"
begin

text \<open>
  Groundedness of the syntax functions, as in \<open>BGA_on_GA.thy\<close>, by one
  strong induction covering terms and formulas.
\<close>

lemma fresh_TF_bool:
  assumes k: "k N" and x: "x N"
  shows "(fresh_T k x B) \<and> (fresh_F k x B)"
  \<comment> \<open>strong induction on \<open>x\<close>; recursive calls are on smaller codes\<close>
  sorry

lemma fresh_T_bool [auto]: "\<lbrakk>k N; t N\<rbrakk> \<Longrightarrow> fresh_T k t B"
  by (rule conjE1[OF fresh_TF_bool])

lemma fresh_F_bool [auto]: "\<lbrakk>k N; f N\<rbrakk> \<Longrightarrow> fresh_F k f B"
  by (rule conjE2[OF fresh_TF_bool])

lemma fresh_H_bool [auto]:
  assumes k: "k N" and G: "G N"
  shows "fresh_H k G B"
  \<comment> \<open>list induction on \<open>G\<close>\<close>
  sorry

lemma subst_T_N [auto]: "\<lbrakk>t N; j N; v N\<rbrakk> \<Longrightarrow> subst_T t j v N"
  \<comment> \<open>strong induction, jointly with \<open>subst_F_N\<close>\<close>
  sorry
lemma subst_F_N [auto]: "\<lbrakk>f N; j N; v N\<rbrakk> \<Longrightarrow> subst_F f j v N" sorry
lemma subst_H_N [auto]: "\<lbrakk>G N; j N; v N\<rbrakk> \<Longrightarrow> subst_H G j v N" sorry

lemma close_T_N [auto]: "\<lbrakk>t N; Pv N; A N\<rbrakk> \<Longrightarrow> close_T t Pv A N" sorry
lemma close_F_N [auto]: "\<lbrakk>f N; Pv N; A N\<rbrakk> \<Longrightarrow> close_F f Pv A N" sorry
lemma close_H_N [auto]: "\<lbrakk>G N; Pv N; A N\<rbrakk> \<Longrightarrow> close_H G Pv A N" sorry
lemma numeral_of_N [auto]: "v N \<Longrightarrow> numeral_of v N" sorry
lemma asn_put_N [auto]: "\<lbrakk>A N; i N; v N\<rbrakk> \<Longrightarrow> asn_put A i v N" sorry

text \<open>Closure produces closed syntax.\<close>

lemma close_F_closed: "\<lbrakk>f N; A N\<rbrakk> \<Longrightarrow> fresh_F 0 (close_F f Nil A)" sorry
lemma close_H_closed: "\<lbrakk>G N; A N\<rbrakk> \<Longrightarrow> fresh_H 0 (close_H G Nil A)" sorry

end


section \<open>The definition list\<close>

locale qga_dfns = qga_subst +
  fixes dfns   :: "dfn"
  fixes dfn_is :: "dfn \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> o"
  assumes dfns_N: "dfns N"
  assumes dfn_is_def:
    "dfn_is d k b := if d < len dfns = 1 then nth d dfns = b \<and> fresh_T k b else False"
  \<comment> \<open>\<open>tBot = d_0(0, 0)\<close>, closed and divergent (\<open>omega := omega\<close>)\<close>
  assumes tBot_N: "tBot N"
  assumes tBot_closed: "fresh_T 0 tBot"
begin

lemma dfn_is_bool [auto]: "\<lbrakk>d N; k N; b N\<rbrakk> \<Longrightarrow> dfn_is d k b B"
  \<comment> \<open>as \<open>bga_dfns.dfn_is_bool\<close>\<close>
  sorry

end


section \<open>The proof checker\<close>

text \<open>
  A proof is a list of judgments, most recent first, each following from
  later ones by one rule (as in BGA).

  GD.thy has no structural rules because Pure supplies them; here they are
  checker branches: \<open>hyp\<close>, \<open>weak\<close>, \<open>cut\<close>, \<open>inst\<close>.  Premises of the form
  \<open>P \<Longrightarrow> R\<close> are looked up as judgments with \<open>P\<close> added to the hypotheses;
  premises \<open>\<And>x. x N \<Longrightarrow> Q x\<close> as judgments about a fresh variable.

  Every other branch is one GD.thy axiom.  Not coded: \<open>eq_reflection\<close>,
  \<open>iff_reflection\<close>, and \<open>notForallI\<close>, which a reflective reading of the
  universal cannot validate before soundness is proved.
\<close>

subsection \<open>Destructors for the encoded abbreviations\<close>

context qga_encoding
begin

text \<open>Destructors for the abbreviations \<open>B\<close>, \<open>\<and>\<close>, \<open>\<longleftrightarrow>\<close>, each with its shape
      test.\<close>

abbreviation boolArg :: "fm \<Rightarrow> fm" where "boolArg f \<equiv> cpx (load_F f)"
abbreviation andL :: "fm \<Rightarrow> fm" where "andL f \<equiv> load_F (cpx (load_F (load_F f)))"
abbreviation andR :: "fm \<Rightarrow> fm" where "andR f \<equiv> load_F (cpy (load_F (load_F f)))"
abbreviation iffL :: "fm \<Rightarrow> fm" where
  "iffL f \<equiv> load_F (cpx (load_F (andL f)))"
abbreviation iffR :: "fm \<Rightarrow> fm" where
  "iffR f \<equiv> cpy (load_F (andL f))"

end


subsection \<open>Matchers\<close>

text \<open>
  Matchers for the rules over a context:
  \<^item> \<open>eqT\<close>/\<open>eqF\<close>: \<open>eqSubst\<close>;
  \<^item> \<open>lzT\<close>/\<open>lzF\<close>: the lazy conditional rules;
  \<^item> \<open>unfT\<close>/\<open>unfF\<close>: \<open>defE\<close>/\<open>defI\<close>.  Unlike GD.thy, unfolding requires the
    arguments to terminate (as \<open>app_try\<close> in \<open>BGA_on_GA.thy\<close>), because the
    semantics evaluates arguments first.
\<close>

locale qga_match = qga_dfns +
  fixes eqT :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> o"
  fixes eqF :: "fm \<Rightarrow> fm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> o"
  fixes lzT :: "tm \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> num \<Rightarrow> o"
  fixes lzF :: "fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> num \<Rightarrow> o"
  fixes unfT :: "tm \<Rightarrow> tm \<Rightarrow> hyp \<Rightarrow> pf \<Rightarrow> o"
  fixes unfF :: "fm \<Rightarrow> fm \<Rightarrow> hyp \<Rightarrow> pf \<Rightarrow> o"

  assumes eqT_def: "eqT t u a b :=
    if t = u then True
    else if t = a \<and> u = b then True
    else if tag_T t = T_SUC \<and> tag_T u = T_SUC then eqT (load_T t) (load_T u) a b
    else if tag_T t = T_PRED \<and> tag_T u = T_PRED then eqT (load_T t) (load_T u) a b
    else if tag_T t = T_COND \<and> tag_T u = T_COND then
         eqF (pfst (load_T t)) (pfst (load_T u)) a b
         \<and> eqT (psnd (load_T t)) (psnd (load_T u)) a b
         \<and> eqT (pthd (load_T t)) (pthd (load_T u)) a b
    else if tag_T t = T_APP \<and> tag_T u = T_APP \<and> pfst (load_T t) = pfst (load_T u) then
         eqT (psnd (load_T t)) (psnd (load_T u)) a b
         \<and> eqT (pthd (load_T t)) (pthd (load_T u)) a b
    else False"

  assumes eqF_def: "eqF f g a b :=
    if f = g then True
    else if tag_F f = F_EQ \<and> tag_F g = F_EQ then
         eqT (cpx (load_F f)) (cpx (load_F g)) a b \<and> eqT (cpy (load_F f)) (cpy (load_F g)) a b
    else if tag_F f = F_NOT \<and> tag_F g = F_NOT then eqF (load_F f) (load_F g) a b
    else if tag_F f = F_OR \<and> tag_F g = F_OR then
         eqF (cpx (load_F f)) (cpx (load_F g)) a b \<and> eqF (cpy (load_F f)) (cpy (load_F g)) a b
    else if tag_F f = F_ALL \<and> tag_F g = F_ALL \<and> cpx (load_F f) = cpx (load_F g) then
         eqF (cpy (load_F f)) (cpy (load_F g)) a b
    else if tag_F f = F_EX \<and> tag_F g = F_EX \<and> cpx (load_F f) = cpx (load_F g) then
         eqF (cpy (load_F f)) (cpy (load_F g)) a b
    else if tag_F f = F_COND \<and> tag_F g = F_COND then
         eqF (pfst (load_F f)) (pfst (load_F g)) a b
         \<and> eqF (psnd (load_F f)) (psnd (load_F g)) a b
         \<and> eqF (pthd (load_F f)) (pthd (load_F g)) a b
    else False"

  assumes lzT_def: "lzT t u c sel :=
    if t = u then True
    else if tag_T t = T_COND \<and> pfst (load_T t) = c
            \<and> (if sel = 0 then psnd (load_T t) else pthd (load_T t)) = u then True
    else if tag_T t = T_SUC \<and> tag_T u = T_SUC then lzT (load_T t) (load_T u) c sel
    else if tag_T t = T_PRED \<and> tag_T u = T_PRED then lzT (load_T t) (load_T u) c sel
    else if tag_T t = T_COND \<and> tag_T u = T_COND then
         lzF (pfst (load_T t)) (pfst (load_T u)) c sel
         \<and> lzT (psnd (load_T t)) (psnd (load_T u)) c sel
         \<and> lzT (pthd (load_T t)) (pthd (load_T u)) c sel
    else if tag_T t = T_APP \<and> tag_T u = T_APP \<and> pfst (load_T t) = pfst (load_T u) then
         lzT (psnd (load_T t)) (psnd (load_T u)) c sel
         \<and> lzT (pthd (load_T t)) (pthd (load_T u)) c sel
    else False"

  assumes lzF_def: "lzF f g c sel :=
    if f = g then True
    else if tag_F f = F_COND \<and> pfst (load_F f) = c
            \<and> (if sel = 0 then psnd (load_F f) else pthd (load_F f)) = g then True
    else if tag_F f = F_EQ \<and> tag_F g = F_EQ then
         lzT (cpx (load_F f)) (cpx (load_F g)) c sel \<and> lzT (cpy (load_F f)) (cpy (load_F g)) c sel
    else if tag_F f = F_NOT \<and> tag_F g = F_NOT then lzF (load_F f) (load_F g) c sel
    else if tag_F f = F_OR \<and> tag_F g = F_OR then
         lzF (cpx (load_F f)) (cpx (load_F g)) c sel \<and> lzF (cpy (load_F f)) (cpy (load_F g)) c sel
    else if tag_F f = F_ALL \<and> tag_F g = F_ALL \<and> cpx (load_F f) = cpx (load_F g) then
         lzF (cpy (load_F f)) (cpy (load_F g)) c sel
    else if tag_F f = F_EX \<and> tag_F g = F_EX \<and> cpx (load_F f) = cpx (load_F g) then
         lzF (cpy (load_F f)) (cpy (load_F g)) c sel
    else if tag_F f = F_COND \<and> tag_F g = F_COND then
         lzF (pfst (load_F f)) (pfst (load_F g)) c sel
         \<and> lzF (psnd (load_F f)) (psnd (load_F g)) c sel
         \<and> lzF (pthd (load_F f)) (pthd (load_F g)) c sel
    else False"

  assumes unfT_def: "unfT t u G rest :=
    if t = u then True
    else if tag_T t = T_APP \<and> pfst (load_T t) < len dfns = 1
            \<and> mem (G \<tturnstile> mkNat (psnd (load_T t))) rest
            \<and> mem (G \<tturnstile> mkNat (pthd (load_T t))) rest
            \<and> subst_body (nth (pfst (load_T t)) dfns) (psnd (load_T t)) (pthd (load_T t)) = u
    then True
    else if tag_T t = T_SUC \<and> tag_T u = T_SUC then unfT (load_T t) (load_T u) G rest
    else if tag_T t = T_PRED \<and> tag_T u = T_PRED then unfT (load_T t) (load_T u) G rest
    else if tag_T t = T_COND \<and> tag_T u = T_COND then
         unfF (pfst (load_T t)) (pfst (load_T u)) G rest
         \<and> unfT (psnd (load_T t)) (psnd (load_T u)) G rest
         \<and> unfT (pthd (load_T t)) (pthd (load_T u)) G rest
    else if tag_T t = T_APP \<and> tag_T u = T_APP \<and> pfst (load_T t) = pfst (load_T u) then
         unfT (psnd (load_T t)) (psnd (load_T u)) G rest
         \<and> unfT (pthd (load_T t)) (pthd (load_T u)) G rest
    else False"

  assumes unfF_def: "unfF f g G rest :=
    if f = g then True
    else if tag_F f = F_EQ \<and> tag_F g = F_EQ then
         unfT (cpx (load_F f)) (cpx (load_F g)) G rest \<and> unfT (cpy (load_F f)) (cpy (load_F g)) G rest
    else if tag_F f = F_NOT \<and> tag_F g = F_NOT then unfF (load_F f) (load_F g) G rest
    else if tag_F f = F_OR \<and> tag_F g = F_OR then
         unfF (cpx (load_F f)) (cpx (load_F g)) G rest \<and> unfF (cpy (load_F f)) (cpy (load_F g)) G rest
    else if tag_F f = F_ALL \<and> tag_F g = F_ALL \<and> cpx (load_F f) = cpx (load_F g) then
         unfF (cpy (load_F f)) (cpy (load_F g)) G rest
    else if tag_F f = F_EX \<and> tag_F g = F_EX \<and> cpx (load_F f) = cpx (load_F g) then
         unfF (cpy (load_F f)) (cpy (load_F g)) G rest
    else if tag_F f = F_COND \<and> tag_F g = F_COND then
         unfF (pfst (load_F f)) (pfst (load_F g)) G rest
         \<and> unfF (psnd (load_F f)) (psnd (load_F g)) G rest
         \<and> unfF (pthd (load_F f)) (pthd (load_F g)) G rest
    else False"


subsection \<open>Structural rules (from Pure)\<close>

locale qga_struct_rule = qga_match +
  fixes find_cut    :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_cut   :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  fixes find_weak   :: "jdg \<Rightarrow> hyp \<Rightarrow> pf \<Rightarrow> o"
  fixes check_weak  :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  fixes inst_try    :: "jdg \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o"
  fixes inst_a      :: "jdg \<Rightarrow> num \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o"
  fixes inst_i      :: "jdg \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  fixes check_inst  :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  (* cut *)
  assumes find_cut_def: "find_cut J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> mem (conc_of (list_hd ptr) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest then True
    else find_cut J rest (list_tl ptr)"
  assumes check_cut_def: "check_cut J rest := find_cut J rest rest"

  (* weak *)
  assumes find_weak_def: "find_weak J G ptr :=
    if ptr = Nil then False
    else if conc_of (list_hd ptr) = conc_of J \<and> subset (hyp_of (list_hd ptr)) G then True
    else find_weak J G (list_tl ptr)"
  assumes check_weak_def: "check_weak J rest := find_weak J (hyp_of J) rest"

  (* inst: free variables range over values and bottom, so instantiation
   needs no habeas quid premise. *)
  assumes inst_try_def: "inst_try J i a ptr :=
    if ptr = Nil then False
    else if subst_H (hyp_of (list_hd ptr)) i a = hyp_of J
            \<and> subst_F (conc_of (list_hd ptr)) i a = conc_of J
            \<and> fresh_H i (hyp_of (list_hd ptr)) then True
    else inst_try J i a (list_tl ptr)"
  assumes inst_a_def: "inst_a J i a rest :=
    if inst_try J i a rest then True
    else if a > 0 = 1 then inst_a J i (a - 1) rest else False"
  assumes inst_i_def: "inst_i J i rest :=
    if inst_a J i J rest then True
    else if i > 0 = 1 then inst_i J (i - 1) rest else False"
  assumes check_inst_def: "check_inst J rest := inst_i J J rest"


subsection \<open>Propositional rules\<close>

text \<open>The \<open>disj\<close>/\<open>not\<close> axioms.\<close>

locale qga_prop_rule = qga_match +
  fixes find_disjE1 :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes find_disjE23 :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  fixes find_exF    :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_prop_rules :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  (* disjE1: from Gamma |- P v Q, Gamma,P |- R and Gamma,Q |- R infer Gamma |- R *)
  assumes find_disjE1_def: "find_disjE1 J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_OR
            \<and> mem (cpx (load_F (conc_of (list_hd ptr))) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
            \<and> mem (cpy (load_F (conc_of (list_hd ptr))) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
    then True else find_disjE1 J rest (list_tl ptr)"

  (* disjE2 and disjE3: from Gamma |- ~(P v Q) infer Gamma |- ~P, resp. ~Q *)
  assumes find_disjE23_def: "find_disjE23 J ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_NOT
            \<and> tag_F (load_F (conc_of (list_hd ptr))) = F_OR
            \<and> (mkNot (cpx (load_F (load_F (conc_of (list_hd ptr))))) = conc_of J
               \<or> mkNot (cpy (load_F (load_F (conc_of (list_hd ptr))))) = conc_of J)
    then True else find_disjE23 J (list_tl ptr)"

  (* exF: from Gamma |- P and Gamma |- ~P infer Gamma |- anything *)
  assumes find_exF_def: "find_exF J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> mem (hyp_of J \<tturnstile> mkNot (conc_of (list_hd ptr))) rest
    then True else find_exF J rest (list_tl ptr)"

  assumes check_prop_rules_def: "check_prop_rules J rest :=
    if tag_F (conc_of J) = F_OR
       \<and> (mem (hyp_of J \<tturnstile> cpx (load_F (conc_of J))) rest
          \<or> mem (hyp_of J \<tturnstile> cpy (load_F (conc_of J))) rest)
    then True                                                    \<comment> \<open>disjI1, disjI2\<close>
    else if tag_F (conc_of J) = F_NOT \<and> tag_F (load_F (conc_of J)) = F_OR
            \<and> mem (hyp_of J \<tturnstile> mkNot (cpx (load_F (load_F (conc_of J))))) rest
            \<and> mem (hyp_of J \<tturnstile> mkNot (cpy (load_F (load_F (conc_of J))))) rest
    then True                                                    \<comment> \<open>disjI3\<close>
    else if tag_F (conc_of J) = F_NOT \<and> tag_F (load_F (conc_of J)) = F_NOT
            \<and> mem (hyp_of J \<tturnstile> load_F (load_F (conc_of J))) rest
    then True                                                    \<comment> \<open>dNegI\<close>
    else if mem (hyp_of J \<tturnstile> mkNot (mkNot (conc_of J))) rest
    then True                                                    \<comment> \<open>dNegE\<close>
    else if find_disjE1 J rest rest then True
    else if find_disjE23 J rest then True
    else if find_exF J rest rest then True
    else False"


subsection \<open>Equality\<close>

text \<open>\<open>eqSubst\<close> and \<open>eqSym\<close>.\<close>

locale qga_eq_rule = qga_match +
  fixes eqsub_inner :: "jdg \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> pf \<Rightarrow> o"
  fixes eqsub_outer :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_eqsub :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  fixes check_eqsym :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  assumes eqsub_inner_def: "eqsub_inner J a b ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> eqF (conc_of (list_hd ptr)) (conc_of J) a b then True
    else eqsub_inner J a b (list_tl ptr)"

  assumes eqsub_outer_def: "eqsub_outer J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
            \<and> eqsub_inner J (cpx (load_F (conc_of (list_hd ptr))))
                            (cpy (load_F (conc_of (list_hd ptr)))) rest
    then True else eqsub_outer J rest (list_tl ptr)"

  assumes check_eqsub_def: "check_eqsub J rest := eqsub_outer J rest rest"

  assumes check_eqsym_def: "check_eqsym J rest :=
    if tag_F (conc_of J) = F_EQ
       \<and> mem (hyp_of J \<tturnstile> mkEq (cpy (load_F (conc_of J))) (cpx (load_F (conc_of J)))) rest
    then True else False"


subsection \<open>Natural numbers\<close>

text \<open>The ten arithmetic axioms other than \<open>ind\<close>; each premise is a lookup.\<close>

locale qga_nat_rule = qga_match +
  fixes check_nat_rules :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  assumes check_nat_rules_def: "check_nat_rules J rest :=
    if conc_of J = mkNat tZero then True                                  \<comment> \<open>nat0\<close>
    else if conc_of J = mkEq (tPred tZero) tZero then True                \<comment> \<open>pred0\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> mem (hyp_of J \<tturnstile> mkEq (tSuc (cpx (load_F (conc_of J))))
                                     (tSuc (cpy (load_F (conc_of J))))) rest
    then True                                                             \<comment> \<open>sucInj\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> tag_T (cpx (load_F (conc_of J))) = T_SUC
            \<and> tag_T (cpy (load_F (conc_of J))) = T_SUC
            \<and> mem (hyp_of J \<tturnstile> mkEq (load_T (cpx (load_F (conc_of J))))
                                     (load_T (cpy (load_F (conc_of J))))) rest
    then True                                                             \<comment> \<open>sucCong\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> tag_T (cpx (load_F (conc_of J))) = T_PRED
            \<and> tag_T (cpy (load_F (conc_of J))) = T_PRED
            \<and> mem (hyp_of J \<tturnstile> mkEq (load_T (cpx (load_F (conc_of J))))
                                     (load_T (cpy (load_F (conc_of J))))) rest
    then True                                                             \<comment> \<open>predCong\<close>
    else if conc_of J = mkBool (boolArg (conc_of J))
            \<and> tag_F (boolArg (conc_of J)) = F_EQ
            \<and> mem (hyp_of J \<tturnstile> mkNat (cpx (load_F (boolArg (conc_of J))))) rest
            \<and> mem (hyp_of J \<tturnstile> mkNat (cpy (load_F (boolArg (conc_of J))))) rest
    then True                                                             \<comment> \<open>eqBool\<close>
    else if tag_F (conc_of J) = F_NOT \<and> tag_F (load_F (conc_of J)) = F_EQ
            \<and> tag_T (cpx (load_F (load_F (conc_of J)))) = T_SUC
            \<and> cpy (load_F (load_F (conc_of J))) = tZero
            \<and> mem (hyp_of J \<tturnstile> mkNat (load_T (cpx (load_F (load_F (conc_of J)))))) rest
    then True                                                             \<comment> \<open>sucNonZero\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> cpx (load_F (conc_of J)) = tPred (tSuc (cpy (load_F (conc_of J))))
            \<and> mem (hyp_of J \<tturnstile> mkNat (cpy (load_F (conc_of J)))) rest
    then True                                                             \<comment> \<open>predSucInv\<close>
    else if conc_of J = mkAnd (andL (conc_of J)) (andR (conc_of J))
            \<and> tag_F (andL (conc_of J)) = F_EQ \<and> tag_F (andR (conc_of J)) = F_EQ
            \<and> cpx (load_F (andL (conc_of J))) = cpy (load_F (andL (conc_of J)))
            \<and> cpx (load_F (andR (conc_of J))) = cpy (load_F (andR (conc_of J)))
            \<and> mem (hyp_of J \<tturnstile> mkBool (mkEq (cpx (load_F (andL (conc_of J))))
                                             (cpx (load_F (andR (conc_of J)))))) rest
    then True                                                             \<comment> \<open>eqE\<close>
    else if tag_F (conc_of J) = F_EQ
            \<and> cpx (load_F (conc_of J)) = cpy (load_F (conc_of J))
            \<and> mem (hyp_of J \<tturnstile> mkNat (tPred (cpx (load_F (conc_of J))))) rest
    then True                                                             \<comment> \<open>predTIE\<close>
    else False"


subsection \<open>Induction\<close>

text \<open>
  \<open>ind\<close>: the step premise is the judgment \<open>v_i N, Q[v_i], \<Gamma> \<turnstile> Q[S v_i]\<close> with
  \<open>i\<close> fresh; scanning for it gives \<open>i\<close> and the motive directly.
\<close>

locale qga_ind_rule = qga_match +
  fixes ind_inner :: "jdg \<Rightarrow> num \<Rightarrow> fm \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes ind_outer :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_ind :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  assumes ind_inner_def: "ind_inner J i p rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
            \<and> cpx (load_F (conc_of (list_hd ptr))) = cpy (load_F (conc_of (list_hd ptr)))
            \<and> fresh_T i (cpx (load_F (conc_of (list_hd ptr))))
            \<and> subst_F p i (cpx (load_F (conc_of (list_hd ptr)))) = conc_of J
            \<and> mem (hyp_of J \<tturnstile> subst_F p i tZero) rest
    then True else ind_inner J i p rest (list_tl ptr)"

  assumes ind_outer_def: "ind_outer J rest ptr :=
    if ptr = Nil then False
    else if list_hd (hyp_of (list_hd ptr))
              = mkNat (tVar (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr)))))))
            \<and> list_tl (list_tl (hyp_of (list_hd ptr))) = hyp_of J
            \<and> conc_of (list_hd ptr)
                = subst_F (list_hd (list_tl (hyp_of (list_hd ptr))))
                          (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr))))))
                          (tSuc (tVar (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr))))))))
            \<and> fresh_H (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr)))))) (hyp_of J)
            \<and> ind_inner J (load_T (cpx (load_F (list_hd (hyp_of (list_hd ptr))))))
                          (list_hd (list_tl (hyp_of (list_hd ptr)))) rest rest
    then True else ind_outer J rest (list_tl ptr)"

  assumes check_ind_def: "check_ind J rest := ind_outer J rest rest"


subsection \<open>Quantifiers\<close>

text \<open>
  The quantifier axioms.  The premise of \<open>forallI\<close> is looked up as
  \<open>v_i N, \<Gamma> \<turnstile> p\<close> with \<open>i\<close> fresh, which is the shape of the witness the
  semantics below uses.
\<close>

locale qga_quant_rule = qga_match +
  fixes find_allE_inner  :: "jdg \<Rightarrow> num \<Rightarrow> fm \<Rightarrow> pf \<Rightarrow> o"
  fixes find_allE        :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes find_exI         :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes find_exE         :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes find_nallE       :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_quant_rules :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  (* forallE *)
  assumes find_allE_inner_def: "find_allE_inner J i p ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
            \<and> cpx (load_F (conc_of (list_hd ptr))) = cpy (load_F (conc_of (list_hd ptr)))
            \<and> subst_F p i (cpx (load_F (conc_of (list_hd ptr)))) = conc_of J
    then True else find_allE_inner J i p (list_tl ptr)"

  assumes find_allE_def: "find_allE J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_ALL
            \<and> find_allE_inner J (cpx (load_F (conc_of (list_hd ptr))))
                                (cpy (load_F (conc_of (list_hd ptr)))) rest
    then True else find_allE J rest (list_tl ptr)"

  (* existsI *)
  assumes find_exI_def: "find_exI J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
            \<and> cpx (load_F (conc_of (list_hd ptr))) = cpy (load_F (conc_of (list_hd ptr)))
            \<and> mem (hyp_of J \<tturnstile> subst_F (cpy (load_F (conc_of J)))
                                       (cpx (load_F (conc_of J)))
                                       (cpx (load_F (conc_of (list_hd ptr))))) rest
    then True else find_exI J rest (list_tl ptr)"

  (* existsE: the eigenvariable is J + 1 *)
  assumes find_exE_def: "find_exE J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EX
            \<and> fresh_H (J + 1) (hyp_of J) \<and> fresh_F (J + 1) (conc_of J)
            \<and> mem (subst_F (cpy (load_F (conc_of (list_hd ptr))))
                           (cpx (load_F (conc_of (list_hd ptr)))) (tVar (J + 1))
                   \<triangleright> mkNat (tVar (J + 1)) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
    then True else find_exE J rest (list_tl ptr)"

  (* notForallE *)
  assumes find_nallE_def: "find_nallE J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_NOT
            \<and> tag_F (load_F (conc_of (list_hd ptr))) = F_ALL
            \<and> fresh_H (J + 1) (hyp_of J) \<and> fresh_F (J + 1) (conc_of J)
            \<and> mem (mkNot (subst_F (cpy (load_F (load_F (conc_of (list_hd ptr)))))
                                  (cpx (load_F (load_F (conc_of (list_hd ptr)))))
                                  (tVar (J + 1)))
                   \<triangleright> mkNat (tVar (J + 1)) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
    then True else find_nallE J rest (list_tl ptr)"

  assumes check_quant_rules_def: "check_quant_rules J rest :=
    if tag_F (conc_of J) = F_ALL
       \<and> fresh_H (cpx (load_F (conc_of J))) (hyp_of J)
       \<and> mem (mkNat (tVar (cpx (load_F (conc_of J)))) \<triangleright> hyp_of J
              \<tturnstile> cpy (load_F (conc_of J))) rest
    then True                                                        \<comment> \<open>forallI\<close>
    else if tag_F (conc_of J) = F_EX \<and> find_exI J rest rest then True \<comment> \<open>existsI\<close>
    else if find_allE J rest rest then True                           \<comment> \<open>forallE\<close>
    else if find_exE J rest rest then True                            \<comment> \<open>existsE\<close>
    else if find_nallE J rest rest then True                          \<comment> \<open>notForallE\<close>
    else False"


subsection \<open>Conditionals\<close>

text \<open>
  The conditional axioms: ten by one scan (\<open>find_cond\<close>), the four lazy rules
  by the \<open>lzT\<close>/\<open>lzF\<close> matcher (\<open>find_lazy\<close>).
\<close>

locale qga_cond_rule = qga_match +
  fixes find_condE :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_condI :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  fixes lazy_inner :: "jdg \<Rightarrow> fm \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  fixes lazy_outer :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_cond_rules :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  (* condI1, condI2, condI1B, condI2B *)
  assumes check_condI_def: "check_condI J rest :=
    if tag_F (conc_of J) = F_EQ \<and> tag_T (cpx (load_F (conc_of J))) = T_COND
       \<and> psnd (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J))
       \<and> mem (hyp_of J \<tturnstile> pfst (load_T (cpx (load_F (conc_of J))))) rest
       \<and> mem (hyp_of J \<tturnstile> mkNat (cpy (load_F (conc_of J)))) rest
    then True                                                          \<comment> \<open>condI1\<close>
    else if tag_F (conc_of J) = F_EQ \<and> tag_T (cpx (load_F (conc_of J))) = T_COND
       \<and> pthd (load_T (cpx (load_F (conc_of J)))) = cpy (load_F (conc_of J))
       \<and> mem (hyp_of J \<tturnstile> mkNot (pfst (load_T (cpx (load_F (conc_of J)))))) rest
       \<and> mem (hyp_of J \<tturnstile> mkNat (cpy (load_F (conc_of J)))) rest
    then True                                                          \<comment> \<open>condI2\<close>
    else if conc_of J = mkIff (iffL (conc_of J)) (iffR (conc_of J))
       \<and> tag_F (iffL (conc_of J)) = F_COND
       \<and> psnd (load_F (iffL (conc_of J))) = iffR (conc_of J)
       \<and> mem (hyp_of J \<tturnstile> pfst (load_F (iffL (conc_of J)))) rest
       \<and> mem (hyp_of J \<tturnstile> mkBool (iffR (conc_of J))) rest
    then True                                                          \<comment> \<open>condI1B\<close>
    else if conc_of J = mkIff (iffL (conc_of J)) (iffR (conc_of J))
       \<and> tag_F (iffL (conc_of J)) = F_COND
       \<and> pthd (load_F (iffL (conc_of J))) = iffR (conc_of J)
       \<and> mem (hyp_of J \<tturnstile> mkNot (pfst (load_F (iffL (conc_of J))))) rest
       \<and> mem (hyp_of J \<tturnstile> mkBool (iffR (conc_of J))) rest
    then True                                                          \<comment> \<open>condI2B\<close>
    else False"

  (* condE1, condE2, condE3, condE1B, condE2B, condE3B *)
  assumes find_condE_def: "find_condE J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
       \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
       \<and> cpx (load_F (conc_of (list_hd ptr))) = cpy (load_F (conc_of (list_hd ptr)))
       \<and> tag_T (cpx (load_F (conc_of (list_hd ptr)))) = T_COND
       \<and> ((conc_of J = mkNat (psnd (load_T (cpx (load_F (conc_of (list_hd ptr))))))
           \<and> mem (hyp_of J \<tturnstile> pfst (load_T (cpx (load_F (conc_of (list_hd ptr)))))) rest)
          \<or> (conc_of J = mkNat (pthd (load_T (cpx (load_F (conc_of (list_hd ptr))))))
             \<and> mem (hyp_of J \<tturnstile> mkNot (pfst (load_T (cpx (load_F (conc_of (list_hd ptr))))))) rest)
          \<or> conc_of J = mkBool (pfst (load_T (cpx (load_F (conc_of (list_hd ptr)))))))
    then True                                              \<comment> \<open>condE1, condE2, condE3\<close>
    else if hyp_of (list_hd ptr) = hyp_of J
       \<and> conc_of (list_hd ptr) = mkBool (boolArg (conc_of (list_hd ptr)))
       \<and> tag_F (boolArg (conc_of (list_hd ptr))) = F_COND
       \<and> ((conc_of J = mkBool (psnd (load_F (boolArg (conc_of (list_hd ptr)))))
           \<and> mem (hyp_of J \<tturnstile> pfst (load_F (boolArg (conc_of (list_hd ptr))))) rest)
          \<or> (conc_of J = mkBool (pthd (load_F (boolArg (conc_of (list_hd ptr)))))
             \<and> mem (hyp_of J \<tturnstile> mkNot (pfst (load_F (boolArg (conc_of (list_hd ptr)))))) rest)
          \<or> conc_of J = mkBool (pfst (load_F (boolArg (conc_of (list_hd ptr))))))
    then True                                           \<comment> \<open>condE1B, condE2B, condE3B\<close>
    else find_condE J rest (list_tl ptr)"

  (* lazy rules: sel picks the branch, dir the direction *)
  assumes lazy_inner_def: "lazy_inner J c sel dir ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> (if dir = 0 then lzF (conc_of (list_hd ptr)) (conc_of J) c sel
               else lzF (conc_of J) (conc_of (list_hd ptr)) c sel)
    then True else lazy_inner J c sel dir (list_tl ptr)"

  assumes lazy_outer_def: "lazy_outer J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> (lazy_inner J (conc_of (list_hd ptr)) 0 0 rest
               \<or> lazy_inner J (conc_of (list_hd ptr)) 0 1 rest)
    then True                                        \<comment> \<open>cond_thenQ_E, cond_thenQ_I\<close>
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_NOT
            \<and> (lazy_inner J (load_F (conc_of (list_hd ptr))) 1 0 rest
               \<or> lazy_inner J (load_F (conc_of (list_hd ptr))) 1 1 rest)
    then True                                        \<comment> \<open>cond_elseQ_E, cond_elseQ_I\<close>
    else lazy_outer J rest (list_tl ptr)"

  assumes check_cond_rules_def: "check_cond_rules J rest :=
    if check_condI J rest then True
    else if find_condE J rest rest then True
    else if lazy_outer J rest rest then True
    else False"


subsection \<open>Definitions\<close>

text \<open>\<open>defE\<close> and \<open>defI\<close>, at the entries of the definition list.\<close>

locale qga_def_rule = qga_match +
  fixes find_def  :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_def :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  assumes find_def_def: "find_def J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> (unfF (conc_of J) (conc_of (list_hd ptr)) (hyp_of J) rest
               \<or> unfF (conc_of (list_hd ptr)) (conc_of J) (hyp_of J) rest)
    then True else find_def J rest (list_tl ptr)"

  assumes check_def_def: "check_def J rest := find_def J rest rest"


subsection \<open>The step relation and the checker\<close>

locale qga_proof_check =
  qga_struct_rule + qga_prop_rule + qga_eq_rule + qga_nat_rule
  + qga_ind_rule + qga_quant_rule + qga_cond_rule + qga_def_rule +
  fixes valid_step :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  fixes check_list :: "pf \<Rightarrow> o"
  fixes is_valid_proof :: "pf \<Rightarrow> jdg \<Rightarrow> o"

  assumes valid_step_def: "valid_step J rest :=
    if mem (conc_of J) (hyp_of J) then True         \<comment> \<open>hyp, from Pure assume\<close>
    else if check_weak J rest then True             \<comment> \<open>weak, from the hypothesis set\<close>
    else if check_cut J rest then True              \<comment> \<open>cut, from Pure implies intr/elim\<close>
    else if check_inst J rest then True             \<comment> \<open>inst, from Thm.instantiate\<close>
    else if check_prop_rules J rest then True       \<comment> \<open>the nine disj/not axioms\<close>
    else if check_eqsym J rest then True            \<comment> \<open>eqSym\<close>
    else if check_eqsub J rest then True            \<comment> \<open>eqSubst\<close>
    else if check_nat_rules J rest then True        \<comment> \<open>the ten arithmetic axioms\<close>
    else if check_ind J rest then True              \<comment> \<open>ind\<close>
    else if check_quant_rules J rest then True      \<comment> \<open>the six quantifier axioms\<close>
    else if check_cond_rules J rest then True       \<comment> \<open>the fourteen conditional axioms\<close>
    else if check_def J rest then True              \<comment> \<open>defE, defI\<close>
    else False"

  assumes check_list_def: "check_list pf :=
    if pf = Nil then True
    else if valid_step (list_hd pf) (list_tl pf) then check_list (list_tl pf)
    else False"

  assumes is_valid_proof_def: "is_valid_proof pf J :=
    if pf = Nil then False
    else if list_hd pf = J then check_list pf
    else False"
begin

text \<open>Groundedness of proof checking, as \<open>proof_is_bool\<close> in \<open>BGA_on_GA.thy\<close>.\<close>

lemma valid_step_bool [auto]: "\<lbrakk>J N; rest N\<rbrakk> \<Longrightarrow> valid_step J rest B" sorry
lemma check_list_bool [auto]: "pf N \<Longrightarrow> check_list pf B" sorry

lemma proof_is_bool [auto]:
  assumes p: "p N" and J: "J N"
  shows "(is_valid_proof p J) B"
proof (rule defE[OF is_valid_proof_def[where pf=p and J=J], where Q = "\<lambda>z. z B"])
  have g1: "(p = Nil) B" by (rule eqBool[OF p nil_nat])
  have g2: "(list_hd p = J) B" by (rule eqBool[OF list_hd_nat[OF p] J])
  show "(if p = Nil then False else if list_hd p = J then check_list p else False) B"
    by (rule condTB[OF g1 false_bool],
        rule condTB[OF g2 check_list_bool[OF p] false_bool])
qed

text \<open>
  The tail of a checked list proves each of its members.  The forall
  introduction case of soundness uses this as its certificate.
\<close>

lemma check_list_tl:
  "\<lbrakk>pf N; \<not> (pf = Nil); check_list pf\<rbrakk> \<Longrightarrow> check_list (list_tl pf)"
  \<comment> \<open>case split on the step guard, then \<open>condI1B\<close>/\<open>condI2B\<close>\<close>
  sorry

lemma is_valid_proofI:
  "\<lbrakk>pf N; \<not> (pf = Nil); check_list pf\<rbrakk> \<Longrightarrow> is_valid_proof pf (list_hd pf)"
  sorry

lemma suffix_is_proof:
  assumes p: "pf N" and ok: "check_list pf" and K: "K N" and m: "mem K pf"
  shows "\<exists>q. is_valid_proof q K"
proof -
  have main: "mem K pf \<longrightarrow> (check_list pf \<longrightarrow> (\<exists>q. is_valid_proof q K))"
  proof (rule list_induct[OF p,
      where Q = "\<lambda>z. mem K z \<longrightarrow> (check_list z \<longrightarrow> (\<exists>q. is_valid_proof q K))"])
    show "mem K Nil \<longrightarrow> (check_list Nil \<longrightarrow> (\<exists>q. is_valid_proof q K))"
    proof (rule implI)
      show "(mem K Nil) B" by (rule mem_bool[OF K nil_nat])
    next
      assume mm: "mem K Nil"
      show "check_list Nil \<longrightarrow> (\<exists>q. is_valid_proof q K)"
        by (rule exF[OF mm mem_nil])
    qed
  next
    fix x xs
    assume x: "x N" and xs: "xs N"
    assume IH: "mem K xs \<longrightarrow> (check_list xs \<longrightarrow> (\<exists>q. is_valid_proof q K))"
    have cxs: "Cons x xs N" using x xs by simp
    show "mem K (Cons x xs) \<longrightarrow> (check_list (Cons x xs) \<longrightarrow> (\<exists>q. is_valid_proof q K))"
    proof (rule implI)
      show "(mem K (Cons x xs)) B" by (rule mem_bool[OF K cxs])
    next
      assume mm: "mem K (Cons x xs)"
      show "check_list (Cons x xs) \<longrightarrow> (\<exists>q. is_valid_proof q K)"
      proof (rule implI)
        show "(check_list (Cons x xs)) B" by (rule check_list_bool[OF cxs])
      next
        assume ok2: "check_list (Cons x xs)"
        have iff1: "mem K (Cons x xs) \<longrightarrow> (if x = K then True else mem K xs)"
          by (rule conjE1[OF mem_cons[OF x xs K, unfolded iff_def]])
        have step: "if x = K then True else mem K xs" by (rule implE[OF iff1 mm])
        have ne: "\<not> (Cons x xs = Nil)" using x xs by auto
        show "\<exists>q. is_valid_proof q K"
        proof (rule cases_bool[where q = "x = K"])
          show "(x = K) B" by (rule eqBool[OF x K])
        next
          assume xk: "x = K"
          have vp: "is_valid_proof (Cons x xs) (list_hd (Cons x xs))"
            by (rule is_valid_proofI[OF cxs ne ok2])
          have hd: "list_hd (Cons x xs) = x" by (rule list_hd_cons[OF x xs])
          have hk: "list_hd (Cons x xs) = K" by (rule eq_trans[OF hd xk])
          have vp2: "is_valid_proof (Cons x xs) K"
            by (rule eqSubst[where Q="\<lambda>z. is_valid_proof (Cons x xs) z", OF hk vp])
          show ?thesis
            by (rule existsI[where Q="\<lambda>q. is_valid_proof q K", OF cxs vp2])
        next
          assume nxk: "\<not> (x = K)"
          have eB: "(mem K xs) B" by (rule mem_bool[OF K xs])
          have ifq: "(if x = K then True else mem K xs) \<longleftrightarrow> mem K xs"
            by (rule condI2B[OF nxk eB])
          have mk: "mem K xs"
            by (rule implE[OF conjE1[OF ifq[unfolded iff_def]] step])
          have tl: "list_tl (Cons x xs) = xs" by (rule list_tl_cons[OF x xs])
          have okt: "check_list (list_tl (Cons x xs))" by (rule check_list_tl[OF cxs ne ok2])
          have okxs: "check_list xs"
            by (rule eqSubst[where Q="\<lambda>z. check_list z", OF tl okt])
          show ?thesis by (rule implE[OF implE[OF IH mk] okxs])
        qed
      qed
    qed
  qed
  show ?thesis by (rule implE[OF implE[OF main m] ok])
qed

end


section \<open>The official fuelled semantics\<close>

text \<open>
  \<^bold>\<open>Why one three-valued evaluator.\<close>  Exclusivity (nothing is both true and
  false) is needed for \<open>exF\<close>.  It cannot be proved by induction on two
  separate predicates, since QGA induction needs a decided motive.  It does
  follow from stability (a verdict, once produced, does not change with more
  fuel), whose motive is decided.  So evaluation is one function: \<open>evF\<close>
  returns 2 (true), 1 (false) or 0 (no verdict); \<open>evT\<close> returns \<open>S v\<close> or 0.
  An assignment maps an index to \<open>S v\<close> or to 0 (bottom).

  \<^bold>\<open>Quantifiers.\<close>  At each fuel the evaluator must decide between a truth
  witness and a falsity witness.  Letting the least witness win keeps
  stability, but then \<open>notForallI\<close> would need soundness itself, so it is not
  coded: a universal is true when a certificate is found and has no verdict
  otherwise.  Witnesses carry their own fuel (\<open>cpx w \<le> w\<close>), so validity of a
  witness does not depend on the search budget.
\<close>

locale qga_fuel_semantics = qga_proof_check +
  fixes evT    :: "num \<Rightarrow> tm \<Rightarrow> asn \<Rightarrow> val"
  fixes evF    :: "num \<Rightarrow> fm \<Rightarrow> asn \<Rightarrow> num"
  fixes hypsat :: "num \<Rightarrow> hyp \<Rightarrow> asn \<Rightarrow> num"
  fixes all_tt :: "num \<Rightarrow> num \<Rightarrow> fm \<Rightarrow> asn \<Rightarrow> num"
  fixes ex_tt  :: "num \<Rightarrow> num \<Rightarrow> fm \<Rightarrow> asn \<Rightarrow> num"

  assumes evT_def: "evT k t A :=
    if k = 0 then 0
    else if tag_T t = T_VAR  then nth (load_T t) A
    else if tag_T t = T_ZERO then S 0
    else if tag_T t = T_SUC then
      (if evT (P k) (load_T t) A = 0 then 0 else S (evT (P k) (load_T t) A))
    else if tag_T t = T_PRED then
      (if evT (P k) (load_T t) A = 0 then 0 else S (P (P (evT (P k) (load_T t) A))))
    else if tag_T t = T_COND then
      (if evF (P k) (pfst (load_T t)) A = 2 then evT (P k) (psnd (load_T t)) A
       else if evF (P k) (pfst (load_T t)) A = 1 then evT (P k) (pthd (load_T t)) A
       else 0)
    else if tag_T t = T_APP then
      (if evT (P k) (psnd (load_T t)) A = 0 then 0
       else if evT (P k) (pthd (load_T t)) A = 0 then 0
       else evT (P k) (nth (pfst (load_T t)) dfns)
              (evT (P k) (psnd (load_T t)) A \<triangleright> evT (P k) (pthd (load_T t)) A \<triangleright> Nil))
    else 0"

  assumes evF_def: "evF k f A :=
    if k = 0 then 0
    else if tag_F f = F_EQ then
      (if evT (P k) (cpx (load_F f)) A = 0 then 0
       else if evT (P k) (cpy (load_F f)) A = 0 then 0
       else if evT (P k) (cpx (load_F f)) A = evT (P k) (cpy (load_F f)) A then 2 else 1)
    else if tag_F f = F_NOT then
      (if evF (P k) (load_F f) A = 2 then 1
       else if evF (P k) (load_F f) A = 1 then 2 else 0)
    else if tag_F f = F_OR then
      (if evF (P k) (cpx (load_F f)) A = 2 then 2
       else if evF (P k) (cpy (load_F f)) A = 2 then 2
       else if evF (P k) (cpx (load_F f)) A = 1 then
              (if evF (P k) (cpy (load_F f)) A = 1 then 1 else 0)
       else 0)
    else if tag_F f = F_ALL then all_tt (P k) (cpx (load_F f)) (cpy (load_F f)) A
    else if tag_F f = F_EX  then ex_tt  (P k) (cpx (load_F f)) (cpy (load_F f)) A
    else if tag_F f = F_COND then
      (if evF (P k) (pfst (load_F f)) A = 2 then evF (P k) (psnd (load_F f)) A
       else if evF (P k) (pfst (load_F f)) A = 1 then evF (P k) (pthd (load_F f)) A
       else 0)
    else 0"

  assumes hypsat_def: "hypsat j G A :=
    if G = Nil then 1
    else if evF j (list_hd G) A = 2 then hypsat j (list_tl G) A
    else 0"

  (* A witness w = <j, <q, G>> is valid if q proves G, v_i N |- phi[A] with G
   closed and satisfied by A within j steps. *)
  assumes all_tt_def: "all_tt w i phi A :=
    if is_valid_proof (cpx (cpy w))
         (mkNat (tVar i) \<triangleright> cpy (cpy w) \<tturnstile> close_F phi (i \<triangleright> Nil) A)
       \<and> fresh_H 0 (cpy (cpy w))
       \<and> hypsat (cpx w) (cpy (cpy w)) A = 1
    then 2
    else if w > 0 = 1 then all_tt (w - 1) i phi A
    else 0"

  (* An existential is true at a numeral instance. *)
  assumes ex_tt_def: "ex_tt w i phi A :=
    if evF (cpx w) phi (asn_put A i (S (cpy w))) = 2 then 2
    else if w > 0 = 1 then ex_tt (w - 1) i phi A
    else 0"
begin

subsection \<open>Totality\<close>

text \<open>
  Totality, by strong induction on the fuel with a \<open>\<forall>\<close>-motive over term,
  formula and assignment.
\<close>

lemma evT_N [auto]: "\<lbrakk>k N; t N; A N\<rbrakk> \<Longrightarrow> evT k t A N" sorry
lemma evF_N [auto]: "\<lbrakk>k N; f N; A N\<rbrakk> \<Longrightarrow> evF k f A N" sorry
lemma hypsat_N [auto]: "\<lbrakk>j N; G N; A N\<rbrakk> \<Longrightarrow> hypsat j G A N" sorry

subsection \<open>Satisfaction, decided and undecided\<close>

definition evals :: "tm \<Rightarrow> asn \<Rightarrow> val \<Rightarrow> o" where
  "evals t A v \<equiv> \<exists>k. evT k t A = S v"

definition sat_at :: "num \<Rightarrow> fm \<Rightarrow> asn \<Rightarrow> o" where
  "sat_at k f A \<equiv> evF k f A = 2"

definition unsat_at :: "num \<Rightarrow> fm \<Rightarrow> asn \<Rightarrow> o" where
  "unsat_at k f A \<equiv> evF k f A = 1"

definition sat :: "fm \<Rightarrow> asn \<Rightarrow> o" where
  "sat f A \<equiv> \<exists>k. evF k f A = 2"

definition unsat :: "fm \<Rightarrow> asn \<Rightarrow> o" where
  "unsat f A \<equiv> \<exists>k. evF k f A = 1"

definition sat_hyp_at :: "num \<Rightarrow> hyp \<Rightarrow> asn \<Rightarrow> o" where
  "sat_hyp_at k G A \<equiv> hypsat k G A = 1"

definition sat_hyp_fuel :: "hyp \<Rightarrow> asn \<Rightarrow> o" where
  "sat_hyp_fuel G A \<equiv> \<exists>k. hypsat k G A = 1"

text \<open>
  \<open>sat_at\<close> and \<open>sat_hyp_at\<close> are decided, so they can be antecedents of \<open>\<longrightarrow>\<close>
  in the soundness induction.
\<close>

lemma sat_at_bool [auto]: "\<lbrakk>k N; f N; A N\<rbrakk> \<Longrightarrow> (sat_at k f A) B"
  unfolding sat_at_def by (rule eqBool[OF evF_N], simp+)

lemma unsat_at_bool [auto]: "\<lbrakk>k N; f N; A N\<rbrakk> \<Longrightarrow> (unsat_at k f A) B"
  unfolding unsat_at_def by (rule eqBool[OF evF_N], simp+)

lemma sat_hyp_at_bool [auto]: "\<lbrakk>k N; G N; A N\<rbrakk> \<Longrightarrow> (sat_hyp_at k G A) B"
  unfolding sat_hyp_at_def by (rule eqBool[OF hypsat_N], simp+)

lemma sat_hyp_fuel_nil: "sat_hyp_fuel Nil A"
  unfolding sat_hyp_fuel_def
proof (rule existsI[where a = 0, OF nat0])
  have g: "Nil = Nil" by (rule nil_nat[unfolded isNat_def])
  have one: "(1::num) = 1" by simp
  show "hypsat 0 Nil A = 1"
    by (rule defE[OF hypsat_def[where j=0 and G=Nil and A=A], where Q="\<lambda>z. z = 1"],
        rule cond_thenQ_I[where Q="\<lambda>z. z = 1", OF g one])
qed

subsection \<open>Stability, and exclusivity as its corollary\<close>

text \<open>
  Stability: a verdict, once produced, is kept with more fuel.  Induction on
  the fuel; at the quantifiers it holds because witness validity does not
  depend on the budget.
\<close>

lemma evT_stable:
  "\<lbrakk>k N; t N; A N; \<not> (evT k t A = 0)\<rbrakk> \<Longrightarrow> evT (S k) t A = evT k t A" sorry

lemma evF_stable:
  "\<lbrakk>k N; f N; A N; \<not> (evF k f A = 0)\<rbrakk> \<Longrightarrow> evF (S k) f A = evF k f A" sorry

lemma evT_stable_add:
  "\<lbrakk>k N; l N; t N; A N; evT k t A = S v\<rbrakk> \<Longrightarrow> evT (k + l) t A = S v"
  \<comment> \<open>induction on \<open>l\<close> from \<open>evT_stable\<close>\<close>
  sorry

lemma evF_stable_add:
  "\<lbrakk>k N; l N; f N; A N; \<not> (evF k f A = 0)\<rbrakk> \<Longrightarrow> evF (k + l) f A = evF k f A"
  \<comment> \<open>induction on \<open>l\<close> from \<open>evF_stable\<close>\<close>
  sorry

text \<open>Exclusivity, from stability.\<close>

lemma evF_agree:
  assumes k: "k N" and l: "l N" and f: "f N" and A: "A N"
      and nk: "\<not> (evF k f A = 0)" and nl: "\<not> (evF l f A = 0)"
  shows "evF k f A = evF l f A"
proof -
  have left: "evF (k + l) f A = evF k f A" by (rule evF_stable_add[OF k l f A nk])
  have right: "evF (l + k) f A = evF l f A" by (rule evF_stable_add[OF l k f A nl])
  have comm: "l + k = k + l" by (rule add_comm[OF l k])
  have right': "evF (k + l) f A = evF l f A"
    by (rule eqSubst[where Q = "\<lambda>z. evF z f A = evF l f A", OF comm right])
  show ?thesis by (rule eq_trans[OF eqSym[OF left] right'])
qed

lemma two_neq_one: "\<not> ((2::num) = 1)"
  by auto

lemma official_excl:
  assumes f: "f N" and A: "A N" and s: "sat f A" and u: "unsat f A"
  shows "False"
proof -
  have s': "\<exists>k. evF k f A = 2" using s unfolding sat_def .
  show ?thesis
  proof (rule existsE[OF s'])
    fix k assume k: "k N" and hk: "evF k f A = 2"
    have u': "\<exists>l. evF l f A = 1" using u unfolding unsat_def .
    show ?thesis
    proof (rule existsE[OF u'])
      fix l assume l: "l N" and hl: "evF l f A = 1"
      have nk: "\<not> (evF k f A = 0)"
        by (rule eq_ne_trans[OF evF_N[OF k f A] nat0 hk], auto)
      have nl: "\<not> (evF l f A = 0)"
        by (rule eq_ne_trans[OF evF_N[OF l f A] nat0 hl], auto)
      have ag: "evF k f A = evF l f A" by (rule evF_agree[OF k l f A nk nl])
      have e21: "(2::num) = 1" by (rule eq_trans[OF eq_trans[OF eqSym[OF hk] ag] hl])
      show "False" by (rule exF[OF e21 two_neq_one])
    qed
  qed
qed

lemma evals_functional:
  assumes t: "t N" and A: "A N" and h1: "evals t A r" and h2: "evals t A q"
  shows "r = q"
proof -
  have e1: "\<exists>k. evT k t A = S r" using h1 unfolding evals_def .
  show ?thesis
  proof (rule existsE[OF e1])
    fix k assume k: "k N" and hk: "evT k t A = S r"
    have e2: "\<exists>l. evT l t A = S q" using h2 unfolding evals_def .
    show ?thesis
    proof (rule existsE[OF e2])
      fix l assume l: "l N" and hl: "evT l t A = S q"
      have left: "evT (k + l) t A = S r" by (rule evT_stable_add[OF k l t A hk])
      have right: "evT (l + k) t A = S q" by (rule evT_stable_add[OF l k t A hl])
      have comm: "l + k = k + l" by (rule add_comm[OF l k])
      have right': "evT (k + l) t A = S q"
        by (rule eqSubst[where Q = "\<lambda>z. evT z t A = S q", OF comm right])
      have sq: "S r = S q" by (rule eq_trans[OF eqSym[OF left] right'])
      show ?thesis by (rule sucInj[OF sq])
    qed
  qed
qed

subsection \<open>Freshness and closure at the official level\<close>

lemma evF_fresh:
  "\<lbrakk>k N; f N; A N; i N; v N; fresh_F i f\<rbrakk> \<Longrightarrow> evF k f (asn_put A i v) = evF k f A" sorry
lemma hypsat_fresh:
  "\<lbrakk>k N; G N; A N; i N; v N; fresh_H i G\<rbrakk> \<Longrightarrow> hypsat k G (asn_put A i v) = hypsat k G A" sorry
lemma hypsat_closed:
  "\<lbrakk>k N; G N; A N; A' N; fresh_H 0 G\<rbrakk> \<Longrightarrow> hypsat k G A = hypsat k G A'"
  \<comment> \<open>a closed context reads the same under every assignment\<close>
  sorry

end


section \<open>The witnessed semantics\<close>

text \<open>
  \<open>wsat f A := sat f A \<and> extras\<close>, \<open>wunsat f A := unsat f A \<and> extras\<close>.  The
  bridges to the official layer are \<open>conjE1\<close>, and exclusivity follows from
  them, with no induction over the witnessed predicates.
\<close>

locale qga_witnessed = qga_fuel_semantics +
  fixes wsat   :: "fm \<Rightarrow> asn \<Rightarrow> o"
  fixes wunsat :: "fm \<Rightarrow> asn \<Rightarrow> o"

  assumes wsat_def: "wsat f A :=
    (\<exists>k. evF k f A = 2)
    \<and> ((tag_F f = F_NOT \<longrightarrow> wunsat (load_F f) A)
    \<and> ((tag_F f = F_OR \<longrightarrow> (wsat (cpx (load_F f)) A \<or> wsat (cpy (load_F f)) A))
    \<and> ((tag_F f = F_ALL \<longrightarrow> (\<forall>n. wsat (cpy (load_F f)) (asn_put A (cpx (load_F f)) (S n))))
    \<and> ((tag_F f = F_EX \<longrightarrow> (\<exists>n. wsat (cpy (load_F f)) (asn_put A (cpx (load_F f)) (S n))))
    \<and> (tag_F f = F_COND \<longrightarrow>
         ((wsat (pfst (load_F f)) A \<and> wsat (psnd (load_F f)) A)
          \<or> (wunsat (pfst (load_F f)) A \<and> wsat (pthd (load_F f)) A)))))))"

  assumes wunsat_def: "wunsat f A :=
    (\<exists>k. evF k f A = 1)
    \<and> ((tag_F f = F_NOT \<longrightarrow> wsat (load_F f) A)
    \<and> ((tag_F f = F_OR \<longrightarrow> (wunsat (cpx (load_F f)) A \<and> wunsat (cpy (load_F f)) A))
    \<and> (tag_F f = F_COND \<longrightarrow>
         ((wsat (pfst (load_F f)) A \<and> wunsat (psnd (load_F f)) A)
          \<or> (wunsat (pfst (load_F f)) A \<and> wunsat (pthd (load_F f)) A)))))"

begin

subsection \<open>The bridges, and exclusivity\<close>

lemma wsat_sat: "wsat f A \<Longrightarrow> sat f A"
  unfolding sat_def
  by (rule conjE1, rule defI[OF wsat_def])

lemma wunsat_unsat: "wunsat f A \<Longrightarrow> unsat f A"
  unfolding unsat_def
  by (rule conjE1, rule defI[OF wunsat_def])

theorem wdet:
  assumes f: "f N" and A: "A N" and s: "wsat f A" and u: "wunsat f A"
  shows "False"
  by (rule official_excl[OF f A wsat_sat[OF s] wunsat_unsat[OF u]])

subsection \<open>Reading the clauses\<close>

text \<open>
  The structural conjunct uses tag-guarded implications, not a conditional:
  GD.thy's lazy conditional rules exist only at term type.
\<close>

lemma wsat_official: "wsat f A \<Longrightarrow> \<exists>k. evF k f A = 2"
  by (rule conjE1, rule defI[OF wsat_def])

lemma wunsat_official: "wunsat f A \<Longrightarrow> \<exists>k. evF k f A = 1"
  by (rule conjE1, rule defI[OF wunsat_def])

lemma wsat_NOT: "\<lbrakk>tag_F f = F_NOT; wsat f A\<rbrakk> \<Longrightarrow> wunsat (load_F f) A"
  by (rule implE, rule conjE1, rule conjE2, rule defI[OF wsat_def])

lemma wunsat_NOT: "\<lbrakk>tag_F f = F_NOT; wunsat f A\<rbrakk> \<Longrightarrow> wsat (load_F f) A"
  by (rule implE, rule conjE1, rule conjE2, rule defI[OF wunsat_def])

lemma wsat_OR: "\<lbrakk>tag_F f = F_OR; wsat f A\<rbrakk>
    \<Longrightarrow> wsat (cpx (load_F f)) A \<or> wsat (cpy (load_F f)) A"
  by (rule implE, rule conjE1, rule conjE2, rule conjE2, rule defI[OF wsat_def])

lemma wunsat_OR: "\<lbrakk>tag_F f = F_OR; wunsat f A\<rbrakk>
    \<Longrightarrow> wunsat (cpx (load_F f)) A \<and> wunsat (cpy (load_F f)) A"
  by (rule implE, rule conjE1, rule conjE2, rule conjE2, rule defI[OF wunsat_def])

lemma wsat_ALL: "\<lbrakk>tag_F f = F_ALL; wsat f A\<rbrakk>
    \<Longrightarrow> \<forall>n. wsat (cpy (load_F f)) (asn_put A (cpx (load_F f)) (S n))"
  by (rule implE, rule conjE1, rule conjE2, rule conjE2, rule conjE2,
      rule defI[OF wsat_def])

lemma wsat_EX: "\<lbrakk>tag_F f = F_EX; wsat f A\<rbrakk>
    \<Longrightarrow> \<exists>n. wsat (cpy (load_F f)) (asn_put A (cpx (load_F f)) (S n))"
  by (rule implE, rule conjE1, rule conjE2, rule conjE2, rule conjE2, rule conjE2,
      rule defI[OF wsat_def])

text \<open>The negation clause.\<close>

lemma wsat_not:
  assumes f: "f N" and h: "wsat (mkNot f) A"
  shows "wunsat f A"
proof -
  have fN: "(F_NOT::num) N" by auto
  have tg: "tag_F (mkNot f) = F_NOT" by (rule tag_pack_F[OF fN f])
  have step: "wunsat (load_F (mkNot f)) A" by (rule wsat_NOT[OF tg h])
  have ld: "load_F (mkNot f) = f" by (rule load_pack_F[OF fN f])
  show ?thesis by (rule eqSubst[where Q = "\<lambda>z. wunsat z A", OF ld step])
qed

subsection \<open>Substitution\<close>

text \<open>
  Substitution lemmas, both directions.  A certificate for the closure of
  \<open>p[i := a]\<close> converts into one for \<open>p\<close> at the value of \<open>a\<close> by one \<open>eqSubst\<close>.
\<close>

lemma evF_subst:
  "\<lbrakk>k N; p N; i N; a N; A N; v N; evals a A v\<rbrakk>
   \<Longrightarrow> \<not> (evF k (subst_F p i a) A = 0)
   \<Longrightarrow> (\<exists>l. evF l p (asn_put A i (S v)) = evF k (subst_F p i a) A)" sorry

lemma wsat_subst:
  "\<lbrakk>p N; i N; a N; A N; v N; evals a A v; wsat (subst_F p i a) A\<rbrakk>
   \<Longrightarrow> wsat p (asn_put A i (S v))" sorry

lemma wsat_subst_rev:
  "\<lbrakk>p N; i N; a N; A N; v N; evals a A v; wsat p (asn_put A i (S v))\<rbrakk>
   \<Longrightarrow> wsat (subst_F p i a) A" sorry

lemma wunsat_subst:
  "\<lbrakk>p N; i N; a N; A N; v N; evals a A v; wunsat (subst_F p i a) A\<rbrakk>
   \<Longrightarrow> wunsat p (asn_put A i (S v))" sorry

lemma wunsat_subst_rev:
  "\<lbrakk>p N; i N; a N; A N; v N; evals a A v; wunsat p (asn_put A i (S v))\<rbrakk>
   \<Longrightarrow> wunsat (subst_F p i a) A" sorry

subsection \<open>The two internal derivability lemmas\<close>

text \<open>
  The only places that construct a proof code, both for terms and equations.
\<close>

lemma term_value_complete:
  "\<lbrakk>t N; A N; v N; evals t A v\<rbrakk>
   \<Longrightarrow> \<exists>q. is_valid_proof q (Nil \<tturnstile> mkEq (close_T t Nil A) (numeral_of v))"
  \<comment> \<open>value completeness for terms, by induction on the fuel\<close>
  sorry

lemma closure_by_inst:
  "\<lbrakk>q N; G N; c N; A N; i N; is_valid_proof q (mkNat (tVar i) \<triangleright> G \<tturnstile> c)\<rbrakk>
   \<Longrightarrow> \<exists>q'. is_valid_proof q'
              (mkNat (tVar i) \<triangleright> close_H G (i \<triangleright> Nil) A \<tturnstile> close_F c (i \<triangleright> Nil) A)"
  \<comment> \<open>iterate \<open>inst\<close> once per free variable\<close>
  sorry

end


section \<open>Soundness\<close>

locale qga_full = qga_witnessed
begin

text \<open>
  Soundness of a checked step relative to the tail of the proof, lifted along
  the list by \<open>list_induct\<close>, with motive
    \<open>\<forall>A. \<forall>K. \<forall>k. check_list pf \<longrightarrow> (K \<in> pf \<longrightarrow> (sat_hyp_at k (hyp_of K) A \<longrightarrow> wsat (conc_of K) A))\<close>.
  The main cases: \<open>\<forall>\<close>I takes the tail of the list as certificate; \<open>\<forall>\<close>E reads
  the structural conjunct; \<open>exF\<close> uses \<open>wdet\<close>.  \<open>notForallE\<close> is vacuous.
\<close>

lemma valid_step_sound:
  "\<lbrakk>J N; rest N; A N; k N; valid_step J rest; sat_hyp_at k (hyp_of J) A;
    \<And>K k'. \<lbrakk>K N; k' N; K \<in> rest; sat_hyp_at k' (hyp_of K) A\<rbrakk> \<Longrightarrow> wsat (conc_of K) A\<rbrakk>
   \<Longrightarrow> wsat (conc_of J) A" sorry

lemma check_list_sound:
  "\<lbrakk>pf N; K N; A N; k N; check_list pf; K \<in> pf; sat_hyp_at k (hyp_of K) A\<rbrakk>
   \<Longrightarrow> wsat (conc_of K) A" sorry

lemma soundness_bridge:
  "\<lbrakk>p N; J N; A N; is_valid_proof p J; sat_hyp_fuel (hyp_of J) A\<rbrakk>
   \<Longrightarrow> wsat (conc_of J) A" sorry

text \<open>The interpretation of the abstract skeleton.\<close>

sublocale qga_consistent mkNot is_valid_proof wsat wunsat sat_hyp_fuel
proof
  fix f p J A
  show "f N \<Longrightarrow> mkNot f N" by (rule pack_F_N, simp+)
next
  fix p J
  show "\<lbrakk>p N; J N\<rbrakk> \<Longrightarrow> (is_valid_proof p J) B" by (rule proof_is_bool)
next
  fix A
  show "sat_hyp_fuel Nil A" by (rule sat_hyp_fuel_nil)
next
  fix f A
  show "\<lbrakk>f N; wsat (mkNot f) A\<rbrakk> \<Longrightarrow> wunsat f A" by (rule wsat_not)
next
  fix f A
  show "\<lbrakk>f N; A N; wsat f A; wunsat f A\<rbrakk> \<Longrightarrow> False" by (rule wdet)
next
  fix p J A
  show "\<lbrakk>is_valid_proof p J; sat_hyp_fuel (hyp_of J) A; A N\<rbrakk> \<Longrightarrow> wsat (conc_of J) A"
    \<comment> \<open>\<open>soundness_bridge\<close>, given the habeas quid side conditions supplied in
        \<open>qga_encode.thy\<close>\<close>
    sorry
qed

end

end
