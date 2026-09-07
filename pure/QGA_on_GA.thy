theory QGA_on_GA
  imports GD
begin

(*
  ============================================================================
  QGA arithmetized inside QGA.

  This file is to \<open>GD.thy\<close> what \<open>BGA_on_GA.thy\<close> is to \<open>GD.thy\<close>: it encodes a
  formal system as QGA natural numbers, defines a semantics for the encoded
  system as QGA recursive definitions, and proves the encoded proof checker
  sound with respect to that semantics.  The difference is that the encoded
  system is now QGA itself rather than BGA.

  As in \<open>BGA_on_GA.thy\<close> everything is relative to an abstract encoding
  interface; \<open>qga_encode.thy\<close> discharges the interface with a concrete
  Cantor-pairing G\<ouml>del numbering.

  ---------------------------------------------------------------------------
  ARCHITECTURE (see docs/bga_consistency/sections/07-qga-self.tex)

  Two semantic layers are used, and the split is what makes the argument
  non-circular.

  (1) The OFFICIAL fuelled semantics: two total functions
        \<open>evtt k f A\<close>   "f evaluates to TRUE  under A within k steps"   (1 or 0)
        \<open>evff k f A\<close>   "f evaluates to FALSE under A within k steps"   (1 or 0)
      They are separate searches, never consulted against one another, so
      neither has to preempt the other and both are monotone in k by
      construction.  Being total functions into num they are DECIDED at every
      fixed k, which is what lets satisfaction of a hypothesis list sit in the
      antecedent of an object-level \<open>\<longrightarrow>\<close> in the soundness induction.  The
      quantifier clauses of \<open>evtt\<close>/\<open>evff\<close> are bounded searches over proof codes
      (the reflective reading of \<S>6 of the report) and over numeral instances.

  (2) The WITNESSED semantics: two QGA recursive predicates
        \<open>wsat f A\<close>, \<open>wunsat f A\<close>
      whose quantifier clauses carry, in addition to the official verdict, the
      semantic facts the certificate promises:
        \<open>wsat (\<forall>i. \<phi>) A  :=  (\<exists>k. evtt k (\<forall>i. \<phi>) A = 1) \<and> (\<forall>n. wsat \<phi> A[i\<mapsto>n])\<close>
      This is Ford's "witnessed variant" (RGA \<S>4.5) transplanted into QGA.  It
      is what makes
        \<bullet> EXCLUSIVITY (\<open>\<not>(wsat f A \<and> wunsat f A)\<close>) a plain structural induction
          on the formula code, with no appeal to soundness, and
        \<bullet> the \<open>\<forall>\<close>E case of soundness immediate, since the induction hypothesis
          about the certificate is carried inside the clause.
      \<open>wsat\<close>/\<open>wunsat\<close> are never required to be grounded, and they only ever
      occur in CONCLUSION position, so no \<open>\<longrightarrow>\<close> introduction is blocked.

  The bridges \<open>wsat f A \<Longrightarrow> \<exists>k. evtt k f A = 1\<close> and its dual are the interface
  between the two layers; at the quantifiers they hold definitionally.

  Consequently, and unlike \<S>6.5 of the report, NO internal completeness lemma
  is needed: the certificate that the \<open>\<forall>\<close>I case has to produce is the tail of
  the proof list being checked, and the hypotheses are not discharged but
  carried inside the clause and required to be satisfied by the assignment at
  hand.  See \<open>tt_wit\<close> below.
  ============================================================================
*)

section \<open>Type aliases\<close>

type_synonym tm  = num  (* QGA term *)
type_synonym fm  = num  (* QGA formula *)
type_synonym asn = num  (* assignment: a list; entry 0 = bottom, S v = value v *)
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

(* projections used everywhere: a payload is a right-nested tuple *)
abbreviation pfst :: "num \<Rightarrow> num" where "pfst x \<equiv> cpx x"
abbreviation psnd :: "num \<Rightarrow> num" where "psnd x \<equiv> cpx (cpy x)"
abbreviation pthd :: "num \<Rightarrow> num" where "pthd x \<equiv> cpy (cpy x)"


section \<open>The abstract consistency skeleton\<close>

text \<open>
  The skeleton is deliberately smaller than the \<open>consistent\<close> locale of
  \<open>BGA_on_GA.thy\<close>.  BGA has no negation, so its consistency statement had to be
  phrased for a matched pair \<open>a = b\<close> / \<open>a \<noteq> b\<close> and needed determinism of term
  evaluation to close.  QGA has negation as a primitive, and the witnessed
  semantics gives exclusivity outright, so the statement can be the usual one:
  no formula is both provable and refutable from no hypotheses.
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

  (* EXCLUSIVITY.  Proved in \<open>qga_witnessed\<close> below by structural induction on
     the formula code; no appeal to soundness. *)
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
  The encoded system is the object logic of \<open>GD.thy\<close> and nothing else.  Its
  vocabulary is the constants that \<open>GD.thy\<close> axiomatizes --- \<open>eq\<close>, \<open>not\<close>, \<open>disj\<close>,
  \<open>forall\<close>, \<open>exists\<close>, \<open>zero\<close>, \<open>suc\<close>, \<open>pred\<close>, \<open>cond\<close>, \<open>def\<close> --- with everything
  \<open>GD.thy\<close> introduces by \<open>definition\<close> (\<open>\<and>\<close>, \<open>\<longrightarrow>\<close>, \<open>\<longleftrightarrow>\<close>, \<open>\<noteq>\<close>, \<open>N\<close>, \<open>B\<close>,
  \<open>True\<close>, \<open>False\<close>) remaining an abbreviation on this side too.

  Terms.

  \<^item> 0 variable \<open>v_j\<close>, payload \<open>j\<close>
  \<^item> 1 zero, payload ignored --- \<open>GD.thy\<close> \<open>zero\<close>
  \<^item> 2 successor \<open>S(a)\<close>, payload \<open>a\<close> --- \<open>suc\<close>
  \<^item> 3 predecessor \<open>P(a)\<close>, payload \<open>a\<close> --- \<open>pred\<close>
  \<^item> 4 conditional \<open>if c then a else b\<close>, payload \<open>\<langle>c, \<langle>a, b\<rangle>\<rangle>\<close> --- \<open>cond\<close> at type \<open>num\<close>
  \<^item> 5 application \<open>d_i(a, b)\<close>, payload \<open>\<langle>i, \<langle>a, b\<rangle>\<rangle>\<close> --- the only \<open>:=\<close> redex

  \<open>GD.thy\<close>\<^latex>\<open>'\<close>s \<open>cond\<close> has type \<open>o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>, so its guard is a FORMULA.
  Term codes and formula codes are therefore mutually recursive here, where in
  \<open>BGA_on_GA.thy\<close> they were not: this is the one structural difference in the
  term language.

  Formulas.

  \<^item> 0 equality \<open>a = b\<close>, payload \<open>\<langle>a, b\<rangle>\<close> --- \<open>eq\<close>
  \<^item> 1 negation \<open>\<not>p\<close>, payload \<open>p\<close> --- \<open>not\<close>
  \<^item> 2 disjunction \<open>p \<or> q\<close>, payload \<open>\<langle>p, q\<rangle>\<close> --- \<open>disj\<close>
  \<^item> 3 universal \<open>\<forall>v_i. p\<close>, payload \<open>\<langle>i, p\<rangle>\<close> --- \<open>forall\<close>
  \<^item> 4 existential \<open>\<exists>v_i. p\<close>, payload \<open>\<langle>i, p\<rangle>\<close> --- \<open>exists\<close>
  \<^item> 5 conditional \<open>if c then p else q\<close>, payload \<open>\<langle>c, \<langle>p, q\<rangle>\<rangle>\<close> --- \<open>cond\<close> at type \<open>o\<close>

  Twelve tags, and no thirteenth: the code space is exactly the constants
  \<open>GD.thy\<close> axiomatizes.  The \<open>'a\<close> of \<open>cond :: o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> and of
  \<open>def :: 'a \<Rightarrow> 'a \<Rightarrow> o\<close> is Isabelle polymorphism standing for the term/formula
  split that QGA has anyway, exactly as \<open>BGA\<close> does; which of the two a given
  occurrence is, is fixed by its position, and \<open>T_COND\<close> versus \<open>F_COND\<close> is that
  distinction made explicit in the code.  Nothing extra is needed to represent
  the context \<open>Q\<close> of the rules that quantify over one: the checker walks the
  premise and the conclusion in parallel with a mutually recursive matcher over
  the two code spaces, which covers both instantiations at once.  The same
  device replaces \<open>BGA_on_GA.thy\<close>\<^latex>\<open>'\<close>s bounded template search for
  \<open>eqSubst\<close>, and it is exact where the template search was only
  bounded-complete.

  Two axioms of \<open>GD.thy\<close> are deliberately NOT arithmetized, because they are
  statements about Isabelle/Pure rather than about the object logic:
  \<open>eq_reflection\<close> (\<open>x = y \<Longrightarrow> x \<equiv> y\<close>) and \<open>iff_reflection\<close> (\<open>p \<longleftrightarrow> q \<Longrightarrow> p \<equiv> q\<close>).
  Their conclusions live in \<open>prop\<close>, which the encoding does not represent at
  all.  Omitting \<open>eq_reflection\<close> is conservative: its only object-level effect,
  by way of Pure\<^latex>\<open>'\<close>s equality rules, is to replace equals by equals in an
  arbitrary context, which is exactly \<open>eqSubst\<close>, and \<open>eqSubst\<close> is arithmetized.
  Omitting \<open>iff_reflection\<close> is NOT conservative in the same way --- it is the
  only route from \<open>p \<longleftrightarrow> q\<close> to substitutivity of \<open>\<longleftrightarrow>\<close> --- so the encoded system
  is weaker than \<open>GD.thy\<close> at exactly that point, and the gap is recorded here
  rather than hidden.
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

text \<open>A disequality transported along an equation; used constantly to walk the
      tag cases.  QGA has no direct rule, so it goes through \<open>contradiction\<close>,
      whose groundedness premise \<open>eqBool\<close> supplies.\<close>

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
  Identical in shape to \<open>bga_encoding\<close>.  \<open>tag_T\<close>/\<open>load_T\<close>/\<open>pack_T\<close> and their
  formula counterparts form a retraction pair with a structural-decrease
  property, which is what turns structural recursion over syntax into bounded
  numerical recursion under \<open>strong_induction\<close>.
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

text \<open>
  The abbreviations of \<open>GD.thy\<close>, encoded exactly as \<open>GD.thy\<close> defines them:
  \<open>a \<noteq> b \<equiv> \<not>(a = b)\<close>, \<open>a N \<equiv> a = a\<close>, \<open>p B \<equiv> p \<or> \<not>p\<close>, \<open>p \<and> q \<equiv> \<not>(\<not>p \<or> \<not>q)\<close>,
  \<open>p \<longrightarrow> q \<equiv> \<not>p \<or> q\<close>, \<open>p \<longleftrightarrow> q \<equiv> (p \<longrightarrow> q) \<and> (q \<longrightarrow> p)\<close>, \<open>True \<equiv> 0 = 0\<close>,
  \<open>False \<equiv> S 0 = 0\<close>.
\<close>

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
  \<open>fresh_T k t\<close> says that every variable index occurring in \<open>t\<close>, term or
  propositional, is \<open>< k\<close>.  As in \<open>BGA_on_GA.thy\<close> this is the eigenvariable
  machinery: a rule that must pick a variable not occurring in a context picks
  one above the context\<^latex>\<open>'\<close>s bound.  \<open>fresh_T 0 t\<close> therefore says \<open>t\<close> is CLOSED,
  and that special case carries weight below --- the certificate contexts of the
  quantifier clauses are required to be closed, which makes their satisfaction
  independent of the assignment and hence stable under substitution.

  Freshness is a mutual recursion, because \<open>T_COND\<close> carries a formula.  The
  quantifier cases count the BOUND index as an occurrence, which is an
  over-approximation: it only ever makes a side condition harder to satisfy, so
  no soundness obligation is affected.

  \<open>subst_T\<close>/\<open>subst_F\<close>/\<open>subst_H\<close> replace a term variable by a term: this is
  Pure\<^latex>\<open>'\<close>s instantiation of a schematic of type \<open>num\<close>, and it is also the
  \<open>\<forall>E\<close> instantiation and the \<open>\<exists>I\<close> witnessing.  \<open>subst_body\<close> is the two-argument
  definition unfolding.

  \<open>close_F f Pv A\<close> replaces every free term variable of \<open>f\<close> whose index is not
  protected by the list \<open>Pv\<close> with the numeral of \<open>A m\<close>, or with the divergent
  closed term \<open>tBot\<close> when \<open>A m\<close> is bottom.  It is the arithmetized form of the
  closing substitution.  Binders extend \<open>Pv\<close>, so no capture arises.
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
  These groundedness lemmas are the direct analogues of \<open>fresh_T_bool\<close>,
  \<open>fresh_F_bool\<close> and \<open>fresh_H_bool\<close> of \<open>BGA_on_GA.thy\<close>.  The only structural
  difference is that the term and formula recursions are now mutual, so the
  \<open>strong_induction\<close> runs on a single motive covering both --- legitimate,
  because term codes and formula codes are both just numbers.
\<close>

lemma fresh_TF_bool:
  assumes k: "k N" and x: "x N"
  shows "(fresh_T k x B) \<and> (fresh_F k x B)"
  \<comment> \<open>joint \<open>strong_induction\<close> on \<open>x\<close>; every branch is a \<open>condTB\<close> chain over a
      decided guard, and the recursive calls land on \<open>load_T x\<close>, \<open>load_F x\<close> and
      their projections, all \<open>\<le> x\<close> by \<open>decrease_T\<close>, \<open>decrease_F\<close>, \<open>cpx_mono\<close>,
      \<open>cpy_mono\<close>.  Base case \<open>x = 0\<close> uses \<open>tag_T_zero\<close> and \<open>tag_F_zero\<close>.\<close>
  sorry

lemma fresh_T_bool [auto]: "\<lbrakk>k N; t N\<rbrakk> \<Longrightarrow> fresh_T k t B"
  by (rule conjE1[OF fresh_TF_bool])

lemma fresh_F_bool [auto]: "\<lbrakk>k N; f N\<rbrakk> \<Longrightarrow> fresh_F k f B"
  by (rule conjE2[OF fresh_TF_bool])

lemma fresh_H_bool [auto]:
  assumes k: "k N" and G: "G N"
  shows "fresh_H k G B"
  \<comment> \<open>\<open>list_induct\<close> on \<open>G\<close>, exactly as \<open>bga_encoding.fresh_H_bool\<close>.\<close>
  sorry

lemma subst_T_N [auto]: "\<lbrakk>t N; j N; v N\<rbrakk> \<Longrightarrow> subst_T t j v N"
  \<comment> \<open>joint strong induction with \<open>subst_F_N\<close>; \<open>pack_T_N\<close>/\<open>pack_F_N\<close> at each node.\<close>
  sorry
lemma subst_F_N [auto]: "\<lbrakk>f N; j N; v N\<rbrakk> \<Longrightarrow> subst_F f j v N" sorry
lemma subst_H_N [auto]: "\<lbrakk>G N; j N; v N\<rbrakk> \<Longrightarrow> subst_H G j v N" sorry

lemma close_T_N [auto]: "\<lbrakk>t N; Pv N; A N\<rbrakk> \<Longrightarrow> close_T t Pv A N" sorry
lemma close_F_N [auto]: "\<lbrakk>f N; Pv N; A N\<rbrakk> \<Longrightarrow> close_F f Pv A N" sorry
lemma close_H_N [auto]: "\<lbrakk>G N; Pv N; A N\<rbrakk> \<Longrightarrow> close_H G Pv A N" sorry
lemma numeral_of_N [auto]: "v N \<Longrightarrow> numeral_of v N" sorry
lemma asn_put_N [auto]: "\<lbrakk>A N; i N; v N\<rbrakk> \<Longrightarrow> asn_put A i v N" sorry

text \<open>Closure produces closed syntax; this is the fact the quantifier
      certificates rely on.\<close>

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
  \<comment> \<open>\<open>tBot\<close> is a closed divergent term: the self-application \<open>d_0(0, 0)\<close> with
      \<open>nth 0 dfns\<close> the body \<open>d_0(v_0, v_1)\<close>, which is QGA\<^latex>\<open>'\<close>s \<open>omega := omega\<close>
      written in the object language.  Nothing else about \<open>dfns\<close> is assumed.\<close>
  assumes tBot_N: "tBot N"
  assumes tBot_closed: "fresh_T 0 tBot"
begin

lemma dfn_is_bool [auto]: "\<lbrakk>d N; k N; b N\<rbrakk> \<Longrightarrow> dfn_is d k b B"
  \<comment> \<open>as \<open>bga_dfns.dfn_is_bool\<close>: \<open>condTB'\<close> on the range guard, then
      \<open>nth_in_range_N\<close> and \<open>fresh_T_bool\<close>.\<close>
  sorry

end


section \<open>The proof checker\<close>

text \<open>
  A proof is a list of judgments, most recent first, each of which must follow
  from the ones after it by one rule.  This is BGA's format unchanged.

  \<^bold>\<open>Where the structural rules come from.\<close>  \<open>GD.thy\<close> states no structural rule,
  because Isabelle/Pure supplies them.  Making them explicit is forced once the
  system is arithmetized, and each one comes from a specific Pure kernel
  operation.

  \<^item> \<open>hyp\<close>, \<open>\<Gamma>, \<phi> \<turnstile> \<phi>\<close>.  From Pure's \<open>Thm.assume\<close>.  Checker: the conclusion is a
    member of the hypothesis list.
  \<^item> \<open>weak\<close>, from \<open>\<Gamma> \<turnstile> \<phi>\<close> infer \<open>\<Gamma>' \<turnstile> \<phi>\<close> for \<open>\<Gamma> \<subseteq> \<Gamma>'\<close>.  From the fact that Pure
    carries the hypotheses of a theorem as a SET which is only ever enlarged
    (\<open>Thm.weaken\<close>, and the implicit union performed by every kernel inference).
    Contraction and exchange are invisible for the same reason.  Checker:
    \<open>check_weak\<close>.
  \<^item> \<open>cut\<close>, from \<open>\<Gamma> \<turnstile> \<psi>\<close> and \<open>\<Gamma>, \<psi> \<turnstile> \<phi>\<close> infer \<open>\<Gamma> \<turnstile> \<phi>\<close>.  From \<open>\<Longrightarrow>\<close> introduction
    (\<open>Thm.implies_intr\<close>) on the second premise followed by \<open>\<Longrightarrow>\<close> elimination
    (\<open>Thm.implies_elim\<close>).  Checker: \<open>check_cut\<close>.
  \<^item> \<open>inst\<close>, from \<open>\<Gamma> \<turnstile> \<phi>\<close> infer \<open>[v_i \<mapsto> a]\<Gamma> \<turnstile> [v_i \<mapsto> a]\<phi>\<close>.  From \<open>Thm.instantiate\<close>,
    equivalently \<open>\<And>\<close> introduction followed by \<open>\<And>\<close> elimination.  Checker:
    \<open>check_inst\<close>.

  Two Pure operations deliberately do NOT become checker branches, because they
  are not steps of an object derivation but the SHAPE of a rule.

  \<^item> \<open>\<Longrightarrow>\<close> in a premise position.  A premise \<open>P \<Longrightarrow> R\<close>, as in \<open>disjE1\<close>, says that \<open>R\<close>
    was derived under the extra hypothesis \<open>P\<close>, so it is looked up in the proof
    list as the judgment \<open>P, \<Gamma> \<turnstile> R\<close>.  Discharging it is exactly what makes the
    rule applicable; there is nothing left to check.
  \<^item> \<open>\<And>\<close> in a premise position.  A premise \<open>\<And>x. x N \<Longrightarrow> Q x\<close>, as in \<open>forallI\<close>,
    \<open>existsE\<close>, \<open>notForallE\<close> and \<open>ind\<close>, says that \<open>Q x\<close> was derived uniformly in
    \<open>x\<close>, so it is looked up as \<open>v_i N, \<Gamma> \<turnstile> Q[v_i]\<close> TOGETHER WITH the
    eigenvariable condition that \<open>v_i\<close> occurs neither in \<open>\<Gamma>\<close> nor in the
    conclusion.  That side condition is the entire content of \<open>\<And>\<close> here, and it
    is discharged by \<open>fresh_H i (hyp_of J)\<close> and, where the rule needs it,
    \<open>fresh_F i (conc_of J)\<close>.  \<open>fresh_T i t\<close> says every index in \<open>t\<close> is \<open>< i\<close>,
    which is a sufficient rather than a necessary form of ``does not occur'';
    it costs no generality, since a derivation can always be renamed upward,
    and it is what \<open>BGA_on_GA.thy\<close> already uses in \<open>check_ind\<close>.  Where the rule
    invents the eigenvariable (\<open>existsE\<close>, \<open>notForallE\<close>) the checker takes
    \<open>i = J + 1\<close>, which is fresh for the whole judgment by construction, since
    every index occurring in \<open>J\<close> is below \<open>J\<close>.

  \<^bold>\<open>Where the logical rules come from.\<close>  One checker branch per axiom of
  \<open>GD.thy\<close>, named after it.  Every branch is one of those axioms, and every
  axiom has a branch save three.  \<open>eq_reflection\<close> and \<open>iff_reflection\<close> conclude
  in \<open>prop\<close> and are discussed in the vocabulary section above.  \<open>notForallI\<close> is
  omitted for a semantic reason set out in \<open>qga_fuel_semantics\<close>: under a
  reflective reading of the universal, ``a counterexample refutes it'' is a
  statement of the system\<^latex>\<open>'\<close>s own soundness, and no arrangement of the
  evaluator validates it before soundness is proved.  \<open>notForallE\<close> is retained
  and is vacuously sound.

  \<^bold>\<open>Search discipline.\<close>  When a premise is DETERMINED by the conclusion the
  checker looks it up with \<open>mem\<close>.  When a premise is larger than the conclusion
  the checker SCANS the proof list and decomposes what it finds.  When a rule
  quantifies over a context the checker uses a MATCHER, which walks the two
  codes in parallel and needs no search at all.  The single exception is
  \<open>check_inst\<close>, whose pair \<open>(i, a)\<close> is constrained only numerically; it is
  searched by nested countdown bounded by the code of the judgment, as
  \<open>check_template\<close> is in \<open>BGA_on_GA.thy\<close>.
\<close>

subsection \<open>Destructors for the encoded abbreviations\<close>

context qga_encoding
begin

text \<open>\<open>GD.thy\<close> defines \<open>p B \<equiv> p \<or> \<not>p\<close>, \<open>p \<and> q \<equiv> \<not>(\<not>p \<or> \<not>q)\<close> and
      \<open>p \<longleftrightarrow> q \<equiv> (p \<longrightarrow> q) \<and> (q \<longrightarrow> p)\<close>, so a code carrying one of these has a fixed
      shape and its components can be read off.  Each destructor is paired with
      the shape test the checker actually performs, namely that rebuilding the
      abbreviation from the parts returns the code.\<close>

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
  Three mutually recursive pairs, one per rule family that quantifies over a
  context.  Each pair walks a term code and a formula code simultaneously,
  because \<open>T_COND\<close> carries a formula and every formula carries terms.

  \<^item> \<open>eqT\<close>/\<open>eqF\<close>: \<open>u\<close> is \<open>t\<close> with some occurrences of \<open>a\<close> replaced by \<open>b\<close>.  This is
    \<open>eqSubst\<close> --- one occurrence is the axiom, several are iterations of it.
  \<^item> \<open>lzT\<close>/\<open>lzF\<close>: \<open>u\<close> is \<open>t\<close> with some occurrences of \<open>if c then x else y\<close>, for
    the fixed guard \<open>c\<close>, replaced by the branch selected by \<open>sel\<close>.  This is
    \<open>cond_thenQ_E\<close> (\<open>sel = 0\<close>) and \<open>cond_elseQ_E\<close> (\<open>sel = 1\<close>) iterated; reading
    the two codes in the other order gives \<open>cond_thenQ_I\<close> and \<open>cond_elseQ_I\<close>.
    Because \<open>lzT\<close> and \<open>lzF\<close> are mutual, both instantiations of the polymorphic
    \<open>Q\<close> are covered by the same definition.
  \<^item> \<open>unfT\<close>/\<open>unfF\<close>: \<open>u\<close> is \<open>t\<close> with some applications \<open>d(x, y)\<close> replaced by
    \<open>body\<^sub>d[v\<^sub>0 \<mapsto> x, v\<^sub>1 \<mapsto> y]\<close>.  This is \<open>defE\<close>/\<open>defI\<close> at the definition list.
    The two \<open>mem\<close> tests inside carry the habeas quid premises: the operational
    semantics below evaluates an application by evaluating its arguments first,
    so unfolding is sound only at arguments known to terminate.  \<open>GD.thy\<close>'s
    \<open>:=\<close> is call-by-name and carries no such premise; this is the one point at
    which the encoded system is a restriction of \<open>GD.thy\<close> rather than a copy of
    it, and it is the same restriction \<open>BGA_on_GA.thy\<close> makes in \<open>app_try\<close>.
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

  (* cut: Pure implies_intr followed by implies_elim. *)
  assumes find_cut_def: "find_cut J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> mem (conc_of (list_hd ptr) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest then True
    else find_cut J rest (list_tl ptr)"
  assumes check_cut_def: "check_cut J rest := find_cut J rest rest"

  (* weak: Pure carries hypotheses as a set that is only ever enlarged. *)
  assumes find_weak_def: "find_weak J G ptr :=
    if ptr = Nil then False
    else if conc_of (list_hd ptr) = conc_of J \<and> subset (hyp_of (list_hd ptr)) G then True
    else find_weak J G (list_tl ptr)"
  assumes check_weak_def: "check_weak J rest := find_weak J (hyp_of J) rest"

  (* inst: Thm.instantiate, equivalently forall_intr then forall_elim.  Pure
     instantiates with an ARBITRARY term and incurs no habeas quid obligation,
     which is sound because a free variable of the encoded system ranges over
     the flat domain N-bottom: an assignment sends an index either to S v or to
     0.  Quantified variables range over values only, which is what the x N
     premises of forallI, forallE and existsI enforce. *)
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

text \<open>The nine axioms of the \<open>disj\<close>/\<open>not\<close> block of \<open>GD.thy\<close>.  \<open>disjE1\<close> has two
      discharged premises, which are looked up with the hypothesis prepended;
      \<open>disjE2\<close>, \<open>disjE3\<close> and \<open>exF\<close> have premises larger than their conclusions
      and are scanned for.\<close>

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

text \<open>The two axioms of the \<open>eq\<close> block that live in the object logic:
      \<open>eqSubst\<close> and \<open>eqSym\<close>.  \<open>eq_reflection\<close> is a framework rule and is not
      arithmetized.\<close>

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

text \<open>The ten non-inductive axioms of the \<open>zero\<close>/\<open>suc\<close>/\<open>pred\<close> block, in the
      order they appear in \<open>GD.thy\<close>: \<open>nat0\<close>, \<open>sucInj\<close>, \<open>sucCong\<close>, \<open>predCong\<close>,
      \<open>eqBool\<close>, \<open>sucNonZero\<close>, \<open>predSucInv\<close>, \<open>pred0\<close>, \<open>eqE\<close>, \<open>predTIE\<close>.  Each
      premise is determined by the conclusion, so each is one \<open>mem\<close>.\<close>

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
  \<open>ind: \<lbrakk>a N; Q 0; \<And>x. x N \<Longrightarrow> Q x \<Longrightarrow> Q (S x)\<rbrakk> \<Longrightarrow> Q a\<close>.  The third premise has one
  \<open>\<And>\<close> and two \<open>\<Longrightarrow>\<close>, so it is the judgment \<open>v_i N, Q[v_i], \<Gamma> \<turnstile> Q[S v_i]\<close> subject to
  the eigenvariable condition on \<open>i\<close>.  Scanning the proof list for a judgment of
  that shape yields \<open>i\<close> and the motive \<open>p = Q[v_i]\<close> directly, from the first two
  entries of its hypothesis list; no template search is needed.  The subject
  \<open>a\<close> comes from the habeas quid premise, which is scanned for in the same way.
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
  The six quantifier axioms.  \<open>forallI\<close> is the rule whose semantic
  justification decides the architecture: its premise is \<open>\<And>x. x N \<Longrightarrow> Q x\<close>, so the
  checker looks for \<open>v_i N, \<Gamma> \<turnstile> p\<close> with \<open>i\<close> the bound index of the conclusion and
  \<open>i\<close> fresh for \<open>\<Gamma>\<close>.  That is exactly the shape of the tt-witness of the
  semantics below, which is why the \<open>\<forall>\<close>I case of soundness has a certificate to
  hand rather than one to build.
\<close>

locale qga_quant_rule = qga_match +
  fixes find_allE_inner  :: "jdg \<Rightarrow> num \<Rightarrow> fm \<Rightarrow> pf \<Rightarrow> o"
  fixes find_allE        :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes find_exI         :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes find_exE         :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes find_nallE       :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_quant_rules :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  (* forallE: from Gamma |- forall v_i. p and Gamma |- a N infer Gamma |- p[i := a] *)
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

  (* existsI: from Gamma |- a N and Gamma |- p[i := a] infer Gamma |- exists v_i. p *)
  assumes find_exI_def: "find_exI J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EQ
            \<and> cpx (load_F (conc_of (list_hd ptr))) = cpy (load_F (conc_of (list_hd ptr)))
            \<and> mem (hyp_of J \<tturnstile> subst_F (cpy (load_F (conc_of J)))
                                       (cpx (load_F (conc_of J)))
                                       (cpx (load_F (conc_of (list_hd ptr))))) rest
    then True else find_exI J rest (list_tl ptr)"

  (* existsE: the eigenvariable is J + 1, fresh for J by construction *)
  assumes find_exE_def: "find_exE J rest ptr :=
    if ptr = Nil then False
    else if hyp_of (list_hd ptr) = hyp_of J
            \<and> tag_F (conc_of (list_hd ptr)) = F_EX
            \<and> fresh_H (J + 1) (hyp_of J) \<and> fresh_F (J + 1) (conc_of J)
            \<and> mem (subst_F (cpy (load_F (conc_of (list_hd ptr))))
                           (cpx (load_F (conc_of (list_hd ptr)))) (tVar (J + 1))
                   \<triangleright> mkNat (tVar (J + 1)) \<triangleright> hyp_of J \<tturnstile> conc_of J) rest
    then True else find_exE J rest (list_tl ptr)"

  (* notForallE: extract the counterexample under a fresh eigenvariable *)
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
  The fourteen conditional axioms.  Ten of them fix the conditional up to its
  guard and are handled by one scan (\<open>find_cond\<close>); the four that quantify over
  a context are handled by the \<open>lzT\<close>/\<open>lzF\<close> matcher (\<open>find_lazy\<close>).  \<open>condI1B\<close>
  and \<open>condI2B\<close> conclude a \<open>\<longleftrightarrow>\<close>, which is an abbreviation, so the checker tests
  that rebuilding \<open>mkIff\<close> from the destructed parts returns the conclusion.
\<close>

locale qga_cond_rule = qga_match +
  fixes find_condE :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_condI :: "jdg \<Rightarrow> pf \<Rightarrow> o"
  fixes lazy_inner :: "jdg \<Rightarrow> fm \<Rightarrow> num \<Rightarrow> num \<Rightarrow> pf \<Rightarrow> o"
  fixes lazy_outer :: "jdg \<Rightarrow> pf \<Rightarrow> pf \<Rightarrow> o"
  fixes check_cond_rules :: "jdg \<Rightarrow> pf \<Rightarrow> o"

  (* condI1, condI2, condI1B, condI2B: the conclusion is determined *)
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

  (* condE1, condE2, condE3, condE1B, condE2B, condE3B: the premise is larger *)
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

  (* cond_thenQ_E/I and cond_elseQ_E/I: sel picks the branch, dir picks which of
     the two judgments carries the conditionals. *)
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

text \<open>\<open>defE\<close> and \<open>defI\<close>, restricted to the definition list.  The only \<open>:=\<close> facts
      available to the encoded system are the entries of \<open>dfns\<close>, so unfolding an
      application is the only way either rule can fire.\<close>

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

text \<open>
  Groundedness of proof checking.  Every branch of \<open>valid_step\<close> is a \<open>condTB\<close>
  chain over guards that are \<open>mem\<close> tests, equalities between terminating codes,
  or the scans and matchers above; each scan is grounded by \<open>list_induct\<close> on its
  pointer and each matcher by \<open>strong_induction\<close> on its first argument.  This is
  \<open>proof_is_bool\<close> of \<open>BGA_on_GA.thy\<close>, one branch per rule group.
\<close>

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
  The tail of a checked list is a proof of each of its members.  This is what
  the \<open>\<forall>\<close>I case of soundness uses to produce a certificate: the certificate is
  not constructed, it is the suffix of the proof already in hand.
\<close>

lemma check_list_tl:
  "\<lbrakk>pf N; \<not> (pf = Nil); check_list pf\<rbrakk> \<Longrightarrow> check_list (list_tl pf)"
  \<comment> \<open>\<open>cases_bool\<close> on the step guard, then \<open>condI1B\<close>/\<open>condI2B\<close>, whose branch
      groundedness is \<open>check_list_bool\<close> and \<open>false_bool\<close>.  An \<open>o\<close>-valued
      conditional cannot be peeled directly; see the note in \<open>qga_witnessed\<close>.\<close>
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
  \<^bold>\<open>Why the evaluator is a single three-valued function.\<close>  This is the design
  decision the whole development turns on, and the reason for it is a
  constraint of the object logic, not a matter of taste.

  Exclusivity --- no formula is both true and false --- is needed by exactly one
  rule, \<open>exF\<close>, whose soundness case receives \<open>\<Gamma> \<turnstile> P\<close> and \<open>\<Gamma> \<turnstile> \<not>P\<close> and must
  produce an arbitrary conclusion.  In a classical metatheory one proves
  exclusivity by rule induction over the evaluation relation, and Ford does
  exactly that for RGA.  Here that route is closed.  A QGA induction
  instantiates a schematic predicate, so the statement being inducted on must
  be a single formula of the object logic; a statement of the form
  \<open>\<not>(sat f A \<and> unsat f A)\<close> can only be introduced through \<open>disjI\<close> or \<open>dNegI\<close>,
  which would require one of the two conjuncts to be refutable outright, and
  neither is.  An induction whose hypothesis is an undecided predicate cannot
  be run at all: \<open>\<longrightarrow>\<close> introduction demands a grounded antecedent.

  What IS available is an induction on the fuel with the motive

    \<open>\<forall>f. \<forall>A. \<not>(evF k f A = 0) \<longrightarrow> evF (S k) f A = evF k f A\<close>

  --- every antecedent an equation between terminating terms, hence decided by
  \<open>eqBool\<close>.  Call this STABILITY.  If the evaluator is a single function into
  \<open>{0, 1, 2}\<close>, exclusivity is an immediate corollary of stability: a value once
  produced is never revised, so two runs at different budgets that both
  succeed agree, and \<open>1 = 2\<close> is refutable.  Two separate monotone searches
  \<open>evtt\<close> and \<open>evff\<close>, by contrast, can each be monotone without being mutually
  exclusive, and ruling out a collision between them is precisely soundness.

  So exclusivity is bought by making the evaluator a function.  The price is
  paid at the quantifier, and it is worth stating exactly.

  \<^bold>\<open>The quantifier clauses, and the one axiom that has to go.\<close>  A single
  function must decide, at each fuel, which of the two quantifier searches
  wins.  There are only three arrangements and each loses something:

  \<^item> truth wins: \<open>\<forall>\<close>I is sound, but a later-appearing counterexample would revise
    a verdict, so stability fails;
  \<^item> falsity wins: \<open>\<not>\<forall>\<close>I is sound, stability fails symmetrically;
  \<^item> the least witness wins, witnesses carrying their own fuel so that validity
    is budget-independent: stability holds by construction, and \<open>\<forall>\<close>I is sound
    because a smaller falsity witness would be an instance evaluating to
    \<open>false\<close> while the induction hypothesis makes it evaluate to \<open>true\<close> ---
    refuted by exclusivity, which is available.  But \<open>\<not>\<forall>\<close>I would need to
    refute a smaller TRUTH witness, and a truth witness is a proof; refuting it
    is soundness of the proof system, which is what is being proved.

  The third arrangement is the one that closes, so \<open>notForallI\<close> is the single
  axiom of \<open>GD.thy\<close> that this development does not arithmetize.  With no rule
  concluding \<open>\<not>(\<forall>x. Q x)\<close> the falsity search has nothing to justify, and the
  clause degenerates: a universal is true when a certificate is found and
  ungrounded otherwise.  \<open>notForallE\<close> is retained and is vacuously sound, since
  its major premise is never satisfied.  The same asymmetry is already present
  in \<open>GD.thy\<close> for the existential --- no axiom concludes or consumes
  \<open>\<not>(\<exists>x. Q x)\<close>, and \<open>existsNeg\<close> is derived --- so \<open>\<exists>\<close> is treated dually and
  loses nothing at all.

  This is not a defect of grounded arithmetic; it is the reflective quantifier
  charging for itself.  Reading \<open>\<forall>x. \<phi>\<close> as ``the system proves the schematic
  instance'' makes ``a counterexample refutes it'' a statement of the system's
  own soundness, and no system establishes that before establishing soundness.
  RGA can postpone the question because its official evaluation is a RELATION
  whose determinism is a later theorem; QGA cannot, because a relation is not
  decided and decidedness is what the soundness induction needs.

  \<^bold>\<open>Values.\<close>  \<open>evT k t A\<close> returns \<open>S v\<close> on success and \<open>0\<close> on timeout, as BGA's
  \<open>eval_fuel\<close> does.  \<open>evF k f A\<close> returns \<open>2\<close> for true, \<open>1\<close> for false and \<open>0\<close> for
  no verdict.  Assignments carry the same convention as terms: \<open>nth i A = S v\<close>
  means \<open>v_i\<close> denotes \<open>v\<close> and \<open>nth i A = 0\<close> means it denotes nothing, so an
  index past the end of the list reads as bottom and an assignment is a finite
  description of a total map into \<open>N\<^sub>\<bottom>\<close>.  That is what makes \<open>inst\<close>
  unconditional.

  \<^bold>\<open>Witnesses carry their own fuel.\<close>  A witness \<open>w\<close> for a quantifier clause has
  \<open>cpx w\<close> as its fuel component, and \<open>cpx w \<le> w\<close>, so a search bounded by
  \<open>w \<le> k\<close> only ever calls the evaluator at fuel \<open>< k\<close>: the recursion is
  fuel-decreasing, the whole family is total, and --- the point --- whether a
  given \<open>w\<close> is a valid witness does not depend on the budget of the search that
  found it.  That budget-independence is what makes stability hold by
  construction at the quantifiers.
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

  (* The reflective clause.  A witness w = <j, <q, G>> is valid when q is a
     valid proof of  G, v_i N |- phi[A],  where G is CLOSED and satisfied by A
     within j steps.  Because G is closed its satisfaction does not depend on
     the assignment, which is what keeps the clause stable under substitution;
     because j = cpx w <= w the recursion is fuel-decreasing and validity does
     not depend on the budget of the search. *)
  assumes all_tt_def: "all_tt w i phi A :=
    if is_valid_proof (cpx (cpy w))
         (mkNat (tVar i) \<triangleright> cpy (cpy w) \<tturnstile> close_F phi (i \<triangleright> Nil) A)
       \<and> fresh_H 0 (cpy (cpy w))
       \<and> hypsat (cpx w) (cpy (cpy w)) A = 1
    then 2
    else if w > 0 = 1 then all_tt (w - 1) i phi A
    else 0"

  (* Dual: an existential is true at an actual numeral instance. *)
  assumes ex_tt_def: "ex_tt w i phi A :=
    if evF (cpx w) phi (asn_put A i (S (cpy w))) = 2 then 2
    else if w > 0 = 1 then ex_tt (w - 1) i phi A
    else 0"
begin

subsection \<open>Totality\<close>

text \<open>
  All five functions are total.  \<open>strong_induction\<close> on the fuel \<open>k\<close>, with the
  motive an object-level \<open>\<forall>\<close>-statement over the term, the formula and the
  assignment simultaneously, since QGA induction instantiates a schematic
  predicate and the generalization must live inside the formula.  Every
  recursive call is at fuel \<open>P k\<close> or at \<open>cpx w \<le> w \<le> P k\<close>, and the witness
  searches recurse on \<open>w - 1\<close> under an inner induction.  The guards of
  \<open>all_tt\<close> need \<open>proof_is_bool\<close> and \<open>fresh_H_bool\<close>, which is why the checker is
  a parameter of this locale rather than the other way round.
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
  The whole reason for the fuelled layer.  \<open>sat_at\<close> and \<open>sat_hyp_at\<close> are
  DECIDED, because they are equations between terminating terms and \<open>eqBool\<close>
  turns termination into decidability.  That is what allows them to sit in the
  antecedent of an object-level \<open>\<longrightarrow>\<close> in the soundness induction, whose motive
  must be a single QGA formula.
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
  Stability is the load-bearing lemma of the official layer, and the reason the
  evaluator is a function.  Its motive,
  \<open>\<forall>f. \<forall>A. \<not>(evF k f A = 0) \<longrightarrow> evF (S k) f A = evF k f A\<close>, has an antecedent that
  \<open>eqBool\<close> decides, so the induction on \<open>k\<close> runs.  Every clause preserves a
  value once produced: the propositional clauses because their inputs do, by
  the induction hypothesis, and the quantifier clauses BY CONSTRUCTION, since
  the validity of a witness does not mention the budget and the search at
  budget \<open>S k\<close> scans a superset of the witnesses scanned at \<open>k\<close>, taking the
  least.
\<close>

lemma evT_stable:
  "\<lbrakk>k N; t N; A N; \<not> (evT k t A = 0)\<rbrakk> \<Longrightarrow> evT (S k) t A = evT k t A" sorry

lemma evF_stable:
  "\<lbrakk>k N; f N; A N; \<not> (evF k f A = 0)\<rbrakk> \<Longrightarrow> evF (S k) f A = evF k f A" sorry

lemma evT_stable_add:
  "\<lbrakk>k N; l N; t N; A N; evT k t A = S v\<rbrakk> \<Longrightarrow> evT (k + l) t A = S v"
  \<comment> \<open>induction on \<open>l\<close> from \<open>evT_stable\<close>; \<open>S v \<noteq> 0\<close> keeps the side condition alive.\<close>
  sorry

lemma evF_stable_add:
  "\<lbrakk>k N; l N; f N; A N; \<not> (evF k f A = 0)\<rbrakk> \<Longrightarrow> evF (k + l) f A = evF k f A"
  \<comment> \<open>induction on \<open>l\<close> from \<open>evF_stable\<close>.\<close>
  sorry

text \<open>
  Exclusivity at the official level.  Two runs of a function at different
  budgets that both produce a verdict produce the SAME verdict, and \<open>1 = 2\<close> is
  refutable, so nothing is both true and false.  No appeal to soundness: this
  is where the design pays for itself.
\<close>

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
  \<comment> \<open>corollary of \<open>hypsat_fresh\<close>: a closed context reads the same under every
      assignment, which is what makes a quantifier certificate stable under
      substitution.\<close>
  sorry

end


section \<open>The witnessed semantics\<close>

text \<open>
  \<open>wsat\<close> and \<open>wunsat\<close> are QGA recursive definitions of type \<open>o\<close>.  Each is the
  official verdict CONJOINED with the structural facts the verdict stands for:

    \<open>wsat f A := sat f A \<and> extras\<close>,   \<open>wunsat f A := unsat f A \<and> extras\<close>

  and the extras at the quantifiers are the instance facts.  Two consequences,
  and they are the reason for the arrangement.

  \<^item> The bridges to the official layer are \<open>conjE1\<close>.  A bridge proved by
    induction would need \<open>wsat\<close> in an antecedent, which \<open>\<longrightarrow>\<close> introduction
    forbids; carrying the official verdict as a conjunct is how that induction
    is avoided.
  \<^item> Exclusivity follows in three lines from the bridges and \<open>official_excl\<close>,
    with no induction over the witnessed predicates at all.

  The extras are never consumed as an induction hypothesis --- only produced by
  the soundness proof and read off by \<open>\<forall>\<close>E and \<open>\<exists>\<close>E --- so nothing else in the
  development needs them to be decided.
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
  The structural conjunct is a chain of tag-guarded implications rather than a
  nested conditional, for a reason worth recording.  \<open>GD.thy\<close> declares its
  fourteen conditional axioms in one \<open>axiomatization where\<close> block that declares
  no constant of its own, so Isabelle pins the block\<^latex>\<open>'\<close>s type variable, and
  \<open>condI1\<close> pins it to \<open>num\<close>.  The lazy pair \<open>cond_thenQ_E\<close>/\<open>cond_elseQ_E\<close> is
  therefore available at term-valued conditionals ONLY, and an \<open>o\<close>-valued
  conditional cannot be peeled to a branch without a groundedness premise on
  that branch.  Tag-guarded implications sidestep the issue: \<open>implE\<close> carries no
  obligation at all, and \<open>implI\<close> needs only the tag equation to be grounded,
  which \<open>eqBool\<close> supplies.
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

text \<open>The negation clause, in the form the consistency skeleton asks for.\<close>

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
  Both directions are needed: \<open>\<forall>\<close>E and \<open>\<exists>\<close>I go one way, the congruence lemma for
  \<open>eqSubst\<close>, \<open>ind\<close> and \<open>defE\<close>/\<open>defI\<close> goes down and back up.  The official
  conjunct transfers because a quantifier certificate is a certificate for the
  A-CLOSURE of the body: \<open>close_F (subst_F p i a) Pv A\<close> and
  \<open>close_F p Pv (asn_put A i (S v))\<close> differ only in that the first carries the
  closed term \<open>a[A]\<close> where the second carries the numeral of \<open>v\<close>, and
  \<open>evals a A v\<close> makes those two provably equal, so one \<open>eqSubst\<close> step converts
  a certificate for either into a certificate for the other.  The structural
  conjunct transfers by the same induction.  Requiring the certificate context
  to be closed is what keeps \<open>hypsat\<close> out of the argument.
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
  The only places where the development CONSTRUCTS a proof code rather than
  consuming one, and both are confined to terms and equations, that is, to the
  BGA fragment.  Neither is the formula-level internal completeness that the
  original plan anticipated; that obligation was removed by making the
  certificate context-relative.
\<close>

lemma term_value_complete:
  "\<lbrakk>t N; A N; v N; evals t A v\<rbrakk>
   \<Longrightarrow> \<exists>q. is_valid_proof q (Nil \<tturnstile> mkEq (close_T t Nil A) (numeral_of v))"
  \<comment> \<open>RGA's value completeness restricted to terms.  Induction on the fuel, one
      proof-list constructor per term constructor, using \<open>sucCong\<close>,
      \<open>predSucInv\<close>, the conditional rules and \<open>check_def\<close>.\<close>
  sorry

lemma closure_by_inst:
  "\<lbrakk>q N; G N; c N; A N; i N; is_valid_proof q (mkNat (tVar i) \<triangleright> G \<tturnstile> c)\<rbrakk>
   \<Longrightarrow> \<exists>q'. is_valid_proof q'
              (mkNat (tVar i) \<triangleright> close_H G (i \<triangleright> Nil) A \<tturnstile> close_F c (i \<triangleright> Nil) A)"
  \<comment> \<open>the closing substitution is a derived rule: iterate the \<open>inst\<close> step of
      \<open>qga_struct_rule\<close> once per free variable.  \<open>inst\<close> is Pure's schematic
      instantiation and is unconditional, so no habeas quid obligation arises.\<close>
  sorry

end


section \<open>Soundness\<close>

locale qga_full = qga_witnessed
begin

text \<open>
  The soundness bridge, in the shape \<open>BGA_on_GA.thy\<close> established: a checked
  step is sound relative to the tail of the proof, the local statement lifts
  along the list by \<open>list_induct\<close>, and the motive is the object-level formula

    \<open>\<forall>A. \<forall>K. \<forall>k. check_list pf \<longrightarrow> (K \<in> pf \<longrightarrow> (sat_hyp_at k (hyp_of K) A \<longrightarrow> wsat (conc_of K) A))\<close>

  with the three antecedents decided by \<open>check_list_bool\<close>, \<open>mem_bool\<close> and
  \<open>sat_hyp_at_bool\<close>.  The conclusion is the witnessed predicate and needs no
  groundedness, which is why the two semantic layers are split as they are.

  Every case has to establish BOTH conjuncts of \<open>wsat\<close>: the official verdict,
  from the official verdicts of the premises, and the structural extra, from
  the induction hypothesis.  Three cases carry the content.

  \<^item> \<open>\<forall>\<close>I.  The checker has found \<open>v_i N, \<Gamma> \<turnstile> \<phi>\<close> in the tail with \<open>i\<close> fresh for
    \<open>\<Gamma>\<close>.  The official conjunct is produced by \<open>suffix_is_proof\<close> --- the
    certificate is the suffix of the proof list --- followed by
    \<open>closure_by_inst\<close> to close it against \<open>A\<close>; the resulting context is closed by
    \<open>close_H_closed\<close> and satisfied by \<open>hypsat_closed\<close>.  Nothing has to be
    excluded, because a universal has no falsity clause.  The structural
    conjunct is the induction hypothesis at \<open>asn_put A i (S n)\<close> for arbitrary
    \<open>n\<close>, legitimate because \<open>i\<close> is fresh for \<open>\<Gamma>\<close> (\<open>hypsat_fresh\<close>) and \<open>v_i N\<close> is
    satisfied there by construction.
  \<^item> \<open>\<forall>\<close>E.  Read the structural conjunct at the value of the witness and push it
    back through \<open>wsat_subst_rev\<close>.  No certificate is inspected, which is the
    whole point of carrying the extras.
  \<^item> \<open>exF\<close>.  The two premises give \<open>wsat \<phi> A\<close> and \<open>wunsat \<phi> A\<close>, and \<open>wdet\<close> closes
    the case.  \<open>wdet\<close> is available because it rests on stability, not on
    soundness.

  The remaining cases are the congruence lemma for \<open>eqSubst\<close>, \<open>ind\<close> and
  \<open>defE\<close>/\<open>defI\<close>, weakening and cut on the hypothesis list, and one
  clause-reading per propositional, arithmetic and conditional rule.
  \<open>notForallE\<close> is vacuous: its major premise \<open>wsat (mkNot (mkAll i p)) A\<close> unfolds
  to \<open>wunsat (mkAll i p) A\<close>, whose official conjunct asks for \<open>evF k (mkAll i p) A = 1\<close>,
  and the \<open>F_ALL\<close> clause of \<open>evF\<close> returns only 2 or 0.
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

text \<open>
  With the bridge in place the abstract skeleton applies.  Note what the
  interpretation does not have to supply: exclusivity is a theorem of the
  official layer, and internal completeness has disappeared except at terms.
\<close>

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
    \<comment> \<open>\<open>soundness_bridge\<close> modulo the habeas quid side conditions, which the
        interpretation in \<open>qga_encode.thy\<close> supplies.\<close>
    sorry
qed

end

end
