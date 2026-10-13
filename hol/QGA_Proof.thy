section "The QGA proof system: GD.thy's axioms, one for one"

theory QGA_Proof
  imports QGA_Syntax
begin

text \<open>
  \<^bold>\<open>Fidelity.\<close>  Every rule below is an axiom of \<^file>\<open>../pure/GD.thy\<close>, carries its
  name, and quotes its statement verbatim.  Every object-logic axiom of
  \<open>GD.thy\<close> appears.  What does not appear, and why:

  \<^item> \<open>eq_reflection\<close> and \<open>iff_reflection\<close> conclude in \<open>prop\<close>, not in \<open>o\<close>.  They are
    statements about Isabelle/Pure and have no counterpart in a first-order
    presentation.  \<open>eq_reflection\<close> is conservative here --- composed with Pure's
    equality rules its only object-level effect is replacement of equals in an
    arbitrary context, which is \<open>eqSubst\<close>.  \<open>iff_reflection\<close> is NOT: it is the
    only route in \<open>GD.thy\<close> from \<open>p \<longleftrightarrow> q\<close> to substitutivity of \<open>\<longleftrightarrow>\<close>, so this
    presentation is weaker than \<open>GD.thy\<close> at exactly that point.  If that matters
    it should be added as \<open>iffSubst\<close> rather than left implicit.

  \<^bold>\<open>The structural rules, and what they cost.\<close>  \<open>GD.thy\<close> states none, because
  Pure supplies them --- and in a SHALLOW embedding (\<open>QGA_Model.thy\<close>) none are
  needed either, since HOL has the same Pure connectives and hypotheses stay
  Pure's.  They appear here only because \<open>derives\<close> replaces Pure's context
  management with an explicit \<open>fm fset\<close>, which a deep embedding must do in
  order that provability be a predicate HOL can quantify over --- and that is
  the only reason to pay for a deep embedding at all.  They are therefore NOT
  GD.thy axioms but an arithmetization of what Pure does, and they carry an
  adequacy obligation: that \<open>derives\<close> proves exactly what GD.thy-in-Pure
  proves.  Each comes from a specific kernel operation:
  \<open>pr_hyp\<close> from \<open>Thm.assume\<close>; \<open>pr_weak\<close> from the fact that Pure carries
  hypotheses as a set that is only ever enlarged (so contraction and exchange
  are invisible); \<open>pr_cut\<close> from \<open>implies_intr\<close> followed by \<open>implies_elim\<close>;
  \<open>pr_inst\<close> from \<open>Thm.instantiate\<close>, equivalently \<open>\<And>\<close> introduction followed by
  \<open>\<And>\<close> elimination.  Pure's \<open>\<Longrightarrow>\<close> and \<open>\<And>\<close> in PREMISE position are not rules but
  rule shapes: a premise \<open>P \<Longrightarrow> R\<close> becomes the judgment \<open>P, \<Gamma> \<turnstile> R\<close>, and a premise
  \<open>\<And>x. x N \<Longrightarrow> Q x\<close> becomes \<open>v\<^sub>0 N, \<Up>\<Gamma> \<turnstile> Q\<close> --- with the context LIFTED, which is
  the de Bruijn form of the eigenvariable condition and needs no freshness
  side condition.

  \<^bold>\<open>Two places where a context is a hole, not a binder.\<close>  \<open>eqSubst\<close>, \<open>ind\<close>, the
  lazy conditional quartet and \<open>defE\<close>/\<open>defI\<close> quantify over an arbitrary context
  \<open>Q\<close>.  A context is a formula with a distinguished free variable, filled by
  \<open>psub_fm\<close> (no index shifting).  The quantifier rules instead instantiate a
  binder, which is \<open>subst_fm\<close> (with shifting).  Conflating the two is a classic
  bug; they are separate operations in \<open>QGA_Syntax.thy\<close>.

  \<^bold>\<open>One discovered fact about GD.thy, recorded here.\<close>  The fourteen conditional
  axioms sit in a single \<open>axiomatization where\<close> block that declares no constant
  of its own, so Isabelle pins the block's type variable, and \<open>condI1\<close> pins it
  to \<open>num\<close>.  The lazy quartet \<open>cond_thenQ_E\<close>, \<open>cond_thenQ_I\<close>, \<open>cond_elseQ_E\<close>,
  \<open>cond_elseQ_I\<close> is therefore available in \<open>GD.thy\<close> at TERM-valued conditionals
  only --- Isabelle reports their context type as \<open>num \<Rightarrow> o\<close>.  They are encoded
  here at that arity, and not at the formula-valued one.

  \<^bold>\<open>Call by name.\<close>  \<open>GD.thy\<close>'s \<open>:=\<close> is Isabelle substitution, so unfolding a
  definition carries no habeas quid premise, and \<open>pr_defE\<close>/\<open>pr_defI\<close> have none.
  The semantics must therefore be call-by-name at application, as RGA's is;
  a call-by-value evaluator would force premises \<open>x N\<close>, \<open>y N\<close> that \<open>GD.thy\<close> does
  not have.
\<close>

locale qga_proof =
  fixes D :: dfns   \<comment> \<open>the definition list; nothing is assumed of it\<close>
begin

inductive derives :: "fm fset \<Rightarrow> fm \<Rightarrow> bool"  (infix "\<turnstile>" 15) where

  \<comment> \<open>structural, from Pure\<close>
    pr_hyp:    "c |\<in>| \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> c"
  | pr_weak:   "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> |\<subseteq>| \<Delta> \<Longrightarrow> \<Delta> \<turnstile> c"
  | pr_cut:    "\<Gamma> \<turnstile> a \<Longrightarrow> finsert a \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c"
  | pr_inst:   "\<Gamma> \<turnstile> c \<Longrightarrow> fimage (psub_fm i s) \<Gamma> \<turnstile> psub_fm i s c"

  \<comment> \<open>\<open>disjI1: P \<Longrightarrow> P \<or> Q\<close>\<close>
  | pr_disjI1: "\<Gamma> \<turnstile> p \<Longrightarrow> \<Gamma> \<turnstile> p \<^bold>\<or> q"
  \<comment> \<open>\<open>disjI2: Q \<Longrightarrow> P \<or> Q\<close>\<close>
  | pr_disjI2: "\<Gamma> \<turnstile> q \<Longrightarrow> \<Gamma> \<turnstile> p \<^bold>\<or> q"
  \<comment> \<open>\<open>disjI3: \<lbrakk>\<not>P; \<not>Q\<rbrakk> \<Longrightarrow> \<not>(P \<or> Q)\<close>\<close>
  | pr_disjI3: "\<Gamma> \<turnstile> \<^bold>\<not>p \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>\<not>q \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>\<not>(p \<^bold>\<or> q)"
  \<comment> \<open>\<open>disjE1: \<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close>\<close>
  | pr_disjE1: "\<Gamma> \<turnstile> p \<^bold>\<or> q \<Longrightarrow> finsert p \<Gamma> \<turnstile> r \<Longrightarrow> finsert q \<Gamma> \<turnstile> r \<Longrightarrow> \<Gamma> \<turnstile> r"
  \<comment> \<open>\<open>disjE2: \<not>(P \<or> Q) \<Longrightarrow> \<not>P\<close>\<close>
  | pr_disjE2: "\<Gamma> \<turnstile> \<^bold>\<not>(p \<^bold>\<or> q) \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>\<not>p"
  \<comment> \<open>\<open>disjE3: \<not>(P \<or> Q) \<Longrightarrow> \<not>Q\<close>\<close>
  | pr_disjE3: "\<Gamma> \<turnstile> \<^bold>\<not>(p \<^bold>\<or> q) \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>\<not>q"
  \<comment> \<open>\<open>dNegI: P \<Longrightarrow> \<not>\<not>P\<close>\<close>
  | pr_dNegI:  "\<Gamma> \<turnstile> p \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>\<not>\<^bold>\<not>p"
  \<comment> \<open>\<open>dNegE: \<not>\<not>P \<Longrightarrow> P\<close>\<close>
  | pr_dNegE:  "\<Gamma> \<turnstile> \<^bold>\<not>\<^bold>\<not>p \<Longrightarrow> \<Gamma> \<turnstile> p"
  \<comment> \<open>\<open>exF: \<lbrakk>P; \<not>P\<rbrakk> \<Longrightarrow> Q\<close>\<close>
  | pr_exF:    "\<Gamma> \<turnstile> p \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>\<not>p \<Longrightarrow> \<Gamma> \<turnstile> q"

  \<comment> \<open>\<open>eqSubst: \<lbrakk>a = b; Q a\<rbrakk> \<Longrightarrow> Q b\<close>\<close>
  | pr_eqSubst: "\<Gamma> \<turnstile> a \<^bold>= b \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>a]p \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>b]p"
  \<comment> \<open>\<open>eqSym: a = b \<Longrightarrow> b = a\<close>\<close>
  | pr_eqSym:   "\<Gamma> \<turnstile> a \<^bold>= b \<Longrightarrow> \<Gamma> \<turnstile> b \<^bold>= a"

  \<comment> \<open>\<open>nat0: zero N\<close>\<close>
  | pr_nat0:       "\<Gamma> \<turnstile> \<^bold>0 \<^bold>N"
  \<comment> \<open>\<open>sucInj: S a = S b \<Longrightarrow> a = b\<close>\<close>
  | pr_sucInj:     "\<Gamma> \<turnstile> \<^bold>S a \<^bold>= \<^bold>S b \<Longrightarrow> \<Gamma> \<turnstile> a \<^bold>= b"
  \<comment> \<open>\<open>sucCong: a = b \<Longrightarrow> S a = S b\<close>\<close>
  | pr_sucCong:    "\<Gamma> \<turnstile> a \<^bold>= b \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>S a \<^bold>= \<^bold>S b"
  \<comment> \<open>\<open>predCong: a = b \<Longrightarrow> P a = P b\<close>\<close>
  | pr_predCong:   "\<Gamma> \<turnstile> a \<^bold>= b \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>P a \<^bold>= \<^bold>P b"
  \<comment> \<open>\<open>eqBool: \<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> (a = b) B\<close>\<close>
  | pr_eqBool:     "\<Gamma> \<turnstile> a \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> b \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> (a \<^bold>= b) \<^bold>B"
  \<comment> \<open>\<open>sucNonZero: a N \<Longrightarrow> S a \<noteq> zero\<close>\<close>
  | pr_sucNonZero: "\<Gamma> \<turnstile> a \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>S a \<^bold>\<noteq> \<^bold>0"
  \<comment> \<open>\<open>predSucInv: a N \<Longrightarrow> P(S(a)) = a\<close>\<close>
  | pr_predSucInv: "\<Gamma> \<turnstile> a \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>P \<^bold>S a \<^bold>= a"
  \<comment> \<open>\<open>pred0: P(zero) = zero\<close>\<close>
  | pr_pred0:      "\<Gamma> \<turnstile> \<^bold>P \<^bold>0 \<^bold>= \<^bold>0"
  \<comment> \<open>\<open>eqE: ((a = b) B) \<Longrightarrow> ((a N) \<and> (b N))\<close>\<close>
  | pr_eqE:        "\<Gamma> \<turnstile> (a \<^bold>= b) \<^bold>B \<Longrightarrow> \<Gamma> \<turnstile> (a \<^bold>N) \<^bold>\<and> (b \<^bold>N)"
  \<comment> \<open>\<open>predTIE: (P a N) \<Longrightarrow> (a N)\<close>\<close>
  | pr_predTIE:    "\<Gamma> \<turnstile> (\<^bold>P a) \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> a \<^bold>N"
  \<comment> \<open>\<open>ind: \<lbrakk>a N; Q zero; \<And>x. x N \<Longrightarrow> Q x \<Longrightarrow> Q S(x)\<rbrakk> \<Longrightarrow> Q a\<close>.  The motive is a hole
        context; the eigenvariable is a free index \<open>i\<close> not occurring in \<open>\<Gamma>\<close>.\<close>
  | pr_ind:        "\<Gamma> \<turnstile> a \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>\<^bold>0]p
                     \<Longrightarrow> finsert (\<^bold>vi \<^bold>N) (finsert p \<Gamma>) \<turnstile> [i\<mapsto>\<^bold>S (\<^bold>vi)]p
                     \<Longrightarrow> \<not> freein i \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>a]p"

  \<comment> \<open>\<open>forallI: \<lbrakk>\<And>x. x N \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> \<forall>x. Q x\<close>.  The lifted context makes \<open>v\<^sub>0\<close> fresh.\<close>
  | pr_forallI:    "finsert (\<^bold>v0 \<^bold>N) (\<Up>\<Gamma>) \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> fmAll b"
  \<comment> \<open>\<open>forallE: \<lbrakk>\<forall>c'. Q c'; a N\<rbrakk> \<Longrightarrow> Q a\<close>\<close>
  | pr_forallE:    "\<Gamma> \<turnstile> fmAll b \<Longrightarrow> \<Gamma> \<turnstile> a \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> subst_fm 0 a b"
  \<comment> \<open>\<open>existsI: \<lbrakk>a N; Q a\<rbrakk> \<Longrightarrow> \<exists>x. Q x\<close>\<close>
  | pr_existsI:    "\<Gamma> \<turnstile> a \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> subst_fm 0 a b \<Longrightarrow> \<Gamma> \<turnstile> fmEx b"
  \<comment> \<open>\<open>existsE: \<lbrakk>\<exists>i. Q i; \<And>a. a N \<Longrightarrow> Q a \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close>\<close>
  | pr_existsE:    "\<Gamma> \<turnstile> fmEx b \<Longrightarrow> finsert (\<^bold>v0 \<^bold>N) (finsert b (\<Up>\<Gamma>)) \<turnstile> \<upharpoonleft>c \<Longrightarrow> \<Gamma> \<turnstile> c"
  \<comment> \<open>\<open>notForallI: \<lbrakk>a N; \<not>(F a)\<rbrakk> \<Longrightarrow> \<not>(\<forall>x. F x)\<close>\<close>
  | pr_notForallI: "\<Gamma> \<turnstile> a \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>\<not>(subst_fm 0 a b) \<Longrightarrow> \<Gamma> \<turnstile> \<^bold>\<not>(fmAll b)"
  \<comment> \<open>\<open>notForallE: \<lbrakk>\<not>(\<forall>x. F x); \<And>a. a N \<Longrightarrow> \<not>(F a) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close>\<close>
  | pr_notForallE: "\<Gamma> \<turnstile> \<^bold>\<not>(fmAll b)
                     \<Longrightarrow> finsert (\<^bold>v0 \<^bold>N) (finsert (\<^bold>\<not>b) (\<Up>\<Gamma>)) \<turnstile> \<upharpoonleft>c \<Longrightarrow> \<Gamma> \<turnstile> c"

  \<comment> \<open>\<open>condI1: \<lbrakk>c; a N\<rbrakk> \<Longrightarrow> (if c then a else b) = a\<close>\<close>
  | pr_condI1:  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> a \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> tmCond c a b \<^bold>= a"
  \<comment> \<open>\<open>condI2: \<lbrakk>\<not>c; b N\<rbrakk> \<Longrightarrow> (if c then a else b) = b\<close>\<close>
  | pr_condI2:  "\<Gamma> \<turnstile> \<^bold>\<not>c \<Longrightarrow> \<Gamma> \<turnstile> b \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> tmCond c a b \<^bold>= b"
  \<comment> \<open>\<open>condI1B: \<lbrakk>c; d B\<rbrakk> \<Longrightarrow> (if c then d else e) \<longleftrightarrow> d\<close>\<close>
  | pr_condI1B: "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> d \<^bold>B \<Longrightarrow> \<Gamma> \<turnstile> fmCond c d e \<^bold>\<longleftrightarrow> d"
  \<comment> \<open>\<open>condI2B: \<lbrakk>\<not>c; e B\<rbrakk> \<Longrightarrow> (if c then d else e) \<longleftrightarrow> e\<close>\<close>
  | pr_condI2B: "\<Gamma> \<turnstile> \<^bold>\<not>c \<Longrightarrow> \<Gamma> \<turnstile> e \<^bold>B \<Longrightarrow> \<Gamma> \<turnstile> fmCond c d e \<^bold>\<longleftrightarrow> e"
  \<comment> \<open>\<open>condE1: \<lbrakk>c; (if c then a else b) N\<rbrakk> \<Longrightarrow> (a N)\<close>\<close>
  | pr_condE1:  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> (tmCond c a b) \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> a \<^bold>N"
  \<comment> \<open>\<open>condE2: \<lbrakk>\<not>c; (if c then a else b) N\<rbrakk> \<Longrightarrow> (b N)\<close>\<close>
  | pr_condE2:  "\<Gamma> \<turnstile> \<^bold>\<not>c \<Longrightarrow> \<Gamma> \<turnstile> (tmCond c a b) \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> b \<^bold>N"
  \<comment> \<open>\<open>condE3: \<lbrakk>(if c then a else b) N\<rbrakk> \<Longrightarrow> (c B)\<close>\<close>
  | pr_condE3:  "\<Gamma> \<turnstile> (tmCond c a b) \<^bold>N \<Longrightarrow> \<Gamma> \<turnstile> c \<^bold>B"
  \<comment> \<open>\<open>condE1B: \<lbrakk>c; (if c then d else e) B\<rbrakk> \<Longrightarrow> (d B)\<close>\<close>
  | pr_condE1B: "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> (fmCond c d e) \<^bold>B \<Longrightarrow> \<Gamma> \<turnstile> d \<^bold>B"
  \<comment> \<open>\<open>condE2B: \<lbrakk>\<not>c; (if c then d else e) B\<rbrakk> \<Longrightarrow> (e B)\<close>\<close>
  | pr_condE2B: "\<Gamma> \<turnstile> \<^bold>\<not>c \<Longrightarrow> \<Gamma> \<turnstile> (fmCond c d e) \<^bold>B \<Longrightarrow> \<Gamma> \<turnstile> e \<^bold>B"
  \<comment> \<open>\<open>condE3B: \<lbrakk>(if c then d else e) B\<rbrakk> \<Longrightarrow> (c B)\<close>\<close>
  | pr_condE3B: "\<Gamma> \<turnstile> (fmCond c d e) \<^bold>B \<Longrightarrow> \<Gamma> \<turnstile> c \<^bold>B"
  \<comment> \<open>\<open>cond_thenQ_E: c \<Longrightarrow> Q (if c then a else b) \<Longrightarrow> Q a\<close>\<close>
  | pr_cond_thenQ_E: "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>tmCond c a b]p \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>a]p"
  \<comment> \<open>\<open>cond_thenQ_I: c \<Longrightarrow> Q a \<Longrightarrow> Q (if c then a else b)\<close>\<close>
  | pr_cond_thenQ_I: "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>a]p \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>tmCond c a b]p"
  \<comment> \<open>\<open>cond_elseQ_E: \<not>c \<Longrightarrow> Q (if c then a else b) \<Longrightarrow> Q b\<close>\<close>
  | pr_cond_elseQ_E: "\<Gamma> \<turnstile> \<^bold>\<not>c \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>tmCond c a b]p \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>b]p"
  \<comment> \<open>\<open>cond_elseQ_I: \<not>c \<Longrightarrow> Q b \<Longrightarrow> Q (if c then a else b)\<close>\<close>
  | pr_cond_elseQ_I: "\<Gamma> \<turnstile> \<^bold>\<not>c \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>b]p \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>tmCond c a b]p"

  \<comment> \<open>\<open>defE: \<lbrakk>a := b; Q b\<rbrakk> \<Longrightarrow> Q a\<close>, at the definition list --- the only \<open>:=\<close> facts
        the system has.  No habeas quid premise, matching \<open>GD.thy\<close>.\<close>
  | pr_defE: "\<Gamma> \<turnstile> [i\<mapsto>dfn_body D d x y]p \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>tmApp2 d x y]p"
  \<comment> \<open>\<open>defI: \<lbrakk>a := b; Q a\<rbrakk> \<Longrightarrow> Q b\<close>\<close>
  | pr_defI: "\<Gamma> \<turnstile> [i\<mapsto>tmApp2 d x y]p \<Longrightarrow> \<Gamma> \<turnstile> [i\<mapsto>dfn_body D d x y]p"


subsection "The consistency statements to aim at"

text \<open>\<open>BGA\<close> has no primitive negation, so \<open>CONSISTENCY.md\<close> \<S>2.2 phrases syntactic
      consistency through the equals/unequals pair.  QGA has \<open>not\<close>, so the
      ordinary statement is available and is strictly stronger; both are
      recorded, and the second is what \<open>QGA_Sound.thy\<close> will discharge.\<close>

definition consistent_eq :: "fm fset \<Rightarrow> bool" where
  "consistent_eq \<Gamma> \<equiv> \<nexists>a b. (\<Gamma> \<turnstile> a \<^bold>= b) \<and> (\<Gamma> \<turnstile> a \<^bold>\<noteq> b)"

definition consistent :: "fm fset \<Rightarrow> bool" where
  "consistent \<Gamma> \<equiv> \<nexists>c. (\<Gamma> \<turnstile> c) \<and> (\<Gamma> \<turnstile> \<^bold>\<not>c)"

lemma consistent_imp_consistent_eq: "consistent \<Gamma> \<Longrightarrow> consistent_eq \<Gamma>"
  by (auto simp: consistent_def consistent_eq_def)

text \<open>Consistency also rules out \<open>False\<close>, since \<open>exF\<close> makes the two equivalent.\<close>

lemma consistent_imp_not_false: "consistent \<Gamma> \<Longrightarrow> \<not> (\<Gamma> \<turnstile> \<^bold>\<bottom>)"
proof
  assume c: "consistent \<Gamma>" and f: "\<Gamma> \<turnstile> \<^bold>\<bottom>"
  have "\<Gamma> \<turnstile> \<^bold>0 \<^bold>N" by (rule pr_nat0)
  hence "\<Gamma> \<turnstile> \<^bold>S \<^bold>0 \<^bold>\<noteq> \<^bold>0" by (rule pr_sucNonZero)
  with f c show False by (auto simp: consistent_def)
qed

end

end
