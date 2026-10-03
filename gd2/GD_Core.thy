theory GD_Core
  imports Pure
  keywords "gd_def" "gd_decl" "gd_fuel" "gd_approx" :: thy_decl
    and "print_gd_defs" :: diag
begin

text \<open>
  GD_Core: the trusted kernel of the second-generation GD development.

  Everything outside this file is either a Pure definition (which is conservative) or a
  lemma proved from the axioms below.  The one exception is the gd_def command,
   which adds one axiom per recursive definition; 
  its admissibility conditions are stated in the last section and are part of the kernel.

  Differences from pure/GD.thy
  ----------------------------
  1. One universe.  The types o and num are merged into a single type tm.
     Formulas are terms; truth values are the numerals 1 (true) and 0 (false),
     as in PGA/RGA.  One set of conditional rules replaces the o/num pairs.
  2. Functions are object values.  lam and app are object constants and
     Pure's function type is used only for binding (HOAS).  Pure-level
     constants of type tm => ... => tm (e.g. from gd_def) are fixed-arity
     symbols, like BGA's defined symbols d_i, not a function space.
  3. Replacement principles are meta-equalities.  eq_reflection, beta, the
     conditional rules and recursive definitions are all stated with ==, so
     Pure rewriting (unfold, simp) applies them in any context.  Each needs the
     model lemma listed under "Proof obligations".
  4. Removed from the axiom list because they are derivable: eqSubst, eqSym,
     sucCong, predCong, natP, iff_reflection, the o-typed conditional rules,
     and the existential quantifier (a Pure definition, not a primitive).
  5. Added: truth values are numerals (trueI/trueE/falseI/falseE), needed
     once formulas are terms; ATI from OGA; prop-level motives in ind,
     disjE1, notForallE and exF.

  Intended model (not yet formalized; for a later HOL development)
  -----------------------------------------------------------------------
  M1  Terms.  Pure terms of type tm correspond to closed-or-open object terms
      (de Bruijn syntax), variables of type tm => tm to object terms with one
      hole.  This is the standard LF adequacy argument; it goes through because
      Pure has no case analysis or equality test on tm.
  M2  Evaluation.  A relation  t \<Down> v  on closed terms, v a numeral or a
      head-normal lam.  Call-by-name.  Clauses:
        \<bottom> has no value;
        0, S, P (P 0 = 0), strict in their argument;
        a = b    : 1 if a, b evaluate to the same numeral, 0 if to different
                   numerals, no value otherwise (in particular for lam);
        \<not> a      : flips 0/1, no value otherwise;
        a \<or> b    : Kleene-strong (1 if either is 1, 0 if both are 0);
        if c then a else b : a's value if c is 1, b's if c is 0, lazy in a, b;
        f \<cdot> a    : head-evaluate f to lam F, then evaluate F a (a unevaluated);
        c x1..xn : unfold the body of c from the definition environment;
        \<forall>x. Q x  : 1 if Q n is 1 for every numeral n, 0 if Q n is 0 for some n.
      The \<forall> clause is the omega-semantics of OGA's soundness proof: not
      effective, but only soundness is at stake here.  Evaluation is the least
      fixed point of a monotone operator with infinitary premises.
  M3  Truth.  A closed formula p is true iff p \<Down> 1, false iff p \<Down> 0.
  M4  Judgments.  A Pure proposition is read classically under a closing
      substitution s (object variables to arbitrary closed terms, including
      divergent ones and lam terms):
        Trueprop t : s(t) is true
        A ==> B    : [A]s implies [B]s
        !!x. A     : [A]s[x:=t] for every closed t
        a == b     : s(a) ~ s(b), where ~ is closed-instance (CIU) equivalence
      A theorem is valid iff it holds under every s.

  Proof obligations for the model (the soundness proof proper)
  -------------------------------------------------------------
  O1 (determinism)  No closed term evaluates to two values.  Needed by exF.
  O2 (congruence)   ~ is a congruence, including under lam and \<forall>
                    (a CIU theorem, e.g. by Howe's method, for call-by-name
                    with parallel-or and the omega-quantifier).  Needed for
                    Pure's combination and abstraction rules on ==.
  O3 (evaluation)   If t \<Down> v then t ~ v.  Needed by eq_reflection.
  O4 (head steps)   Beta, taking a branch of a decided conditional, and
                    unfolding a definition are contained in ~.  Needed by beta,
                    condT, condF and gd_def.
  O5 (unwinding)    For a finitary block (A5 below): if f a evaluates to v,
                    then f_fuel k a evaluates to v for some numeral k.  The
                    part of the derivation contributed by the bodies is
                    finite (no omega clause, no function values), so it
                    unfolds the block's constants only finitely often.
                    Needed by the approx axioms.
  Everything else is a direct check against the clauses of M2/M3; each axiom
  below carries a one-line justification.

\<close>


section \<open>Universe and judgment\<close>

typedecl tm

judgment
  Trueprop :: \<open>tm \<Rightarrow> prop\<close>  (\<open>_\<close> 5)


section \<open>Term formers\<close>

axiomatization
  bot   :: \<open>tm\<close>                         (\<open>\<bottom>\<close>) and
  zero  :: \<open>tm\<close>                         (\<open>0\<close>) and
  suc   :: \<open>tm \<Rightarrow> tm\<close>                  (\<open>S(_)\<close> [800]) and
  pred  :: \<open>tm \<Rightarrow> tm\<close>                  (\<open>P(_)\<close> [800]) and
  eq    :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>            (infixl \<open>=\<close> 45) and
  not   :: \<open>tm \<Rightarrow> tm\<close>                  (\<open>\<not> _\<close> [40] 40) and
  disj  :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>            (infixr \<open>\<or>\<close> 30) and
  cond  :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm\<close>      (\<open>if _ then _ else _\<close> [25, 24, 24] 24) and
  lam   :: \<open>(tm \<Rightarrow> tm) \<Rightarrow> tm\<close> and
  app   :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>            (infixl \<open>\<cdot>\<close> 900) and
  All   :: \<open>(tm \<Rightarrow> tm) \<Rightarrow> tm\<close>           (binder \<open>\<forall>\<close> [8] 9)

text \<open>
  Object lambda.
\<close>

syntax
  "_lam" :: \<open>idt \<Rightarrow> tm \<Rightarrow> tm\<close>  (\<open>(3\<Lambda> _./ _)\<close> [0, 10] 10)
translations
  "\<Lambda> x. b" \<rightleftharpoons> "CONST lam (\<lambda>x. b)"

abbreviation one :: \<open>tm\<close>  (\<open>1\<close>)
  where \<open>1 \<equiv> S 0\<close>

text \<open>The two dynamic type checks.  Pure definitions, hence conservative.\<close>

definition isNat :: \<open>tm \<Rightarrow> tm\<close>  (\<open>_ N\<close> [21] 20)
  where \<open>x N \<equiv> x = x\<close>

definition isBool :: \<open>tm \<Rightarrow> tm\<close>  (\<open>_ B\<close> [21] 20)
  where \<open>p B \<equiv> p \<or> \<not> p\<close>


section \<open>Propositional core\<close>

text \<open>
  Kleene-strong disjunction and flipping negation (M2).  Elimination rules take
  a Pure-level conclusion R: sound because M4 reads judgments classically.
\<close>

axiomatization where
  disjI1: \<open>p \<Longrightarrow> p \<or> q\<close> and                                (* p is 1, so p \<or> q is 1 *)
  disjI2: \<open>q \<Longrightarrow> p \<or> q\<close> and                                (* symmetric *)
  disjI3: \<open>\<lbrakk>\<not> p; \<not> q\<rbrakk> \<Longrightarrow> \<not> (p \<or> q)\<close> and                  (* both 0, so 0 *)
  disjE1: \<open>\<lbrakk>p \<or> q; p \<Longrightarrow> PROP R; q \<Longrightarrow> PROP R\<rbrakk> \<Longrightarrow> PROP R\<close> and
                                                  (* value 1 needs a disjunct 1 *)
  disjE2: \<open>\<not> (p \<or> q) \<Longrightarrow> \<not> p\<close> and                          (* value 0 needs both 0 *)
  disjE3: \<open>\<not> (p \<or> q) \<Longrightarrow> \<not> q\<close> and
  dNegI:  \<open>p \<Longrightarrow> \<not> \<not> p\<close> and                                  (* flip twice *)
  dNegE:  \<open>\<not> \<not> p \<Longrightarrow> p\<close> and
  exF:    \<open>\<lbrakk>p; \<not> p\<rbrakk> \<Longrightarrow> PROP R\<close>                              (* O1: premises never both hold *)


section \<open>Truth values are numerals\<close>

text \<open>
  New relative to GD.thy: with formulas as terms, "p is true" and "p evaluates
  to 1" are the same statement (M3).  These are RGA's T= and F= rules.
\<close>

axiomatization where
  trueE:  \<open>p \<Longrightarrow> p = 1\<close> and
  trueI:  \<open>p = 1 \<Longrightarrow> p\<close> and
  falseE: \<open>\<not> p \<Longrightarrow> p = 0\<close> and
  falseI: \<open>p = 0 \<Longrightarrow> \<not> p\<close>


section \<open>Grounded equality\<close>

text \<open>
  eq_reflection is the only replacement rule for equality: substitution, symmetry
  and transitivity are derived (see the sanity section).  It is sound by O3:
  both sides evaluate to the same numeral, so both are ~ that numeral.
\<close>

axiomatization where
  eq_reflection: \<open>a = b \<Longrightarrow> a \<equiv> b\<close> and                        (* O3 *)
  eqBool:  \<open>\<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> (a = b) B\<close> and                    (* numerals compare to 0 or 1 *)
  neqE1:   \<open>\<not> (a = b) \<Longrightarrow> a N\<close> and                           (* value 0 needs two numerals *)
  neqE2:   \<open>\<not> (a = b) \<Longrightarrow> b N\<close>


section \<open>Natural numbers\<close>

text \<open>
  ind takes a Pure-level motive.  Sound because the meta-induction over
  numerals is carried out in the model and judgments are invariant under ~
  (O2, O3): if a evaluates to n, [Q a] and [Q n] agree.  This gives
  hypothetical motives (x-dependent assumptions) without needing a decided
  object implication.
\<close>

axiomatization where
  nat0:       \<open>0 N\<close> and
  natS:       \<open>a N \<Longrightarrow> S a N\<close> and
  sucInj:     \<open>S a = S b \<Longrightarrow> a = b\<close> and
  sucNonZero: \<open>a N \<Longrightarrow> \<not> (S a = 0)\<close> and
  pred0:      \<open>P 0 = 0\<close> and
  predSuc:    \<open>a N \<Longrightarrow> P (S a) = a\<close> and
  natPE:      \<open>P a N \<Longrightarrow> a N\<close> and                             (* P is strict *)
  botE:       \<open>\<bottom> N \<Longrightarrow> PROP R\<close> and                             (* \<bottom> has no value *)
  ind [case_names HQ Base Step]:
    \<open>\<lbrakk>a N; PROP Q 0; \<And>x. x N \<Longrightarrow> PROP Q x \<Longrightarrow> PROP Q (S x)\<rbrakk> \<Longrightarrow> PROP Q a\<close>


section \<open>Conditional evaluation\<close>

text \<open>
  One set of rules for every use of the conditional (numbers, formulas,
  functions), replacing GD.thy's condI/condE/condB/cond_thenQ families.  The
  branch not taken is never evaluated, so no N premise on a or b.
\<close>

axiomatization where
  condT: \<open>c \<Longrightarrow> (if c then a else b) \<equiv> a\<close> and                   (* O4 *)
  condF: \<open>\<not> c \<Longrightarrow> (if c then a else b) \<equiv> b\<close> and                 (* O4 *)
  condE: \<open>(if c then a else b) N \<Longrightarrow> c B\<close>                        (* strict in c *)


section \<open>Functions\<close>

text \<open>
  Call-by-name beta: the argument is substituted unevaluated, so no N premise.
  No eta rule: it is not needed, and whether it holds depends on how the
  model treats non-lam heads.
\<close>

axiomatization where
  beta: \<open>(\<Lambda> x. F x) \<cdot> a \<equiv> F a\<close>                                    (* O4 *)


section \<open>The universal quantifier\<close>

text \<open>
  GD.thy's quantifier rules, which are also RGA's AI/AE/notAI/notAE, checked
  against the omega clause of M2.  ATI is OGA's one extra rule.  The
  existential quantifier is defined in the base theory as \<not>(\<forall>x. \<not> Q x).
\<close>

axiomatization where
  forallI:    \<open>(\<And>x. x N \<Longrightarrow> Q x) \<Longrightarrow> \<forall>x. Q x\<close> and             (* every numeral instance is 1 *)
  forallE:    \<open>\<lbrakk>\<forall>x. Q x; a N\<rbrakk> \<Longrightarrow> Q a\<close> and                    (* a ~ its numeral, O3 *)
  notForallI: \<open>\<lbrakk>a N; \<not> Q a\<rbrakk> \<Longrightarrow> \<not> (\<forall>x. Q x)\<close> and              (* a 0 instance *)
  notForallE: \<open>\<lbrakk>\<not> (\<forall>x. Q x); \<And>a. a N \<Longrightarrow> \<not> Q a \<Longrightarrow> PROP R\<rbrakk> \<Longrightarrow> PROP R\<close> and
                                                  (* value 0 has a witness *)
  ATI:        \<open>(\<forall>x. (Q x) B) \<Longrightarrow> (\<forall>x. Q x) B\<close>                  (* all instances decided,
                                                     so all 1 or some 0 *)


section \<open>Recursive definitions (axiom schemes, enforced by gd_def)\<close>

text \<open>
  gd_def is part of the trusted base: it adds axioms.  For a block declaring
  constants f1 ... fm, gd_def emits the unfolding axioms (1).  The fuel
  versions and the least-fixed-point axioms (2) are opt-in, per block:
  gd_fuel f adds the fuel versions of f's block (ordinary definitions), and
  gd_approx f adds the approx axioms (and the fuel versions if missing).
  Keeping (2) opt-in means thm_deps shows exactly which results depend on
  it; where a termination measure is available, approx is derivable from the
  fuel equations by induction and the axiom is not needed at all.

  (1) Unfolding.  For each constant f of the block, one meta-equality

        f x1 ... xn \<equiv> body_f

      so definitions unfold anywhere with unfold/simp.  This says f is a
      fixed point of its body.

  (2) Least fixed point (gd_approx; only if A5 holds).  First the fuel
      versions of every constant of the block, by a syntactic rewrite
      (this part alone is gd_fuel):

        f_fuel k x1 ... xn \<equiv> if k = 0 then \<bottom> else body_f'

      where body_f' is body_f with every call  g t1 ... tj  to a constant g
      of the block replaced by  g_fuel (P k) t1 ... tj.  All constants of the
      block share the one fuel argument k.  These are ordinary gd_def
      equations of kind (1) (they satisfy A1-A4 by construction).  Then, for
      each f of the block, one axiom

        approx_f:  \<lbrakk>f a1 ... an N;
                    \<And>k. k N \<Longrightarrow> f_fuel k a1 ... an = f a1 ... an \<Longrightarrow> PROP R\<rbrakk>
                   \<Longrightarrow> PROP R

      i.e. if f a has a value, some finite fuel k computes the same value.
      This says f is the least fixed point: the one that actually runs.  It
      is what makes partial-correctness proofs possible (induction on k), and
      it is not derivable: reading  loop x \<equiv> loop x  as the constant-0
      function satisfies every other axiom but refutes  loop 0 N \<Longrightarrow> loop 0 = 5.

  Example.  From
        up x y \<equiv> if x = y then 0 else S (up (S x) y)
  gd_approx up generates
        up_fuel k x y \<equiv> if k = 0 then \<bottom>
                         else (if x = y then 0 else S (up_fuel (P k) (S x) y))
  and approx_up.

  Admissibility conditions (checked by gd_def; all are soundness-critical):

    A1  each constant is declared in this block (or declared earlier with no
        axioms, to allow forward references), with type tm \<Rightarrow> ... \<Rightarrow> tm;
    A2  the arguments x1 ... xn are pairwise distinct variables;
    A3  every free variable of a body is among its x1 ... xn;
    A4  exactly one equation per constant;
    A6  one definition per constant across theories: two theories that give
        the same constant different equations (possible after a shared
        gd_decl) cannot be imported together;
    A5  (approx only) every body of the block is finitary: built only from
        the variables x1 ... xn, the primitives 0 \<bottom> S P = \<not> \<or> if, the
        definitions N and B, constants of the block (fully applied), and
        constants of earlier blocks that were themselves finitary.  No \<Lambda>,
        \<cdot>, \<forall>, \<exists>, other Pure definitions, constants declared by gd_decl but
        not yet defined, or Pure-level abstraction.

  A1-A4 fail: the block is rejected.  A5 fails: the block is accepted, and
  gd_fuel works, but gd_approx refuses it.  A6 fails: the merge of the two
  theories is refused.  (A6 covers gd_def only; a plain axiomatization of a
  constant that gd_def also defines is outside what the registry can see.)

  Why A5.  Iterating from \<bottom> (f_fuel 0, f_fuel 1, ...) reaches the least fixed
  point after finitely many steps when every evaluation derivation is finite.
  The omega-quantifier breaks this: its clause has one premise per numeral,
  so a derivation can unfold f to unboundedly many depths across the
  instances.  Two counterexamples, both making approx inconsistent:

  (i) recursion directly under \<forall>:
        f x \<equiv> if x = 0 then (\<forall>n. f (S n) = 1)
              else if x = 1 then 1 else f (P x)
      f 0 = 1 is provable (f (S n) reaches f 1 after n steps), but every
      f_fuel k 0 runs out of fuel at the instance n := P k.

  (ii) recursion hidden behind helper definitions:
        roll v fn \<equiv> \<Lambda> n. if n = 0 then v else fn \<cdot> P n
        sweep v fn \<equiv> \<forall>n. fn \<cdot> n = v
        walk v \<equiv> roll v (walk v)       
        total v \<equiv> sweep v (walk v)
      No block constant is under a binder in the bodies.  Call-by-name
      passes the unevaluated call  walk v  into roll's \<Lambda>, and sweep's \<forall>
      applies that \<Lambda> to every n, unfolding walk n times.  total v is
      provable, every total_fuel k v fails at the instance n := P k, and
      approx then proves \<bottom> \<cdot> 0 = 0 and \<bottom> \<cdot> 0 = 1.

  (ii) shows that no check on where the block constants occur can work once
  function values and \<forall> are available: a call can be carried anywhere as
  data.  The finitary fragment rules out both, so derivations are finite
  (arguments are only used as first-order data, and their own evaluation is
  identical in f and f_fuel).  This is the standard setting of the unwinding
  argument.  Higher-order recursion gets unfolding equations but no approx;
  extending approx to it would need transfinite fuel or a different \<forall>.

  Model: unfolding equations are head steps (O4); approx is the unwinding
  property (O5).

  gd_decl f :: "tm \<Rightarrow> tm" declares f with no axioms, so that an earlier
  block can call it and a later gd_def can define it (A1).  Such a constant
  is not finitary while it is undefined, so a block calling it gets no approx
  axioms (A5), and neither does the block that later defines it in terms of
  the earlier one.

  A2 is missing from pure/gd_def.ML.  Without it the scheme is inconsistent:
      gd_def f :: "num \<Rightarrow> num" where "f (P x) := x"
  passes the current checks, and instantiating x with 0 and with S 0 gives
  f 0 := 0 and f 0 := S 0 (using P 0 = 0 and P (S 0) = 0), hence 0 = S 0.
\<close>

ML_file \<open>gd_def.ML\<close>

section \<open>Sanity checks\<close>

text \<open>
  Derivations of rules that GD.thy took as axioms.  They are here to confirm
  that dropping them lost nothing; the rest of the library belongs in the
  base theory.
\<close>

lemma eq_natL: \<open>a = b \<Longrightarrow> a N\<close>
proof -
  assume h: \<open>a = b\<close>
  show \<open>a N\<close>
    unfolding isNat_def using h unfolding eq_reflection[OF h] .
qed

lemma eqSym: \<open>a = b \<Longrightarrow> b = a\<close>
proof -
  assume h: \<open>a = b\<close>
  show \<open>b = a\<close>
    using h unfolding eq_reflection[OF h] .
qed

lemma eq_trans: \<open>\<lbrakk>a = b; b = c\<rbrakk> \<Longrightarrow> a = c\<close>
proof -
  assume h1: \<open>a = b\<close> and h2: \<open>b = c\<close>
  show \<open>a = c\<close>
    using h1 unfolding eq_reflection[OF h2] .
qed

lemma eqSubst: \<open>\<lbrakk>a = b; PROP Q a\<rbrakk> \<Longrightarrow> PROP Q b\<close>
proof -
  assume h: \<open>a = b\<close> and q: \<open>PROP Q a\<close>
  show \<open>PROP Q b\<close>
    using q unfolding eq_reflection[OF h] .
qed

lemma eq_natR: \<open>a = b \<Longrightarrow> b N\<close>
  by (rule eq_natL, rule eqSym)

lemma natSE: \<open>S a N \<Longrightarrow> a N\<close>
proof -
  assume h: \<open>S a N\<close>
  show \<open>a N\<close>
    unfolding isNat_def by (rule sucInj, fold isNat_def, rule h)
qed

end
