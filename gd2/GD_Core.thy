theory GD_Core
  imports Pure
  keywords "gd_def" "gd_fuel" "gd_approx" :: thy_decl
    and "print_gd_defs" :: diag
begin

text \<open>
  GD_Core: the trusted kernel of the second-generation GD development.

  Everything outside this file is either a Pure definition (which is conservative) or a
  lemma proved from the axioms below.  Recursive definitions (gd_def, gd_fuel) are
  Pure definitions too: they are built from the fixed-point combinator fix, and
  their unfolding equations are proved.  

  The one command that adds axioms is
  gd_approx; its condition A5 is stated in the last section and is part of the
  kernel.THIS IS CURRENTLY EXPERIMENTAL

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
     once formulas are terms; prop-level motives in ind, disjE1, notForallE
     and exF.  OGA's extra rule ATI is not in the kernel: it is an opt-in
     axiom in GD_ATI.thy.

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
                    condT and condF (and so by fix and gd_def).
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
  disjI1: \<open>p \<Longrightarrow> p \<or> q\<close> and                                (* p is 1, so p \<or> q is 1*)
  disjI2: \<open>q \<Longrightarrow> p \<or> q\<close> and                                (* symmetric*)
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


section \<open>Fixed points\<close>

text \<open>
  The object language is untyped and beta is unrestricted, so self-application
  gives a fixed-point combinator as a Pure definition: with W = \<Lambda> x. F (x \<cdot> x),
  W \<cdot> W unfolds in one beta step to F (W \<cdot> W).  No rule is needed beyond beta.
  A term like W \<cdot> W for F = \<lambda>y. y has no value, and grounding is what makes
  that harmless: no rule concludes anything from a term that has no value.

  gd_def builds every recursive definition from fix (last section), so
  recursive definitions add no axioms.  In HOL and Lean the type system rules
  out x \<cdot> x, so a recursive definition goes through a package that first
  proves termination or monotonicity.
\<close>

definition "fix" :: \<open>(tm \<Rightarrow> tm) \<Rightarrow> tm\<close>
  where \<open>fix F \<equiv> (\<Lambda> x. F (x \<cdot> x)) \<cdot> (\<Lambda> x. F (x \<cdot> x))\<close>

lemma fix_unfold: \<open>fix F \<equiv> F (fix F)\<close>
  unfolding fix_def by (rule beta)


section \<open>The universal quantifier\<close>

text \<open>
  GD.thy's quantifier rules, which are also RGA's AI/AE/notAI/notAE, checked
  against the omega clause of M2.  OGA's extra rule ATI is sound for the same
  clause but is opt-in (GD_ATI.thy), so thm_deps shows which results use it.
  The existential quantifier is defined in the base theory as \<not>(\<forall>x. \<not> Q x).
\<close>

axiomatization where
  forallI:    \<open>(\<And>x. x N \<Longrightarrow> Q x) \<Longrightarrow> \<forall>x. Q x\<close> and             (* every numeral instance is 1 *)
  forallE:    \<open>\<lbrakk>\<forall>x. Q x; a N\<rbrakk> \<Longrightarrow> Q a\<close> and                    (* a ~ its numeral, O3 *)
  notForallI: \<open>\<lbrakk>a N; \<not> Q a\<rbrakk> \<Longrightarrow> \<not> (\<forall>x. Q x)\<close> and              (* a 0 instance *)
  notForallE: \<open>\<lbrakk>\<not> (\<forall>x. Q x); \<And>a. a N \<Longrightarrow> \<not> Q a \<Longrightarrow> PROP R\<rbrakk> \<Longrightarrow> PROP R\<close>
                                                  (* value 0 has a witness *)


section \<open>Recursive definitions\<close>

text \<open>
  gd_def is a definitional package.  For a block

      gd_def f1 :: ... and ... and fm :: ...
        where "f1 x1 ... xn \<equiv> body_1" and ... and "fm ... \<equiv> body_m"

  it makes one fixed point of an m-tuple (g a fresh variable):

      \<pi>j      =  \<Lambda> y1 ... ym. yj                     (Church tuple selector)
      Ci g    =  \<Lambda> x1 ... xn. body_i[fj := \<lambda>z1 ... zk. g \<cdot> \<pi>j \<cdot> z1 \<cdot> ... \<cdot> zk]
      F       =  \<lambda>g. \<Lambda> s. s \<cdot> C1 g \<cdot> ... \<cdot> Cm g
      fi      \<equiv>  \<lambda>x1 ... xn. fix F \<cdot> \<pi>i \<cdot> x1 \<cdot> ... \<cdot> xn      (Pure definition, fi_raw_def)

Here's an example with m=1 and f1=fact:

fact n = if n = 0 then 1 else n * fact(P n)

\<pi>1 = \<Lambda> y1. y1
C1 g = \<Lambda>n. if n=0 then 1 else n* (g \<cdot> \<pi>1 \<cdot> (P n))
F = \<lambda>g. \<Lambda>s. s\<cdot>(C1 g)
G = fix F

fact_raw_def:  fact \<equiv> \<lambda>z. fix F \<sqdot> \<pi>1 \<sqdot> z

prove that fact n \<equiv> body

fact n \<equiv> (\<lambda>z. G\<sqdot>\<pi>1\<sqdot>z) n (fact_raw_def)
\<equiv> G \<sqdot> \<pi>1 \<sqdot> n (pure beta rule)
\<equiv> (\<Lambda>s. s \<sqdot> C1 G) \<sqdot> \<pi>1 \<sqdot> n (fix unfold)
\<equiv> \<pi>1 \<sqdot> (C1 G) \<sqdot> n (object beta rule)
\<equiv> C1 G \<sqdot> n (object beta)
\<equiv> if n = 0 then 1 else n * ((\<lambda>z. G\<sqdot>\<pi>1\<sqdot>z) (P n))
\<equiv> if n = 0 then 1 else n * (G \<sqdot> \<pi>1 \<sqdot> (P n))


  and proves the unfolding equation  fi x1 ... xn \<equiv> body_i  (fi_def) by one
  fix_unfold and 1 + m + n beta steps at the head.  Mutual recursion is the
  same construction with m > 1.

  So unfolding equations are theorems, and their soundness is that of beta
  (O4).  Pure's definitional mechanism checks that each constant is defined
  once and that definitions are acyclic.  The consequences:

    - The old condition A6 (no conflicting definitions across merged
      theories) is enforced by Pure.
    - There is no forward declaration (the former gd_decl): defining g in
      terms of a declared f and later f in terms of g is a cyclic definition,
      which Pure rejects.  Mutually recursive constants go in one block.
    - The conditions below are what it takes to build the fixed point.  A
      violation gives a malformed definition, not an inconsistency; gd_def
      checks them to explain the rejection.

    A1  each constant is declared in this block, with type tm \<Rightarrow> ... \<Rightarrow> tm;
    A2  the arguments x1 ... xn are pairwise distinct variables;
    A3  every free variable of a body is among its x1 ... xn;
    A4  exactly one equation per constant.

  Fuel versions and approximation are opt-in, per block.

  (1) gd_fuel f defines, for each constant of f's block,

        f_fuel k x1 ... xn \<equiv> if k = 0 then \<bottom> else body_f'

      where body_f' is body_f with every call  g t1 ... tj  to a constant g
      of the block replaced by  g_fuel (P k) t1 ... tj.  All constants of the
      block share the one fuel argument k.  This is an ordinary gd_def block.

  (2) gd_approx f adds, for each f of the block (defining the fuel versions
      first if needed), one axiom

        approx_f:  \<lbrakk>f a1 ... an N;
                    \<And>k. k N \<Longrightarrow> f_fuel k a1 ... an = f a1 ... an \<Longrightarrow> PROP R\<rbrakk>
                   \<Longrightarrow> PROP R

      i.e. if f a has a value, some finite fuel k computes the same value.
      This says f is the least fixed point: the one that actually runs.  It
      is what makes partial-correctness proofs possible (induction on k).
      Where a termination measure is available it is derivable from the fuel
      equations by induction (see evn in GD_Def_Test), so keeping it opt-in
      means thm_deps shows exactly which results depend on it.  Whether it is
      derivable in general is open: the old argument that it is not (read
      loop x \<equiv> loop x as the constant-0 function) needed loop to be an
      uninterpreted constant, and loop is now a closed fix term.

  Example.  From
        up x y \<equiv> if x = y then 0 else S (up (S x) y)
  gd_approx up generates
        up_fuel k x y \<equiv> if k = 0 then \<bottom>
                         else (if x = y then 0 else S (up_fuel (P k) (S x) y))
  and approx_up.

    A5  (gd_approx only; soundness-critical) every body of the block is
        finitary: built only from the variables x1 ... xn, the primitives
        0 \<bottom> S P = \<not> \<or> if, the definitions N and B, constants of the block
        (fully applied), and constants of earlier blocks that were themselves
        finitary.  No \<Lambda>, \<cdot>, \<forall>, \<exists>, other Pure definitions, or Pure-level
        abstraction.  A5 fails: the block is accepted, and gd_fuel works, but
        gd_approx refuses it.

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

  Model: approx is the unwinding property (O5).  A finitary body uses the
  lam/app plumbing of the fixed point only to pass to the next unfolding, so
  the finiteness argument is unchanged.

  A2 is missing from pure/gd_def.ML, where definitions are axioms.  There it
  is soundness-critical:
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
