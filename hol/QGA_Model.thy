theory QGA_Model
  imports Main
begin

(*
  ============================================================================
  A MODEL OF QGA IN ISABELLE/HOL.

  This file interprets the object logic of ../pure/GD.thy inside HOL and
  proves every one of its axioms as an HOL theorem.  Together with the
  soundness of Isabelle/Pure for such interpretations, that is a consistency
  proof for GD.thy: a derivation of False in GD.thy would give a proof of
  Tr gFalse here, and gFalse_not_true refutes it.

  WHY A MODEL RATHER THAN A DEEP EMBEDDING.

  The system modelled here is GD.thy's and only GD.thy's.  ga-work/hol/QGA/
  carries something else that also goes by "QGA" -- a different signature and
  a different rule set (SKI and R combinators in place of pred, cond and a
  definition list; no existential; grounded contradiction primitive rather
  than derived) -- and it is cited here only as precedent, not as a
  specification.  Nothing below is derived from it.

  What that precedent shows is where a deep embedding of a REFLECTIVE
  quantifier gets stuck, and it is worth knowing because the obstruction has
  the same shape whichever system it happens to.  QUANTIFIERS.md there records
  118 sorries, with the universal introduction and elimination cases of
  soundness blocked because they reduce to soundness or completeness of the
  very semantics being defined.  The QGA-on-QGA development in ../pure/ hits
  the same wall independently: under a reflective reading of the universal,
  "a counterexample refutes it" IS a statement of the system's own soundness,
  so no arrangement of an effective evaluator validates notForallI ahead of
  soundness.

  A model is not subject to that.  It is not required to be effective, so the
  universal may be interpreted by the omega-rule -- true when every numeral
  instance is true, false when some numeral instance is false -- and then all
  four quantifier rules, notForallI included, are immediate.  Nothing here is
  recursively enumerable and nothing here needs to be.

  What a model does NOT give is completeness, or the r.e. characterisation of
  grounded truth, or self-consistency.  Those need the operational semantics
  and are a separate line of work.  This file answers exactly one question --
  is the system safe -- and answers it for the whole of GD.thy.

  THE MODEL.

    num  is  nat option    None = bottom,  Some n = the natural n
    o    is  bool option   None = ungrounded, Some True = tt, Some False = ff

  Both are flat domains.  The connectives are Kleene's strong three-valued
  ones, equality is grounded (undefined if either side diverges, otherwise a
  genuine comparison of values), and the conditional returns bottom on an
  ungrounded guard.  omega is bottom, and a := b is interpreted as equality of
  denotations, which is exactly what GD.thy says := means: a and b are
  interchangeable in every context.

  HOW TO CHECK FIDELITY.

  Every lemma below carries the name of the GD.thy axiom it discharges, and
  the GD.thy statement verbatim in the comment above it.  The Pure structure
  is preserved: an axiom stated in GD.thy with Pure's ==> and !! is stated
  here with Pure's ==> and !!, because an HOL theory has the same Pure
  connectives available.  The only difference is the judgment: GD.thy declares
  Trueprop :: o => prop, and here that role is played by Tr :: gform => bool
  composed with HOL's own Trueprop.
  ============================================================================
*)

section \<open>The two domains\<close>

type_synonym gnum  = "nat option"
type_synonym gform = "bool option"

text \<open>GD.thy's \<open>cond\<close>, \<open>def\<close> and \<open>omega\<close> are polymorphic, and are used at both
  \<open>num\<close> and \<open>o\<close>.  A one-method class supplies the bottom element that the
  conditional needs when its guard is ungrounded; both domains are option
  types, so a single instantiation covers them.\<close>

class gbot =
  fixes gbot :: "'a"

instantiation option :: (type) gbot
begin
  definition gbot_option :: "'a option" where "gbot_option = None"
  instance ..
end

lemma gbot_None [simp]: "gbot = None"
  by (simp add: gbot_option_def)


section \<open>The signature of GD.thy, interpreted\<close>

subsection \<open>Equality, negation, disjunction\<close>

text \<open>Grounded equality: a genuine comparison of values, undefined as soon as
  either side denotes nothing.  This is the pivot of the whole system --- it is
  why reflexivity is not free.\<close>

definition gEq :: "gnum \<Rightarrow> gnum \<Rightarrow> gform"  (infixl "\<^bold>=" 45) where
  "gEq a b = (case a of None \<Rightarrow> None
              | Some m \<Rightarrow> (case b of None \<Rightarrow> None | Some n \<Rightarrow> Some (m = n)))"

text \<open>Kleene's strong negation and disjunction: negation swaps the two genuine
  values and preserves the gap; a disjunction is true as soon as one disjunct
  is, whatever the other does, and false only when both are.\<close>

definition gNot :: "gform \<Rightarrow> gform"  ("\<^bold>\<not> _" [40] 40) where
  "gNot p = map_option Not p"

definition gOr :: "gform \<Rightarrow> gform \<Rightarrow> gform"  (infixr "\<^bold>\<or>" 30) where
  "gOr p q = (if p = Some True \<or> q = Some True then Some True
              else if p = Some False \<and> q = Some False then Some False
              else None)"

subsection \<open>Naturals\<close>

definition gZero :: "gnum"  ("\<^bold>0") where "gZero = Some 0"

definition gSuc :: "gnum \<Rightarrow> gnum"  ("\<^bold>S _" [800] 800) where
  "gSuc a = map_option Suc a"

text \<open>Predecessor is truncated at zero, matching \<open>pred0\<close>.\<close>

definition gPred :: "gnum \<Rightarrow> gnum"  ("\<^bold>P _" [800] 800) where
  "gPred a = map_option (\<lambda>n. n - 1) a"

subsection \<open>Quantifiers\<close>

text \<open>The omega-rule reading.  A universal is true when every NUMERAL instance
  is true and false when some numeral instance is false; the quantifier ranges
  over values only, which is what the \<open>x N\<close> premises of \<open>forallI\<close>, \<open>forallE\<close> and
  \<open>existsI\<close> enforce on the syntactic side.  Free variables, by contrast, range
  over the whole flat domain including bottom, which is what makes
  instantiation by an arbitrary term carry no habeas quid obligation.

  This clause is not effective, and that is the point: an effective clause has
  to read the universal reflectively, and then \<open>notForallI\<close> cannot be justified
  ahead of soundness.  A model is under no such constraint.\<close>

definition gAll :: "(gnum \<Rightarrow> gform) \<Rightarrow> gform"  (binder "\<^bold>\<forall>" 10) where
  "gAll Q = (if \<forall>n. Q (Some n) = Some True then Some True
             else if \<exists>n. Q (Some n) = Some False then Some False
             else None)"

definition gEx :: "(gnum \<Rightarrow> gform) \<Rightarrow> gform"  (binder "\<^bold>\<exists>" 10) where
  "gEx Q = (if \<exists>n. Q (Some n) = Some True then Some True
            else if \<forall>n. Q (Some n) = Some False then Some False
            else None)"

subsection \<open>The conditional, definitions, and omega\<close>

text \<open>The guard is a formula, and an ungrounded guard makes the whole
  conditional ungrounded --- which is exactly \<open>condE3\<close> read backwards.\<close>

definition gCond :: "gform \<Rightarrow> 'a::gbot \<Rightarrow> 'a \<Rightarrow> 'a"  ("IF _ THEN _ ELSE _" [25,24,24] 24) where
  "gCond c a b = (case c of Some True \<Rightarrow> a | Some False \<Rightarrow> b | None \<Rightarrow> gbot)"

text \<open>\<open>a := b\<close> does not assert \<open>a = b\<close>; it asserts that \<open>a\<close> and \<open>b\<close> are
  interchangeable in every context, whether or not either denotes a value.  In
  the model that is identity of denotations, and \<open>defE\<close>/\<open>defI\<close> become
  substitution of equals.  \<open>omega := omega\<close> is then harmless, as GD.thy says.\<close>

definition gDef :: "'a \<Rightarrow> 'a \<Rightarrow> gform"  (infix "\<^bold>:=" 10) where
  "gDef a b = Some (a = b)"

definition gOmega :: "'a::gbot" where "gOmega = gbot"

subsection \<open>The judgment\<close>

text \<open>GD.thy declares \<open>Trueprop :: o \<Rightarrow> prop\<close> with the \<open>judgment\<close> command.  Here
  that coercion is \<open>Tr\<close> followed by HOL's own \<open>Trueprop\<close>.  Asserting a formula
  means asserting that it is TRUE, not merely that it is not false: the gap is
  not a third assertible status.\<close>

definition Tr :: "gform \<Rightarrow> bool" where "Tr p \<longleftrightarrow> p = Some True"

subsection \<open>The abbreviations of GD.thy\<close>

text \<open>Defined exactly as GD.thy defines them, so that no rule about them is
  assumed --- each is unfolded and the underlying primitives do the work.\<close>

definition gNeq  :: "gnum \<Rightarrow> gnum \<Rightarrow> gform"  (infixl "\<^bold>\<noteq>" 45) where
  "gNeq a b = (\<^bold>\<not>(a \<^bold>= b))"
definition gB    :: "gform \<Rightarrow> gform"  ("_ \<^bold>B" [21] 20) where
  "gB p = (p \<^bold>\<or> \<^bold>\<not>p)"
definition gN    :: "gnum \<Rightarrow> gform"  ("_ \<^bold>N" [21] 20) where
  "gN x = (x \<^bold>= x)"
definition gAnd  :: "gform \<Rightarrow> gform \<Rightarrow> gform"  (infixl "\<^bold>\<and>" 35) where
  "gAnd p q = (\<^bold>\<not>(\<^bold>\<not>p \<^bold>\<or> \<^bold>\<not>q))"
definition gImp  :: "gform \<Rightarrow> gform \<Rightarrow> gform"  (infixr "\<^bold>\<longrightarrow>" 25) where
  "gImp p q = (\<^bold>\<not>p \<^bold>\<or> q)"
definition gIff  :: "gform \<Rightarrow> gform \<Rightarrow> gform"  (infixl "\<^bold>\<longleftrightarrow>" 25) where
  "gIff p q = ((p \<^bold>\<longrightarrow> q) \<^bold>\<and> (q \<^bold>\<longrightarrow> p))"
definition gTrue :: "gform" where "gTrue = (\<^bold>0 \<^bold>= \<^bold>0)"
definition gFalse :: "gform" where "gFalse = (\<^bold>S \<^bold>0 \<^bold>= \<^bold>0)"

text \<open>Bundles are deliberately narrow.  A single bundle containing \<open>gAll_def\<close>
  and \<open>gEx_def\<close> is unusable: unfolding them puts \<open>\<forall>n. Q (Some n) = Some True\<close>
  into goals that have nothing to do with quantifiers, and \<open>auto\<close> with
  \<open>option.splits\<close> then diverges on the arbitrary function \<open>Q\<close>.  The quantifier
  clauses are reached only through the extraction lemmas below.\<close>

lemmas gprop = gNot_def gOr_def Tr_def
lemmas gnat  = gEq_def gZero_def gSuc_def gPred_def gN_def gB_def gAnd_def
               gNeq_def gNot_def gOr_def gOmega_def Tr_def
lemmas gcnd  = gCond_def gNot_def gOr_def gEq_def gN_def gB_def gAnd_def
               gImp_def gIff_def Tr_def
lemmas gdfn  = gDef_def gOmega_def Tr_def
lemmas gtf   = gEq_def gZero_def gSuc_def gTrue_def gFalse_def Tr_def

subsection \<open>Bounded extraction lemmas\<close>

text \<open>Each of these is decided by a case split on at most two options or one
  if-condition, so the automation has a bounded search space.  Proving the
  axioms through them, rather than by unfolding everything into one \<open>auto\<close>
  call, is what keeps the quantifier cases from diverging: a goal mentioning
  \<open>\<forall>n. Q (Some n) = Some True\<close> must not be handed to \<open>auto\<close> together with
  \<open>option.splits\<close>.\<close>

lemma Tr_simp [simp]: "Tr p \<longleftrightarrow> p = Some True"
  by (simp add: Tr_def)

lemma gEq_TrD: "Tr (a \<^bold>= b) \<Longrightarrow> a = b"
  by (cases a; cases b) (simp_all add: gEq_def)

lemma gEq_TrI: "\<lbrakk>a = Some n; b = Some n\<rbrakk> \<Longrightarrow> Tr (a \<^bold>= b)"
  by (simp add: gEq_def)

lemma gN_TrD: "Tr (a \<^bold>N) \<Longrightarrow> \<exists>n. a = Some n"
  by (cases a) (simp_all add: gN_def gEq_def)

lemma gN_TrI: "a = Some n \<Longrightarrow> Tr (a \<^bold>N)"
  by (simp add: gN_def gEq_def)

lemma gNot_TrD: "Tr (\<^bold>\<not>p) \<Longrightarrow> p = Some False"
  by (cases p) (simp_all add: gNot_def)

lemma gNot_TrI: "p = Some False \<Longrightarrow> Tr (\<^bold>\<not>p)"
  by (simp add: gNot_def)

lemma gAll_TrD: "Tr (\<^bold>\<forall>x. Q x) \<Longrightarrow> \<forall>n. Q (Some n) = Some True"
  by (simp add: gAll_def split: if_splits)

lemma gAll_TrI: "\<forall>n. Q (Some n) = Some True \<Longrightarrow> Tr (\<^bold>\<forall>x. Q x)"
  by (simp add: gAll_def)

lemma gAll_falseD: "(\<^bold>\<forall>x. Q x) = Some False \<Longrightarrow> \<exists>n. Q (Some n) = Some False"
  by (auto simp: gAll_def split: if_splits)

lemma gAll_falseI:
  assumes "Q (Some n) = Some False" shows "(\<^bold>\<forall>x. Q x) = Some False"
proof -
  have a: "\<not> (\<forall>m. Q (Some m) = Some True)"
  proof
    assume "\<forall>m. Q (Some m) = Some True"
    hence "Q (Some n) = Some True" ..
    with assms show False by simp
  qed
  have b: "\<exists>m. Q (Some m) = Some False" using assms ..
  from a b show ?thesis by (simp add: gAll_def)
qed

lemma gEx_TrD: "Tr (\<^bold>\<exists>x. Q x) \<Longrightarrow> \<exists>n. Q (Some n) = Some True"
  by (auto simp: gEx_def split: if_splits)

lemma gEx_TrI:
  assumes "Q (Some n) = Some True" shows "Tr (\<^bold>\<exists>x. Q x)"
proof -
  have "\<exists>m. Q (Some m) = Some True" using assms by blast
  thus ?thesis by (simp add: gEx_def)
qed


section \<open>Every axiom of GD.thy, discharged\<close>

subsection \<open>Disjunction and negation\<close>

text \<open>\<open>disjI1: P \<Longrightarrow> P \<or> Q\<close>\<close>
lemma disjI1: "Tr P \<Longrightarrow> Tr (P \<^bold>\<or> Q)"
  by (simp add: gprop)

text \<open>\<open>disjI2: Q \<Longrightarrow> P \<or> Q\<close>\<close>
lemma disjI2: "Tr Q \<Longrightarrow> Tr (P \<^bold>\<or> Q)"
  by (simp add: gprop)

text \<open>\<open>disjI3: \<lbrakk>\<not>P; \<not>Q\<rbrakk> \<Longrightarrow> \<not>(P \<or> Q)\<close>\<close>
lemma disjI3: "\<lbrakk>Tr (\<^bold>\<not>P); Tr (\<^bold>\<not>Q)\<rbrakk> \<Longrightarrow> Tr (\<^bold>\<not>(P \<^bold>\<or> Q))"
  by (auto simp: gprop split: option.splits)

text \<open>\<open>disjE1: \<lbrakk>P \<or> Q; P \<Longrightarrow> R; Q \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close>\<close>
lemma disjE1: "\<lbrakk>Tr (P \<^bold>\<or> Q); Tr P \<Longrightarrow> Tr R; Tr Q \<Longrightarrow> Tr R\<rbrakk> \<Longrightarrow> Tr R"
  by (auto simp: gprop split: if_splits)

text \<open>\<open>disjE2: \<not>(P \<or> Q) \<Longrightarrow> \<not>P\<close>\<close>
lemma disjE2: "Tr (\<^bold>\<not>(P \<^bold>\<or> Q)) \<Longrightarrow> Tr (\<^bold>\<not>P)"
  by (auto simp: gprop split: if_splits option.splits)

text \<open>\<open>disjE3: \<not>(P \<or> Q) \<Longrightarrow> \<not>Q\<close>\<close>
lemma disjE3: "Tr (\<^bold>\<not>(P \<^bold>\<or> Q)) \<Longrightarrow> Tr (\<^bold>\<not>Q)"
  by (auto simp: gprop split: if_splits option.splits)

text \<open>\<open>dNegI: P \<Longrightarrow> \<not>\<not>P\<close>\<close>
lemma dNegI: "Tr P \<Longrightarrow> Tr (\<^bold>\<not>\<^bold>\<not>P)"
  by (simp add: gprop)

text \<open>\<open>dNegE: \<not>\<not>P \<Longrightarrow> P\<close>\<close>
lemma dNegE: "Tr (\<^bold>\<not>\<^bold>\<not>P) \<Longrightarrow> Tr P"
  by (auto simp: gprop split: option.splits)

text \<open>\<open>exF: \<lbrakk>P; \<not>P\<rbrakk> \<Longrightarrow> Q\<close>.  The one rule that needs the two truth values to be
  exclusive; here they are exclusive because the model is a function into
  \<open>bool option\<close>, not because of any prior theorem.\<close>
lemma exF: "\<lbrakk>Tr P; Tr (\<^bold>\<not>P)\<rbrakk> \<Longrightarrow> Tr Q"
  by (simp add: gprop)

subsection \<open>Equality\<close>

text \<open>\<open>eqSubst: \<lbrakk>a = b; Q a\<rbrakk> \<Longrightarrow> Q b\<close>.  \<open>Q\<close> is an arbitrary context, and it is an
  arbitrary HOL function here, so the rule is covered at full generality.\<close>
lemma eqSubst: "\<lbrakk>Tr (a \<^bold>= b); Tr (Q a)\<rbrakk> \<Longrightarrow> Tr (Q b)"
  by (drule gEq_TrD) simp

text \<open>\<open>eqSym: a = b \<Longrightarrow> b = a\<close>\<close>
lemma eqSym: "Tr (a \<^bold>= b) \<Longrightarrow> Tr (b \<^bold>= a)"
  by (frule gEq_TrD) simp

text \<open>\<open>eq_reflection: x = y \<Longrightarrow> x \<equiv> y\<close>.  A framework rule: its conclusion is a
  Pure equality.  It holds because a true grounded equation forces both sides
  to denote the same element.\<close>
lemma eq_reflection: "Tr (x \<^bold>= y) \<Longrightarrow> x \<equiv> y"
  by (rule HOL.eq_reflection) (rule gEq_TrD)

text \<open>\<open>iff_reflection: p \<longleftrightarrow> q \<Longrightarrow> p \<equiv> q\<close>.  The other framework rule.  A true
  biconditional forces both sides to be grounded and to agree, so they are the
  same element of \<open>bool option\<close>.\<close>
lemma gIff_TrD:
  assumes h: "Tr (p \<^bold>\<longleftrightarrow> q)" shows "p = q"
proof -
  have p3: "p = None \<or> p = Some True \<or> p = Some False" by (cases p) auto
  have q3: "q = None \<or> q = Some True \<or> q = Some False" by (cases q) auto
  from p3 q3 show ?thesis using h
    by (elim disjE) (simp_all add: gIff_def gImp_def gAnd_def gOr_def gNot_def)
qed

lemma iff_reflection: "Tr (p \<^bold>\<longleftrightarrow> q) \<Longrightarrow> p \<equiv> q"
  by (rule HOL.eq_reflection) (rule gIff_TrD)

subsection \<open>Natural numbers\<close>

text \<open>\<open>nat0: zero N\<close>\<close>
lemma nat0: "Tr (\<^bold>0 \<^bold>N)"
  by (simp add: gnat)

text \<open>\<open>sucInj: S a = S b \<Longrightarrow> a = b\<close>\<close>
lemma sucInj: "Tr (\<^bold>S a \<^bold>= \<^bold>S b) \<Longrightarrow> Tr (a \<^bold>= b)"
  by (auto simp: gnat split: option.splits)

text \<open>\<open>sucCong: a = b \<Longrightarrow> S a = S b\<close>\<close>
lemma sucCong: "Tr (a \<^bold>= b) \<Longrightarrow> Tr (\<^bold>S a \<^bold>= \<^bold>S b)"
  by (auto simp: gnat split: option.splits)

text \<open>\<open>predCong: a = b \<Longrightarrow> P a = P b\<close>\<close>
lemma predCong: "Tr (a \<^bold>= b) \<Longrightarrow> Tr (\<^bold>P a \<^bold>= \<^bold>P b)"
  by (auto simp: gnat split: option.splits)

text \<open>\<open>eqBool: \<lbrakk>a N; b N\<rbrakk> \<Longrightarrow> (a = b) B\<close>.  Termination becomes decidability.\<close>
lemma eqBool: "\<lbrakk>Tr (a \<^bold>N); Tr (b \<^bold>N)\<rbrakk> \<Longrightarrow> Tr ((a \<^bold>= b) \<^bold>B)"
  by (auto simp: gnat split: option.splits)

text \<open>\<open>sucNonZero: a N \<Longrightarrow> S a \<noteq> zero\<close>\<close>
lemma sucNonZero: "Tr (a \<^bold>N) \<Longrightarrow> Tr (\<^bold>S a \<^bold>\<noteq> \<^bold>0)"
  by (auto simp: gnat split: option.splits)

text \<open>\<open>predSucInv: a N \<Longrightarrow> P(S(a)) = a\<close>\<close>
lemma predSucInv: "Tr (a \<^bold>N) \<Longrightarrow> Tr (\<^bold>P \<^bold>S a \<^bold>= a)"
  by (auto simp: gnat split: option.splits)

text \<open>\<open>pred0: P(zero) = zero\<close>\<close>
lemma pred0: "Tr (\<^bold>P \<^bold>0 \<^bold>= \<^bold>0)"
  by (simp add: gnat)

text \<open>\<open>eqE: ((a = b) B) \<Longrightarrow> ((a N) \<and> (b N))\<close>\<close>
lemma eqE: "Tr ((a \<^bold>= b) \<^bold>B) \<Longrightarrow> Tr ((a \<^bold>N) \<^bold>\<and> (b \<^bold>N))"
  by (auto simp: gnat split: option.splits)

text \<open>\<open>predTIE: (P a N) \<Longrightarrow> (a N)\<close>\<close>
lemma predTIE: "Tr (\<^bold>P a \<^bold>N) \<Longrightarrow> Tr (a \<^bold>N)"
  by (auto simp: gnat split: option.splits)

text \<open>\<open>ind: \<lbrakk>a N; Q zero; \<And>x. x N \<Longrightarrow> Q x \<Longrightarrow> Q S(x)\<rbrakk> \<Longrightarrow> Q a\<close>.  The motive is an
  arbitrary HOL function, so no formula-complexity restriction is imposed ---
  matching GD.thy, where \<open>Q\<close> is an arbitrary Pure schematic.\<close>
lemma ind:
  assumes aN: "Tr (a \<^bold>N)"
      and base: "Tr (Q \<^bold>0)"
      and step: "\<And>x. Tr (x \<^bold>N) \<Longrightarrow> Tr (Q x) \<Longrightarrow> Tr (Q (\<^bold>S x))"
  shows "Tr (Q a)"
proof -
  from aN obtain n where a: "a = Some n"
    by (auto simp: gnat split: option.splits)
  have "Tr (Q (Some n))"
  proof (induct n)
    case 0 show ?case using base by (simp add: gZero_def)
  next
    case (Suc m)
    have "Tr (Some m \<^bold>N)" by (simp add: gnat)
    from step[OF this Suc] show ?case by (simp add: gSuc_def)
  qed
  thus ?thesis using a by simp
qed

subsection \<open>Quantifiers\<close>

text \<open>\<open>forallI: \<lbrakk>\<And>x. x N \<Longrightarrow> Q x\<rbrakk> \<Longrightarrow> \<forall>x. Q x\<close>.  Pure's \<open>\<And>\<close> ranges over the whole
  flat domain, and the \<open>x N\<close> premise cuts it down to the values --- which is
  exactly the range of the omega-clause.\<close>
lemma forallI:
  assumes "\<And>x. Tr (x \<^bold>N) \<Longrightarrow> Tr (Q x)"
  shows "Tr (\<^bold>\<forall>x. Q x)"
proof (rule gAll_TrI, rule allI)
  fix n show "Q (Some n) = Some True"
    using assms[OF gN_TrI[OF refl]] by simp
qed

text \<open>\<open>forallE: \<lbrakk>\<forall>c'. Q c'; a N\<rbrakk> \<Longrightarrow> Q a\<close>\<close>
lemma forallE:
  assumes q: "Tr (\<^bold>\<forall>x. Q x)" and a: "Tr (a \<^bold>N)"
  shows "Tr (Q a)"
proof -
  from a obtain n where "a = Some n" by (rule gN_TrD[THEN exE])
  with gAll_TrD[OF q] show ?thesis by simp
qed

text \<open>\<open>existsI: \<lbrakk>a N; Q a\<rbrakk> \<Longrightarrow> \<exists>x. Q x\<close>\<close>
lemma existsI:
  assumes a: "Tr (a \<^bold>N)" and q: "Tr (Q a)"
  shows "Tr (\<^bold>\<exists>x. Q x)"
proof -
  from a obtain n where an: "a = Some n" by (rule gN_TrD[THEN exE])
  from q an have "Q (Some n) = Some True" by simp
  thus ?thesis by (rule gEx_TrI)
qed

text \<open>\<open>existsE: \<lbrakk>\<exists>i. Q i; \<And>a. a N \<Longrightarrow> Q a \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close>\<close>
lemma existsE:
  assumes q: "Tr (\<^bold>\<exists>x. Q x)" and step: "\<And>a. Tr (a \<^bold>N) \<Longrightarrow> Tr (Q a) \<Longrightarrow> Tr R"
  shows "Tr R"
proof -
  from gEx_TrD[OF q] obtain n where h: "Q (Some n) = Some True" by blast
  have n1: "Tr (Some n \<^bold>N)" by (rule gN_TrI[OF refl])
  have n2: "Tr (Q (Some n))" using h by simp
  from n1 n2 show ?thesis by (rule step)
qed

text \<open>\<open>notForallI: \<lbrakk>a N; \<not>(F a)\<rbrakk> \<Longrightarrow> \<not>(\<forall>x. F x)\<close>.

  This is the axiom that no effective semantics can validate ahead of
  soundness, and the one the QGA-on-QGA development had to drop.  In the model
  it is one line: a value at which the body is false makes the omega-clause
  return false outright.\<close>
lemma notForallI:
  assumes a: "Tr (a \<^bold>N)" and f: "Tr (\<^bold>\<not>(F a))"
  shows "Tr (\<^bold>\<not>(\<^bold>\<forall>x. F x))"
proof -
  from a obtain n where an: "a = Some n" by (rule gN_TrD[THEN exE])
  from f an have "F (Some n) = Some False" by (simp add: gNot_TrD)
  thus ?thesis by (intro gNot_TrI gAll_falseI)
qed

text \<open>\<open>notForallE: \<lbrakk>\<not>(\<forall>x. F x); \<And>a. a N \<Longrightarrow> \<not>(F a) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R\<close>\<close>
lemma notForallE:
  assumes q: "Tr (\<^bold>\<not>(\<^bold>\<forall>x. F x))"
      and step: "\<And>a. Tr (a \<^bold>N) \<Longrightarrow> Tr (\<^bold>\<not>(F a)) \<Longrightarrow> Tr R"
  shows "Tr R"
proof -
  from gNot_TrD[OF q] have "(\<^bold>\<forall>x. F x) = Some False" .
  from gAll_falseD[OF this] obtain n where h: "F (Some n) = Some False" by blast
  have n1: "Tr (Some n \<^bold>N)" by (rule gN_TrI[OF refl])
  have n2: "Tr (\<^bold>\<not>(F (Some n)))" by (rule gNot_TrI[OF h])
  from n1 n2 show ?thesis by (rule step)
qed

subsection \<open>Conditionals\<close>

text \<open>All fourteen conditional axioms.  These are proved structurally rather
  than by unfolding into one \<open>auto\<close> call: \<open>\<longleftrightarrow>\<close> is an abbreviation for a nest of
  four \<open>\<or>\<close>/\<open>\<not>\<close> nodes, and splitting three options underneath it blows up.  Once
  the guard is decided the conditional simply IS the selected branch, so every
  case is a one-step rewrite.\<close>

lemma gB_TrD: "Tr (p \<^bold>B) \<Longrightarrow> \<exists>v. p = Some v"
  by (cases p) (simp_all add: gB_def gOr_def gNot_def)

lemma gB_TrI: "p = Some v \<Longrightarrow> Tr (p \<^bold>B)"
  by (cases v) (simp_all add: gB_def gOr_def gNot_def)

lemma gIff_refl: "p = Some v \<Longrightarrow> Tr (p \<^bold>\<longleftrightarrow> p)"
  by (cases v) (simp_all add: gIff_def gImp_def gAnd_def gOr_def gNot_def)

lemma gCond_T: "Tr c \<Longrightarrow> (IF c THEN a ELSE b) = a"
  by (simp add: gCond_def)

lemma gCond_F: "Tr (\<^bold>\<not>c) \<Longrightarrow> (IF c THEN a ELSE b) = b"
  by (drule gNot_TrD) (simp add: gCond_def)

text \<open>\<open>condI1: \<lbrakk>c; a N\<rbrakk> \<Longrightarrow> (if c then a else b) = a\<close>\<close>
lemma condI1: "\<lbrakk>Tr c; Tr (a \<^bold>N)\<rbrakk> \<Longrightarrow> Tr ((IF c THEN a ELSE b) \<^bold>= a)"
  by (simp add: gCond_T gN_def)

text \<open>\<open>condI2: \<lbrakk>\<not>c; b N\<rbrakk> \<Longrightarrow> (if c then a else b) = b\<close>\<close>
lemma condI2: "\<lbrakk>Tr (\<^bold>\<not>c); Tr (b \<^bold>N)\<rbrakk> \<Longrightarrow> Tr ((IF c THEN a ELSE b) \<^bold>= b)"
  by (simp add: gCond_F gN_def)

text \<open>\<open>condI1B: \<lbrakk>c; d B\<rbrakk> \<Longrightarrow> (if c then d else e) \<longleftrightarrow> d\<close>\<close>
lemma condI1B:
  assumes c: "Tr c" and d: "Tr (d \<^bold>B)"
  shows "Tr ((IF c THEN d ELSE e) \<^bold>\<longleftrightarrow> d)"
proof -
  from d obtain v where dv: "d = Some v" by (rule gB_TrD[THEN exE])
  have "(IF c THEN d ELSE e) = d" by (rule gCond_T[OF c])
  thus ?thesis using gIff_refl[OF dv] by simp
qed

text \<open>\<open>condI2B: \<lbrakk>\<not>c; e B\<rbrakk> \<Longrightarrow> (if c then d else e) \<longleftrightarrow> e\<close>\<close>
lemma condI2B:
  assumes c: "Tr (\<^bold>\<not>c)" and e: "Tr (e \<^bold>B)"
  shows "Tr ((IF c THEN d ELSE e) \<^bold>\<longleftrightarrow> e)"
proof -
  from e obtain v where ev: "e = Some v" by (rule gB_TrD[THEN exE])
  have "(IF c THEN d ELSE e) = e" by (rule gCond_F[OF c])
  thus ?thesis using gIff_refl[OF ev] by simp
qed

text \<open>\<open>condE1: \<lbrakk>c; (if c then a else b) N\<rbrakk> \<Longrightarrow> (a N)\<close>\<close>
lemma condE1: "\<lbrakk>Tr c; Tr ((IF c THEN a ELSE b) \<^bold>N)\<rbrakk> \<Longrightarrow> Tr (a \<^bold>N)"
  by (simp add: gCond_T)

text \<open>\<open>condE2: \<lbrakk>\<not>c; (if c then a else b) N\<rbrakk> \<Longrightarrow> (b N)\<close>\<close>
lemma condE2: "\<lbrakk>Tr (\<^bold>\<not>c); Tr ((IF c THEN a ELSE b) \<^bold>N)\<rbrakk> \<Longrightarrow> Tr (b \<^bold>N)"
  by (simp add: gCond_F)

text \<open>\<open>condE3: \<lbrakk>(if c then a else b) N\<rbrakk> \<Longrightarrow> (c B)\<close>.  An ungrounded guard makes the
  whole conditional ungrounded, so a grounded conditional decides its guard.\<close>
lemma condE3:
  assumes h: "Tr ((IF c THEN (a::gnum) ELSE b) \<^bold>N)" shows "Tr (c \<^bold>B)"
proof (cases c)
  case None with h show ?thesis by (simp add: gCond_def gN_def gEq_def)
next
  case (Some v) thus ?thesis by (rule gB_TrI)
qed

text \<open>\<open>condE1B: \<lbrakk>c; (if c then d else e) B\<rbrakk> \<Longrightarrow> (d B)\<close>\<close>
lemma condE1B: "\<lbrakk>Tr c; Tr ((IF c THEN d ELSE e) \<^bold>B)\<rbrakk> \<Longrightarrow> Tr (d \<^bold>B)"
  by (simp add: gCond_T)

text \<open>\<open>condE2B: \<lbrakk>\<not>c; (if c then d else e) B\<rbrakk> \<Longrightarrow> (e B)\<close>\<close>
lemma condE2B: "\<lbrakk>Tr (\<^bold>\<not>c); Tr ((IF c THEN d ELSE e) \<^bold>B)\<rbrakk> \<Longrightarrow> Tr (e \<^bold>B)"
  by (simp add: gCond_F)

text \<open>\<open>condE3B: \<lbrakk>(if c then d else e) B\<rbrakk> \<Longrightarrow> (c B)\<close>\<close>
lemma condE3B:
  assumes h: "Tr ((IF c THEN (d::gform) ELSE e) \<^bold>B)" shows "Tr (c \<^bold>B)"
proof (cases c)
  case None with h show ?thesis by (simp add: gCond_def gB_def gOr_def gNot_def)
next
  case (Some v) thus ?thesis by (rule gB_TrI)
qed

text \<open>The lazy quartet \<open>cond_thenQ_E\<close>, \<open>cond_thenQ_I\<close>, \<open>cond_elseQ_E\<close>,
  \<open>cond_elseQ_I\<close>.  \<open>Q\<close> is an arbitrary HOL function, so the rules hold at full
  generality.\<close>

lemma cond_thenQ_E: "\<lbrakk>Tr c; Tr (Q (IF c THEN a ELSE b))\<rbrakk> \<Longrightarrow> Tr (Q a)"
  by (simp add: gCond_T)
lemma cond_thenQ_I: "\<lbrakk>Tr c; Tr (Q a)\<rbrakk> \<Longrightarrow> Tr (Q (IF c THEN a ELSE b))"
  by (simp add: gCond_T)
lemma cond_elseQ_E: "\<lbrakk>Tr (\<^bold>\<not>c); Tr (Q (IF c THEN a ELSE b))\<rbrakk> \<Longrightarrow> Tr (Q b)"
  by (simp add: gCond_F)
lemma cond_elseQ_I: "\<lbrakk>Tr (\<^bold>\<not>c); Tr (Q b)\<rbrakk> \<Longrightarrow> Tr (Q (IF c THEN a ELSE b))"
  by (simp add: gCond_F)


subsection \<open>Definitions\<close>

text \<open>\<open>defE: \<lbrakk>a := b; Q b\<rbrakk> \<Longrightarrow> Q a\<close>\<close>
lemma defE: "\<lbrakk>Tr (a \<^bold>:= b); Tr (Q b)\<rbrakk> \<Longrightarrow> Tr (Q a)"
  by (simp add: gdfn)

text \<open>\<open>defI: \<lbrakk>a := b; Q a\<rbrakk> \<Longrightarrow> Q b\<close>\<close>
lemma defI: "\<lbrakk>Tr (a \<^bold>:= b); Tr (Q a)\<rbrakk> \<Longrightarrow> Tr (Q b)"
  by (simp add: gdfn)

text \<open>\<open>omega_def: omega := omega\<close>.  Admissible precisely because \<open>:=\<close> is
  interchangeability and not equality of values: \<open>omega\<close> is interchangeable
  with itself, and \<open>omega N\<close> is false in the model, matching the fact that it
  is underivable in GD.thy.\<close>
lemma omega_def: "Tr (gOmega \<^bold>:= gOmega)"
  by (simp add: gdfn)

lemma omega_not_nat: "\<not> Tr (gOmega \<^bold>N)"
  by (simp add: gnat)


section \<open>Consistency\<close>

text \<open>\<open>False\<close> is false in the model, so nothing derivable in GD.thy can be
  \<open>False\<close>.  Everything above says that each axiom of GD.thy is true here and
  each rule preserves truth; Pure contributes only assumption, \<open>\<Longrightarrow>\<close> and \<open>\<And>\<close>
  introduction and elimination, instantiation of schematics, and the rules for
  \<open>\<equiv>\<close> --- all of which HOL's own Pure layer supplies and validates.\<close>

theorem gFalse_not_true: "\<not> Tr gFalse"
  by (simp add: gtf)

theorem gTrue_is_true: "Tr gTrue"
  by (simp add: gtf)

text \<open>The two grounded-reasoning workhorses of GD.thy are derived, not
  assumed, exactly as they are there --- a check that the model does not
  accidentally validate more than the axioms give.\<close>

lemma cases_bool: "\<lbrakk>Tr (q \<^bold>B); Tr q \<Longrightarrow> Tr p; Tr (\<^bold>\<not>q) \<Longrightarrow> Tr p\<rbrakk> \<Longrightarrow> Tr p"
  by (rule disjE1[of q "\<^bold>\<not>q"]) (auto simp: gB_def)

lemma contradiction: "\<lbrakk>Tr (p \<^bold>B); Tr (\<^bold>\<not>p) \<Longrightarrow> Tr gFalse\<rbrakk> \<Longrightarrow> Tr p"
  by (rule cases_bool[of p]) (auto simp: gtf)

text \<open>And the two facts that make the logic paracomplete rather than
  classical: excluded middle fails, and it fails at the quantifiers in
  particular.  If either of these were provable the model would be the
  classical one and would prove nothing interesting about GD.thy.\<close>

lemma lem_fails: "\<not> (\<forall>p. Tr (p \<^bold>B))"
  by (rule notI, drule spec[of _ None]) (simp add: gB_def gOr_def gNot_def)

lemma quantified_lem_fails: "\<not> (\<forall>Q. Tr ((\<^bold>\<forall>x. Q x) \<^bold>B))"
  by (rule notI, drule spec[of _ "\<lambda>x. None"])
     (simp add: gB_def gOr_def gNot_def gAll_def)

end
