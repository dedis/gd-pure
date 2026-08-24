section "Closed datatype syntax for QGA (the object logic of pure/GD.thy)"

theory QGA_Syntax
  imports "HOL-Library.FSet"
begin

text \<open>
  A first-order presentation of the language of \<^file>\<open>../pure/GD.thy\<close>.

  \<^item> The vocabulary is exactly the constants \<open>GD.thy\<close> axiomatizes: \<open>zero\<close>, \<open>suc\<close>,
    \<open>pred\<close>, \<open>cond\<close>, the definition-list application, \<open>eq\<close>, \<open>not\<close>, \<open>disj\<close>,
    \<open>forall\<close>, \<open>exists\<close>.  Everything \<open>GD.thy\<close> introduces by \<open>definition\<close> (\<open>\<and>\<close>, \<open>\<longrightarrow>\<close>,
    \<open>\<longleftrightarrow>\<close>, \<open>\<noteq>\<close>, \<open>N\<close>, \<open>B\<close>, \<open>True\<close>, \<open>False\<close>) is an abbreviation here too, so no rule
    about them is assumed.
  \<^item> \<open>GD.thy\<close>'s \<open>cond :: o \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close> is guarded by a FORMULA and is used at
    both \<open>num\<close> and \<open>o\<close>, so terms and formulas are mutually recursive and there
    are two conditional constructors, \<open>tmCond\<close> and \<open>fmCond\<close>.
  \<^item> \<open>GD.thy\<close> uses higher-order abstract syntax (\<open>forall :: (num \<Rightarrow> o) \<Rightarrow> o\<close>), which
    cannot be arithmetized; binding is therefore de Bruijn, as in
    \<open>RGA_Syntax.thy\<close>.  \<open>fmAll b\<close> binds index 0 in \<open>b\<close>.  The eigenvariable
    conditions of \<open>forallI\<close>, \<open>existsE\<close>, \<open>notForallE\<close> and \<open>ind\<close> then need no
    freshness side conditions at all: the rules lift the hypothesis context,
    which makes variable 0 fresh for it by construction.
\<close>

context
begin

text \<open>Terms and formulas.  Defined in a bare context rather than a locale,
      following \<open>BGA_Syntax.thy\<close>: datatypes in locales cause trouble.\<close>

datatype tm =
    tmVar   nat            \<comment> \<open>de Bruijn variable\<close>
  | tm0                    \<comment> \<open>\<open>zero\<close>\<close>
  | tmSuc   tm             \<comment> \<open>\<open>suc\<close>\<close>
  | tmPred  tm             \<comment> \<open>\<open>pred\<close>\<close>
  | tmCond  fm tm tm       \<comment> \<open>\<open>cond\<close> at type \<open>num\<close>: guard is a formula\<close>
  | tmApp2  nat tm tm      \<comment> \<open>invoke definition number \<open>d\<close> on two arguments\<close>
and fm =
    fmEq    tm tm          \<comment> \<open>\<open>eq\<close>\<close>
  | fmNot   fm             \<comment> \<open>\<open>not\<close>\<close>
  | fmOr    fm fm          \<comment> \<open>\<open>disj\<close>\<close>
  | fmAll   fm             \<comment> \<open>\<open>forall\<close>, binding de Bruijn index 0\<close>
  | fmEx    fm             \<comment> \<open>\<open>exists\<close>, binding de Bruijn index 0\<close>
  | fmCond  fm fm fm       \<comment> \<open>\<open>cond\<close> at type \<open>o\<close>\<close>

end


subsection "Notation"

notation tm0        ("\<^bold>0")
notation tmSuc      ("\<^bold>S _" [800] 800)
notation tmPred     ("\<^bold>P _" [800] 800)
notation fmEq       (infixl "\<^bold>=" 45)
notation fmNot      ("\<^bold>\<not> _" [40] 40)
notation fmOr       (infixr "\<^bold>\<or>" 30)

abbreviation tmv :: "nat \<Rightarrow> tm"  ("\<^bold>v_" [900] 900) where "tmv n \<equiv> tmVar n"


subsection "Numerals"

primrec numeral_tm :: "nat \<Rightarrow> tm"  ("\<^bold>n_" [900] 900) where
  "numeral_tm 0 = (\<^bold>0)"
| "numeral_tm (Suc n) = (\<^bold>S (numeral_tm n))"

lemma numeral_tm_inj [simp]: "(\<^bold>nm = \<^bold>nn) \<longleftrightarrow> m = n"
  by (induct m arbitrary: n; case_tac n; simp)


subsection "The abbreviations of GD.thy"

text \<open>Defined exactly as \<open>GD.thy\<close> defines them:
  \<open>a \<noteq> b \<equiv> \<not>(a = b)\<close>, \<open>a N \<equiv> a = a\<close>, \<open>p B \<equiv> p \<or> \<not>p\<close>, \<open>p \<and> q \<equiv> \<not>(\<not>p \<or> \<not>q)\<close>,
  \<open>p \<longrightarrow> q \<equiv> \<not>p \<or> q\<close>, \<open>p \<longleftrightarrow> q \<equiv> (p \<longrightarrow> q) \<and> (q \<longrightarrow> p)\<close>, \<open>True \<equiv> 0 = 0\<close>,
  \<open>False \<equiv> S 0 = 0\<close>.\<close>

abbreviation fmNe :: "tm \<Rightarrow> tm \<Rightarrow> fm"  (infixl "\<^bold>\<noteq>" 45)
  where "a \<^bold>\<noteq> b \<equiv> \<^bold>\<not>(a \<^bold>= b)"
abbreviation fmN :: "tm \<Rightarrow> fm"  ("_ \<^bold>N" [80] 80)
  where "a \<^bold>N \<equiv> a \<^bold>= a"
abbreviation fmB :: "fm \<Rightarrow> fm"  ("_ \<^bold>B" [80] 80)
  where "p \<^bold>B \<equiv> p \<^bold>\<or> \<^bold>\<not>p"
abbreviation fmAnd :: "fm \<Rightarrow> fm \<Rightarrow> fm"  (infixl "\<^bold>\<and>" 35)
  where "p \<^bold>\<and> q \<equiv> \<^bold>\<not>(\<^bold>\<not>p \<^bold>\<or> \<^bold>\<not>q)"
abbreviation fmImp :: "fm \<Rightarrow> fm \<Rightarrow> fm"  (infixr "\<^bold>\<longrightarrow>" 25)
  where "p \<^bold>\<longrightarrow> q \<equiv> \<^bold>\<not>p \<^bold>\<or> q"
abbreviation fmIff :: "fm \<Rightarrow> fm \<Rightarrow> fm"  (infixl "\<^bold>\<longleftrightarrow>" 25)
  where "p \<^bold>\<longleftrightarrow> q \<equiv> (p \<^bold>\<longrightarrow> q) \<^bold>\<and> (q \<^bold>\<longrightarrow> p)"
abbreviation fmTrue :: "fm"  ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<^bold>0 \<^bold>= \<^bold>0"
abbreviation fmFalse :: "fm"  ("\<^bold>\<bottom>")
  where "\<^bold>\<bottom> \<equiv> \<^bold>S \<^bold>0 \<^bold>= \<^bold>0"


subsection "Lifting and substitution"

text \<open>Standard de Bruijn machinery.  \<open>lift k\<close> shifts every index at or above
      \<open>k\<close> up by one; \<open>subst k s\<close> replaces index \<open>k\<close> by \<open>s\<close> and shifts the indices
      above it down.  Both are mutual over the two datatypes.\<close>

primrec lift_tm :: "nat \<Rightarrow> tm \<Rightarrow> tm"
    and lift_fm :: "nat \<Rightarrow> fm \<Rightarrow> fm" where
  "lift_tm k (tmVar n)      = (tmVar (if n < k then n else Suc n))"
| "lift_tm k \<^bold>0             = (\<^bold>0)"
| "lift_tm k (\<^bold>S a)         = (\<^bold>S (lift_tm k a))"
| "lift_tm k (\<^bold>P a)         = (\<^bold>P (lift_tm k a))"
| "lift_tm k (tmCond c a b) = (tmCond (lift_fm k c) (lift_tm k a) (lift_tm k b))"
| "lift_tm k (tmApp2 d a b) = (tmApp2 d (lift_tm k a) (lift_tm k b))"
| "lift_fm k (a \<^bold>= b)       = (lift_tm k a \<^bold>= lift_tm k b)"
| "lift_fm k (\<^bold>\<not> p)         = (\<^bold>\<not> (lift_fm k p))"
| "lift_fm k (p \<^bold>\<or> q)       = (lift_fm k p \<^bold>\<or> lift_fm k q)"
| "lift_fm k (fmAll p)      = (fmAll (lift_fm (Suc k) p))"
| "lift_fm k (fmEx p)       = (fmEx (lift_fm (Suc k) p))"
| "lift_fm k (fmCond c p q) = (fmCond (lift_fm k c) (lift_fm k p) (lift_fm k q))"

primrec subst_tm :: "nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"
    and subst_fm :: "nat \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> fm" where
  "subst_tm k s (tmVar n)      = (if n = k then s else if k < n then tmVar (n - 1) else tmVar n)"
| "subst_tm k s \<^bold>0             = (\<^bold>0)"
| "subst_tm k s (\<^bold>S a)         = (\<^bold>S (subst_tm k s a))"
| "subst_tm k s (\<^bold>P a)         = (\<^bold>P (subst_tm k s a))"
| "subst_tm k s (tmCond c a b) = (tmCond (subst_fm k s c) (subst_tm k s a) (subst_tm k s b))"
| "subst_tm k s (tmApp2 d a b) = (tmApp2 d (subst_tm k s a) (subst_tm k s b))"
| "subst_fm k s (a \<^bold>= b)       = (subst_tm k s a \<^bold>= subst_tm k s b)"
| "subst_fm k s (\<^bold>\<not> p)         = (\<^bold>\<not> (subst_fm k s p))"
| "subst_fm k s (p \<^bold>\<or> q)       = (subst_fm k s p \<^bold>\<or> subst_fm k s q)"
| "subst_fm k s (fmAll p)      = (fmAll (subst_fm (Suc k) (lift_tm 0 s) p))"
| "subst_fm k s (fmEx p)       = (fmEx (subst_fm (Suc k) (lift_tm 0 s) p))"
| "subst_fm k s (fmCond c p q) = (fmCond (subst_fm k s c) (subst_fm k s p) (subst_fm k s q))"

abbreviation subst0_fm :: "tm \<Rightarrow> fm \<Rightarrow> fm"  ("[\<mapsto>_]_" [0, 900] 900)
  where "[\<mapsto>s]p \<equiv> subst_fm 0 s p"

abbreviation lift0_fm :: "fm \<Rightarrow> fm"  ("\<upharpoonleft>_" [900] 900)
  where "\<upharpoonleft>p \<equiv> lift_fm 0 p"

text \<open>Lifting then substituting at the same index is the identity: this is
      what makes the lifted contexts of the quantifier rules behave, and it is
      the de Bruijn replacement for a freshness side condition.\<close>

lemma subst_lift_tm [simp]: "subst_tm k s (lift_tm k a) = a"
  and subst_lift_fm [simp]: "subst_fm k s (lift_fm k p) = p"
  by (induct a and p arbitrary: k s and k s) simp_all


subsection "Free-variable substitution, and free variables"

text \<open>Two different substitutions are needed and conflating them is a classic
      source of bugs.  \<open>subst_fm\<close> above INSTANTIATES A BINDER: it removes index
      \<open>k\<close> and shifts what is above it down, which is what \<open>forallE\<close>, \<open>existsI\<close> and
      \<open>notForallI\<close> do to a quantifier body.  \<open>psub_fm\<close> below fills a HOLE: it
      replaces free occurrences of index \<open>k\<close> and shifts nothing, which is what
      the context \<open>Q\<close> of \<open>eqSubst\<close>, \<open>ind\<close>, the lazy conditional rules and
      \<open>defE\<close>/\<open>defI\<close> needs.\<close>

primrec psub_tm :: "nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"
    and psub_fm :: "nat \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> fm" where
  "psub_tm k s (tmVar n)      = (if n = k then s else tmVar n)"
| "psub_tm k s \<^bold>0             = (\<^bold>0)"
| "psub_tm k s (\<^bold>S a)         = (\<^bold>S (psub_tm k s a))"
| "psub_tm k s (\<^bold>P a)         = (\<^bold>P (psub_tm k s a))"
| "psub_tm k s (tmCond c a b) = (tmCond (psub_fm k s c) (psub_tm k s a) (psub_tm k s b))"
| "psub_tm k s (tmApp2 d a b) = (tmApp2 d (psub_tm k s a) (psub_tm k s b))"
| "psub_fm k s (a \<^bold>= b)       = (psub_tm k s a \<^bold>= psub_tm k s b)"
| "psub_fm k s (\<^bold>\<not> p)         = (\<^bold>\<not> (psub_fm k s p))"
| "psub_fm k s (p \<^bold>\<or> q)       = (psub_fm k s p \<^bold>\<or> psub_fm k s q)"
| "psub_fm k s (fmAll p)      = (fmAll (psub_fm (Suc k) (lift_tm 0 s) p))"
| "psub_fm k s (fmEx p)       = (fmEx (psub_fm (Suc k) (lift_tm 0 s) p))"
| "psub_fm k s (fmCond c p q) = (fmCond (psub_fm k s c) (psub_fm k s p) (psub_fm k s q))"

abbreviation psubh :: "nat \<Rightarrow> tm \<Rightarrow> fm \<Rightarrow> fm"  ("[_\<mapsto>_]_" [0, 0, 900] 900)
  where "[i\<mapsto>s]p \<equiv> psub_fm i s p"

primrec fv_tm :: "tm \<Rightarrow> nat set"
    and fv_fm :: "fm \<Rightarrow> nat set" where
  "fv_tm (tmVar n)      = ({n})"
| "fv_tm \<^bold>0             = ({})"
| "fv_tm (\<^bold>S a)         = (fv_tm a)"
| "fv_tm (\<^bold>P a)         = (fv_tm a)"
| "fv_tm (tmCond c a b) = (fv_fm c \<union> fv_tm a \<union> fv_tm b)"
| "fv_tm (tmApp2 d a b) = (fv_tm a \<union> fv_tm b)"
| "fv_fm (a \<^bold>= b)       = (fv_tm a \<union> fv_tm b)"
| "fv_fm (\<^bold>\<not> p)         = (fv_fm p)"
| "fv_fm (p \<^bold>\<or> q)       = (fv_fm p \<union> fv_fm q)"
| "fv_fm (fmAll p)      = ({n. Suc n \<in> fv_fm p})"
| "fv_fm (fmEx p)       = ({n. Suc n \<in> fv_fm p})"
| "fv_fm (fmCond c p q) = (fv_fm c \<union> fv_fm p \<union> fv_fm q)"

abbreviation freein :: "nat \<Rightarrow> fm fset \<Rightarrow> bool"
  where "freein i \<Gamma> \<equiv> (\<exists>p. p |\<in>| \<Gamma> \<and> i \<in> fv_fm p)"


subsection "Hypothesis contexts"

text \<open>Hypothesis sets are finite, as in \<open>Proof.thy\<close> --- deliberately, so that
      proof checking stays primitive recursive when the syntax is coded.\<close>

abbreviation lift_ctx :: "fm fset \<Rightarrow> fm fset"  ("\<Up>_" [900] 900)
  where "\<Up>\<Gamma> \<equiv> fimage (lift_fm 0) \<Gamma>"

abbreviation subst_ctx :: "nat \<Rightarrow> tm \<Rightarrow> fm fset \<Rightarrow> fm fset"
  where "subst_ctx k s \<Gamma> \<equiv> fimage (subst_fm k s) \<Gamma>"


subsection "Definition lists"

text \<open>\<open>GD.thy\<close>'s recursive definitions are introduced by \<open>axiomatization\<close> with
      \<open>:=\<close> equations, and are all two-argument.  A definition list assigns a body
      to each definition number; the body uses \<open>\<^bold>v0\<close> and \<^bold>\<open>v1\<close> for its two
      arguments, as in \<open>BGA\<close>.  Nothing is assumed about the list --- in
      particular its entries may diverge on all arguments, which is what makes
      \<open>omega := omega\<close> admissible.\<close>

type_synonym dfns = "nat \<Rightarrow> tm"

abbreviation dfn_body :: "dfns \<Rightarrow> nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"
  where "dfn_body D d a b \<equiv> psub_tm 0 a (psub_tm 1 b (D d))"

text \<open>Both arguments are filled by HOLE substitution, at the two distinct
      indices 0 and 1.  \<open>psub\<close> shifts nothing, so the two fills commute and no
      lifting is needed --- unlike a binder instantiation, which would have to
      shift and would make the order matter.\<close>

end
