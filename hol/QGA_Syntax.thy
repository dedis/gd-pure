section "Closed datatype syntax for QGA (the object logic of pure/GD.thy)"

theory QGA_Syntax
  imports "HOL-Library.FSet"
begin

text \<open>
  First-order syntax for the language of \<^file>\<open>../pure/GD.thy\<close>, used by
  \<open>QGA_Proof.thy\<close>.  The constructors are exactly GD.thy's primitives; its
  defined connectives are abbreviations here too.  Terms and formulas are
  mutually recursive because GD.thy's \<open>cond\<close> is used at both types.  Binding
  is de Bruijn instead of HOAS, so the eigenvariable conditions become
  context lifting.
\<close>

context
begin

text \<open>Terms and formulas.  Kept outside a locale, since datatypes in locales
      cause trouble.\<close>

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

text \<open>De Bruijn lifting and substitution, mutual over terms and formulas.\<close>

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

text \<open>Lifting then substituting at the same index is the identity; this
      replaces the freshness side condition of the quantifier rules.\<close>

lemma subst_lift_tm [simp]: "subst_tm k s (lift_tm k a) = a"
  and subst_lift_fm [simp]: "subst_fm k s (lift_fm k p) = p"
  by (induct a and p arbitrary: k s and k s) simp_all


subsection "Free-variable substitution, and free variables"

text \<open>\<open>subst_fm\<close> instantiates a binder (quantifier rules); \<open>psub_fm\<close> below
      fills a hole without shifting (rules over a context \<open>Q\<close>).\<close>

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

text \<open>Hypothesis sets are finite.\<close>

abbreviation lift_ctx :: "fm fset \<Rightarrow> fm fset"  ("\<Up>_" [900] 900)
  where "\<Up>\<Gamma> \<equiv> fimage (lift_fm 0) \<Gamma>"

abbreviation subst_ctx :: "nat \<Rightarrow> tm \<Rightarrow> fm fset \<Rightarrow> fm fset"
  where "subst_ctx k s \<Gamma> \<equiv> fimage (subst_fm k s) \<Gamma>"


subsection "Definition lists"

text \<open>A definition list gives each definition number a body over the two
      arguments \<open>\<^bold>v0\<close> and \<open>\<^bold>v1\<close>.  Nothing is assumed about it, so a
      definition may diverge everywhere.\<close>

type_synonym dfns = "nat \<Rightarrow> tm"

abbreviation dfn_body :: "dfns \<Rightarrow> nat \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm"
  where "dfn_body D d a b \<equiv> psub_tm 0 a (psub_tm 1 b (D d))"

text \<open>Both arguments are filled by hole substitution, so the order does not
      matter.\<close>

end
