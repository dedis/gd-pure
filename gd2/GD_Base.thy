theory GD_Base
  imports GD_Core
begin

text \<open>
  The first layer above the kernel: derived connectives (all Pure
  definitions, so conservative), derived rules, numerals, and the automation
  (auto, simp, unfold_def).  Nothing here is an axiom.
\<close>


section \<open>Numerals\<close>

syntax
  "_gd_num" :: \<open>num_token \<Rightarrow> tm\<close>  (\<open>_\<close>)

ML_file \<open>gd_numerals.ML\<close>

parse_translation \<open>
  [(\<^syntax_const>\<open>_gd_num\<close>, GD_Numerals.parse_numeral)]
\<close>


section \<open>Derived connectives\<close>

definition neq :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixl \<open>\<noteq>\<close> 45)
  where \<open>a \<noteq> b \<equiv> \<not> (a = b)\<close>

definition conj :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixl \<open>\<and>\<close> 35)
  where \<open>p \<and> q \<equiv> \<not> (\<not> p \<or> \<not> q)\<close>

definition impl :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixr \<open>\<longrightarrow>\<close> 25)
  where \<open>p \<longrightarrow> q \<equiv> \<not> p \<or> q\<close>

definition iff :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixl \<open>\<longleftrightarrow>\<close> 25)
  where \<open>p \<longleftrightarrow> q \<equiv> (p \<longrightarrow> q) \<and> (q \<longrightarrow> p)\<close>

definition Ex :: \<open>(tm \<Rightarrow> tm) \<Rightarrow> tm\<close>  (binder \<open>\<exists>\<close> [8] 9)
  where \<open>Ex Q \<equiv> \<not> (\<forall>x. \<not> Q x)\<close>


section \<open>Rule sets for the automation\<close>

named_theorems auto "rules the auto method applies unconditionally"
named_theorems cond "rules the auto method applies only if all premises can be solved"


section \<open>Numbers and truth values\<close>

lemma zero_eq [auto]: \<open>0 = 0\<close>
  using nat0 unfolding isNat_def .

lemma natD [auto]: \<open>a N \<Longrightarrow> a = a\<close>
  unfolding isNat_def .

lemma natI: \<open>a = a \<Longrightarrow> a N\<close>
  unfolding isNat_def .

lemma eq_self_N: \<open>(a = a) \<equiv> (a N)\<close>
  unfolding isNat_def by (rule Pure.reflexive)

lemma one_N [auto]: \<open>1 N\<close>
  by (rule natS[OF nat0])

lemma one_true [auto]: \<open>1\<close>
  by (rule trueI, rule natD[OF one_N])

lemma zero_false [auto]: \<open>\<not> 0\<close>
  by (rule falseI, rule zero_eq)

lemma natP [auto]:
  assumes a: \<open>a N\<close>
  shows \<open>P a N\<close>
proof (rule ind[OF a])
  show \<open>P 0 N\<close>
    unfolding eq_reflection[OF pred0] by (rule nat0)
next
  fix x
  assume x: \<open>x N\<close> and \<open>P x N\<close>
  show \<open>P (S x) N\<close>
    unfolding eq_reflection[OF predSuc[OF x]] by (rule x)
qed


section \<open>Decided formulas\<close>

lemma boolI1 [cond]: \<open>p \<Longrightarrow> p B\<close>
  unfolding isBool_def by (rule disjI1)

lemma boolI2 [cond]: \<open>\<not> p \<Longrightarrow> p B\<close>
  unfolding isBool_def by (rule disjI2)

lemma cases_bool:
  assumes b: \<open>p B\<close>
    and t: \<open>p \<Longrightarrow> PROP R\<close>
    and f: \<open>\<not> p \<Longrightarrow> PROP R\<close>
  shows \<open>PROP R\<close>
proof (rule disjE1[where p=p and q=\<open>\<not> p\<close>])
  show \<open>p \<or> \<not> p\<close> using b unfolding isBool_def .
  show \<open>p \<Longrightarrow> PROP R\<close> by (rule t)
  show \<open>\<not> p \<Longrightarrow> PROP R\<close> by (rule f)
qed

lemma not_bool [auto]:
  assumes b: \<open>p B\<close>
  shows \<open>(\<not> p) B\<close>
proof (rule cases_bool[OF b])
  assume \<open>p\<close>
  then show \<open>(\<not> p) B\<close> by (rule boolI2[OF dNegI])
next
  assume \<open>\<not> p\<close>
  then show \<open>(\<not> p) B\<close> by (rule boolI1)
qed

lemma grounded_contradiction:
  assumes b: \<open>p B\<close>
    and h: \<open>\<not> p \<Longrightarrow> q\<close>
    and nh: \<open>\<not> p \<Longrightarrow> \<not> q\<close>
  shows \<open>p\<close>
proof (rule cases_bool[OF b])
  assume \<open>p\<close>
  then show \<open>p\<close> .
next
  assume np: \<open>\<not> p\<close>
  show \<open>p\<close> by (rule exF[OF h[OF np] nh[OF np]])
qed


section \<open>Equality\<close>

lemma eq_bool_natL:
  assumes h: \<open>(a = b) B\<close>
  shows \<open>a N\<close>
proof (rule cases_bool[OF h])
  assume \<open>a = b\<close>
  then show \<open>a N\<close> by (rule eq_natL)
next
  assume \<open>\<not> (a = b)\<close>
  then show \<open>a N\<close> by (rule neqE1)
qed

lemma eq_bool_natR:
  assumes h: \<open>(a = b) B\<close>
  shows \<open>b N\<close>
proof (rule cases_bool[OF h])
  assume \<open>a = b\<close>
  then show \<open>b N\<close> by (rule eq_natR)
next
  assume \<open>\<not> (a = b)\<close>
  then show \<open>b N\<close> by (rule neqE2)
qed

lemma neq_sym:
  assumes h: \<open>\<not> (a = b)\<close>
  shows \<open>\<not> (b = a)\<close>
proof (rule cases_bool[OF eqBool[OF neqE2[OF h] neqE1[OF h]]])
  assume \<open>b = a\<close>
  then have \<open>a = b\<close> by (rule eqSym)
  then show \<open>\<not> (b = a)\<close> using h by (rule exF)
next
  assume \<open>\<not> (b = a)\<close>
  then show \<open>\<not> (b = a)\<close> .
qed

lemma zero_neq_suc [auto]: \<open>a N \<Longrightarrow> \<not> (0 = S a)\<close>
  by (rule neq_sym, rule sucNonZero)

text \<open>Stated in curried form, so that it is proved by a single application of
  ind.  Passing facts that themselves have premises to OF does not match them
  as whole propositions (their premises become new premises), so the base and
  step cases are proved as Isar blocks instead.\<close>

lemma nat_cases:
  assumes a: \<open>a N\<close>
  shows \<open>(a = 0 \<Longrightarrow> PROP R) \<Longrightarrow> (\<And>b. b N \<Longrightarrow> a = S b \<Longrightarrow> PROP R) \<Longrightarrow> PROP R\<close>
proof (rule ind[where Q=\<open>\<lambda>y. ((y = 0 \<Longrightarrow> PROP R) \<Longrightarrow>
                               (\<And>b. b N \<Longrightarrow> y = S b \<Longrightarrow> PROP R) \<Longrightarrow> PROP R)\<close>, OF a])
  assume z: \<open>0 = 0 \<Longrightarrow> PROP R\<close>
  show \<open>PROP R\<close> by (rule z, rule zero_eq)
next
  fix x
  assume x: \<open>x N\<close>
  assume s: \<open>\<And>b. b N \<Longrightarrow> S x = S b \<Longrightarrow> PROP R\<close>
  show \<open>PROP R\<close> by (rule s[OF x natD[OF natS[OF x]]])
qed


section \<open>Conditionals\<close>

lemma cond_nat [auto]:
  assumes c: \<open>c B\<close> and a: \<open>a N\<close> and b: \<open>b N\<close>
  shows \<open>(if c then a else b) N\<close>
proof (rule cases_bool[OF c])
  assume t: \<open>c\<close>
  show \<open>(if c then a else b) N\<close> unfolding condT[OF t] by (rule a)
next
  assume f: \<open>\<not> c\<close>
  show \<open>(if c then a else b) N\<close> unfolding condF[OF f] by (rule b)
qed

lemma cond_bool [auto]:
  assumes c: \<open>c B\<close> and a: \<open>a B\<close> and b: \<open>b B\<close>
  shows \<open>(if c then a else b) B\<close>
proof (rule cases_bool[OF c])
  assume t: \<open>c\<close>
  show \<open>(if c then a else b) B\<close> unfolding condT[OF t] by (rule a)
next
  assume f: \<open>\<not> c\<close>
  show \<open>(if c then a else b) B\<close> unfolding condF[OF f] by (rule b)
qed

lemma condE_bool:
  assumes h: \<open>(if c then a else b) B\<close>
  shows \<open>c B\<close>
proof (rule cases_bool[OF h])
  assume t: \<open>if c then a else b\<close>
  show \<open>c B\<close> by (rule condE, rule eq_natL, rule trueE, rule t)
next
  assume f: \<open>\<not> (if c then a else b)\<close>
  show \<open>c B\<close> by (rule condE, rule eq_natL, rule falseE, rule f)
qed


section \<open>Conjunction, implication, equivalence\<close>

lemma conjI [auto]:
  assumes p: \<open>p\<close> and q: \<open>q\<close>
  shows \<open>p \<and> q\<close>
  unfolding conj_def by (rule disjI3, rule dNegI, rule p, rule dNegI, rule q)

lemma conjE1: \<open>p \<and> q \<Longrightarrow> p\<close>
  unfolding conj_def by (rule dNegE, erule disjE2)

lemma conjE2: \<open>p \<and> q \<Longrightarrow> q\<close>
  unfolding conj_def by (rule dNegE, erule disjE3)

lemma implI:
  assumes b: \<open>p B\<close> and h: \<open>p \<Longrightarrow> q\<close>
  shows \<open>p \<longrightarrow> q\<close>
  unfolding impl_def
proof (rule cases_bool[OF b])
  assume \<open>p\<close>
  then show \<open>\<not> p \<or> q\<close> by (rule disjI2[OF h])
next
  assume \<open>\<not> p\<close>
  then show \<open>\<not> p \<or> q\<close> by (rule disjI1)
qed

lemma mp:
  assumes i: \<open>p \<longrightarrow> q\<close> and p: \<open>p\<close>
  shows \<open>q\<close>
proof (rule disjE1[OF i[unfolded impl_def]])
  assume np: \<open>\<not> p\<close>
  show \<open>q\<close> by (rule exF[OF p np])
next
  assume \<open>q\<close>
  then show \<open>q\<close> .
qed

lemma iffI:
  assumes bp: \<open>p B\<close> and bq: \<open>q B\<close>
    and pq: \<open>p \<Longrightarrow> q\<close> and qp: \<open>q \<Longrightarrow> p\<close>
  shows \<open>p \<longleftrightarrow> q\<close>
  unfolding iff_def
proof (rule conjI)
  show \<open>p \<longrightarrow> q\<close> by (rule implI[OF bp], rule pq)
  show \<open>q \<longrightarrow> p\<close> by (rule implI[OF bq], rule qp)
qed

lemma iffD1: \<open>p \<longleftrightarrow> q \<Longrightarrow> p \<Longrightarrow> q\<close>
  unfolding iff_def by (erule conjE1[THEN mp])

lemma iffD2: \<open>p \<longleftrightarrow> q \<Longrightarrow> q \<Longrightarrow> p\<close>
  unfolding iff_def by (erule conjE2[THEN mp])

text \<open>An equivalence between formulas is an equation between their truth values,
  hence a meta-equality.  In GD.thy this was the axiom iff_reflection.\<close>

lemma iff_eq:
  assumes h: \<open>p \<longleftrightarrow> q\<close>
  shows \<open>p = q\<close>
proof -
  have pq: \<open>\<not> p \<or> q\<close> using conjE1[OF h[unfolded iff_def]] unfolding impl_def .
  have qp: \<open>\<not> q \<or> p\<close> using conjE2[OF h[unfolded iff_def]] unfolding impl_def .
  show \<open>p = q\<close>
  proof (rule disjE1[OF pq])
    assume np: \<open>\<not> p\<close>
    show \<open>p = q\<close>
    proof (rule disjE1[OF qp])
      assume nq: \<open>\<not> q\<close>
      show \<open>p = q\<close> by (rule eq_trans[OF falseE[OF np] eqSym[OF falseE[OF nq]]])
    next
      assume \<open>p\<close>
      then show \<open>p = q\<close> using np by (rule exF)
    qed
  next
    assume q: \<open>q\<close>
    show \<open>p = q\<close>
    proof (rule disjE1[OF qp])
      assume nq: \<open>\<not> q\<close>
      show \<open>p = q\<close> by (rule exF[OF q nq])
    next
      assume p: \<open>p\<close>
      show \<open>p = q\<close> by (rule eq_trans[OF trueE[OF p] eqSym[OF trueE[OF q]]])
    qed
  qed
qed

lemma iff_reflection: \<open>p \<longleftrightarrow> q \<Longrightarrow> p \<equiv> q\<close>
  by (rule eq_reflection, erule iff_eq)


section \<open>The existential quantifier\<close>

lemma exI:
  assumes a: \<open>a N\<close> and q: \<open>Q a\<close>
  shows \<open>\<exists>x. Q x\<close>
  unfolding Ex_def
  by (rule notForallI[where Q=\<open>\<lambda>x. \<not> Q x\<close>, OF a], rule dNegI, rule q)

lemma exE:
  assumes e: \<open>\<exists>x. Q x\<close>
    and h: \<open>\<And>a. a N \<Longrightarrow> Q a \<Longrightarrow> PROP R\<close>
  shows \<open>PROP R\<close>
proof (rule notForallE[where Q=\<open>\<lambda>x. \<not> Q x\<close>, OF e[unfolded Ex_def]])
  fix a
  assume a: \<open>a N\<close> and nn: \<open>\<not> \<not> Q a\<close>
  show \<open>PROP R\<close> by (rule h[OF a dNegE[OF nn]])
qed


section \<open>More propositional facts\<close>

lemma notE: \<open>\<not> p \<Longrightarrow> p \<Longrightarrow> PROP R\<close>
  by (rule exF)

lemma disj_comm: \<open>p \<or> q \<Longrightarrow> q \<or> p\<close>
  by (erule disjE1, erule disjI2, erule disjI1)

lemma conjE:
  assumes h: \<open>p \<and> q\<close> and r: \<open>p \<Longrightarrow> q \<Longrightarrow> PROP R\<close>
  shows \<open>PROP R\<close>
  by (rule r, rule conjE1[OF h], rule conjE2[OF h])

lemma disj_B [auto]:
  assumes p: \<open>p B\<close> and q: \<open>q B\<close>
  shows \<open>(p \<or> q) B\<close>
proof (rule cases_bool[OF p])
  assume \<open>p\<close>
  then show \<open>(p \<or> q) B\<close> by (rule boolI1[OF disjI1])
next
  assume np: \<open>\<not> p\<close>
  show \<open>(p \<or> q) B\<close>
  proof (rule cases_bool[OF q])
    assume \<open>q\<close>
    then show \<open>(p \<or> q) B\<close> by (rule boolI1[OF disjI2])
  next
    assume nq: \<open>\<not> q\<close>
    show \<open>(p \<or> q) B\<close> by (rule boolI2[OF disjI3[OF np nq]])
  qed
qed

lemma conj_B [auto]: \<open>p B \<Longrightarrow> q B \<Longrightarrow> (p \<and> q) B\<close>
  unfolding conj_def by (rule not_bool, rule disj_B, erule not_bool, erule not_bool)

lemma impl_B [auto]: \<open>p B \<Longrightarrow> q B \<Longrightarrow> (p \<longrightarrow> q) B\<close>
  unfolding impl_def by (rule disj_B, erule not_bool)

lemma iff_B [auto]: \<open>p B \<Longrightarrow> q B \<Longrightarrow> (p \<longleftrightarrow> q) B\<close>
  unfolding iff_def by (rule conj_B, rule impl_B, assumption+, rule impl_B, assumption+)

lemma neq_B [auto]: \<open>a N \<Longrightarrow> b N \<Longrightarrow> (a \<noteq> b) B\<close>
  unfolding neq_def by (rule not_bool, rule eqBool)

lemma eq_cases:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close>
  shows \<open>(a = b \<Longrightarrow> PROP R) \<Longrightarrow> (\<not> (a = b) \<Longrightarrow> PROP R) \<Longrightarrow> PROP R\<close>
  by (rule cases_bool[OF eqBool[OF a b]])

text \<open>Equations between numerals, as rewrite rules: the simplifier can decide
  them, and with them the conditions of if-then-else.\<close>

lemma suc_eq_suc [simp]:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close>
  shows \<open>(S a = S b) \<equiv> (a = b)\<close>
proof (rule eq_reflection, rule eq_cases[OF a b])
  assume e: \<open>a = b\<close>
  show \<open>(S a = S b) = (a = b)\<close>
    unfolding eq_reflection[OF e] eq_self_N
    by (rule eq_trans[OF trueE[OF natS[OF b]] eqSym[OF trueE[OF b]]])
next
  assume ne: \<open>\<not> (a = b)\<close>
  have nS: \<open>\<not> (S a = S b)\<close>
  proof (rule eq_cases[OF natS[OF a] natS[OF b]])
    assume \<open>S a = S b\<close>
    then have \<open>a = b\<close> by (rule sucInj)
    then show \<open>\<not> (S a = S b)\<close> using ne by (rule exF)
  next
    assume h: \<open>\<not> (S a = S b)\<close>
    show \<open>\<not> (S a = S b)\<close> by (rule h)
  qed
  show \<open>(S a = S b) = (a = b)\<close> by (rule eq_trans[OF falseE[OF nS] eqSym[OF falseE[OF ne]]])
qed

lemma suc_eq_zero [simp]: \<open>a N \<Longrightarrow> (S a = 0) \<equiv> 0\<close>
  by (rule eq_reflection, rule falseE, rule sucNonZero)

lemma zero_eq_suc [simp]: \<open>a N \<Longrightarrow> (0 = S a) \<equiv> 0\<close>
  by (rule eq_reflection, rule falseE, rule zero_neq_suc)


text \<open>Classical reasoning inside the decided fragment (from pure/GD_Classical.thy).\<close>

lemma lem: \<open>p B \<Longrightarrow> p \<or> \<not> p\<close>
  unfolding isBool_def .

lemma classical:
  assumes b: \<open>p B\<close> and h: \<open>\<not> p \<Longrightarrow> p\<close>
  shows \<open>p\<close>
proof (rule cases_bool[OF b])
  assume \<open>p\<close>
  then show \<open>p\<close> .
next
  assume np: \<open>\<not> p\<close>
  show \<open>p\<close> by (rule h[OF np])
qed

lemma disj_syllogism:
  assumes d: \<open>p \<or> q\<close> and np: \<open>\<not> p\<close>
  shows \<open>q\<close>
proof (rule disjE1[OF d])
  assume p: \<open>p\<close>
  show \<open>q\<close> by (rule exF[OF p np])
next
  assume \<open>q\<close>
  then show \<open>q\<close> .
qed

lemma deMorgan_disj: \<open>\<not> (p \<or> q) \<Longrightarrow> \<not> p \<and> \<not> q\<close>
  by (rule conjI, erule disjE2, erule disjE3)

lemma deMorgan_disj_rev: \<open>\<not> p \<and> \<not> q \<Longrightarrow> \<not> (p \<or> q)\<close>
  by (rule disjI3, erule conjE1, erule conjE2)

lemma deMorgan_conj: \<open>\<not> (p \<and> q) \<Longrightarrow> \<not> p \<or> \<not> q\<close>
  unfolding conj_def by (erule dNegE)

lemma deMorgan_conj_rev: \<open>\<not> p \<or> \<not> q \<Longrightarrow> \<not> (p \<and> q)\<close>
  unfolding conj_def by (erule dNegI)

lemma contrapos:
  assumes i: \<open>p \<longrightarrow> q\<close> and nq: \<open>\<not> q\<close>
  shows \<open>\<not> p\<close>
proof (rule disjE1[OF i[unfolded impl_def]])
  assume \<open>\<not> p\<close>
  then show \<open>\<not> p\<close> .
next
  assume q: \<open>q\<close>
  show \<open>\<not> p\<close> by (rule exF[OF q nq])
qed


section \<open>The conditional, for the simplifier\<close>

text \<open>
  Weak congruence: the simplifier rewrites the condition of an if-then-else
  but not its branches until the condition is decided (then condT or condF
  removes the if).  This is what makes  simp add: f_def  usable for a
  recursive f: the recursive call in the branch not taken is never unfolded.
\<close>

lemma cond_weak_cong [cong]:
  assumes e: \<open>c \<equiv> c'\<close>
  shows \<open>(if c then a else b) \<equiv> (if c' then a else b)\<close>
  unfolding e by (rule Pure.reflexive)

lemma cond_same:
  assumes c: \<open>c B\<close>
  shows \<open>(if c then a else a) \<equiv> a\<close>
proof (rule cases_bool[OF c])
  assume t: \<open>c\<close>
  show \<open>(if c then a else a) \<equiv> a\<close> by (rule condT[OF t])
next
  assume f: \<open>\<not> c\<close>
  show \<open>(if c then a else a) \<equiv> a\<close> by (rule condF[OF f])
qed

text \<open>A conditional has a value only if its condition is decided; these split
  a hypothesis or a goal about its value into the two branches.\<close>

lemma cond_NE:
  assumes h: \<open>(if c then a else b) N\<close>
    and t: \<open>c \<Longrightarrow> a N \<Longrightarrow> PROP R\<close> and f: \<open>\<not> c \<Longrightarrow> b N \<Longrightarrow> PROP R\<close>
  shows \<open>PROP R\<close>
proof (rule cases_bool[OF condE[OF h]])
  assume c: \<open>c\<close>
  show \<open>PROP R\<close> by (rule t[OF c], rule h[unfolded condT[OF c]])
next
  assume c: \<open>\<not> c\<close>
  show \<open>PROP R\<close> by (rule f[OF c], rule h[unfolded condF[OF c]])
qed

lemma cond_eqE:
  assumes h: \<open>(if c then a else b) = v\<close>
    and t: \<open>c \<Longrightarrow> a = v \<Longrightarrow> PROP R\<close> and f: \<open>\<not> c \<Longrightarrow> b = v \<Longrightarrow> PROP R\<close>
  shows \<open>PROP R\<close>
proof (rule cases_bool[OF condE[OF eq_natL[OF h]]])
  assume c: \<open>c\<close>
  show \<open>PROP R\<close> by (rule t[OF c], rule h[unfolded condT[OF c]])
next
  assume c: \<open>\<not> c\<close>
  show \<open>PROP R\<close> by (rule f[OF c], rule h[unfolded condF[OF c]])
qed

lemma cond_eqI:
  assumes c: \<open>c B\<close> and t: \<open>c \<Longrightarrow> a = v\<close> and f: \<open>\<not> c \<Longrightarrow> b = v\<close>
  shows \<open>(if c then a else b) = v\<close>
proof (rule cases_bool[OF c])
  assume h: \<open>c\<close>
  show \<open>(if c then a else b) = v\<close> unfolding condT[OF h] by (rule t[OF h])
next
  assume h: \<open>\<not> c\<close>
  show \<open>(if c then a else b) = v\<close> unfolding condF[OF h] by (rule f[OF h])
qed


section \<open>Truth values, for the simplifier\<close>

text \<open>Facts the simplifier needs to finish: a premise rewritten to 0 closes the
  goal (false_elim, used by the solver), and constants of the logic evaluate.\<close>

lemma false_elim [cond]: \<open>0 \<Longrightarrow> PROP R\<close>
  by (rule exF, assumption, rule zero_false)

lemma nat0_eq [simp]: \<open>(0 N) \<equiv> 1\<close>
  by (rule eq_reflection, rule trueE, rule nat0)

lemma natS_eq [simp]: \<open>a N \<Longrightarrow> (S a N) \<equiv> 1\<close>
  by (rule eq_reflection, rule trueE, rule natS)

lemma not_zero_eq [simp]: \<open>(\<not> 0) \<equiv> 1\<close>
  by (rule eq_reflection, rule trueE, rule zero_false)

lemma not_one_eq [simp]: \<open>(\<not> 1) \<equiv> 0\<close>
  by (rule eq_reflection, rule falseE, rule dNegI, rule one_true)

text \<open>Kleene-strong disjunction: a true disjunct decides it, whatever the other
  does; a false disjunct can be dropped only when the other is decided.\<close>

lemma disj_one_r [simp]: \<open>(p \<or> 1) \<equiv> 1\<close>
  by (rule eq_reflection, rule trueE, rule disjI2, rule one_true)

lemma disj_one_l [simp]: \<open>(1 \<or> p) \<equiv> 1\<close>
  by (rule eq_reflection, rule trueE, rule disjI1, rule one_true)

lemma disj_zero_l [simp]:
  assumes p: \<open>p B\<close>
  shows \<open>(0 \<or> p) \<equiv> p\<close>
proof (rule eq_reflection, rule cases_bool[OF p])
  assume h: \<open>p\<close>
  show \<open>(0 \<or> p) = p\<close> by (rule eq_trans[OF trueE[OF disjI2[OF h]] eqSym[OF trueE[OF h]]])
next
  assume h: \<open>\<not> p\<close>
  show \<open>(0 \<or> p) = p\<close>
    by (rule eq_trans[OF falseE[OF disjI3[OF zero_false h]] eqSym[OF falseE[OF h]]])
qed

lemma disj_zero_r [simp]:
  assumes p: \<open>p B\<close>
  shows \<open>(p \<or> 0) \<equiv> p\<close>
proof (rule eq_reflection, rule cases_bool[OF p])
  assume h: \<open>p\<close>
  show \<open>(p \<or> 0) = p\<close> by (rule eq_trans[OF trueE[OF disjI1[OF h]] eqSym[OF trueE[OF h]]])
next
  assume h: \<open>\<not> p\<close>
  show \<open>(p \<or> 0) = p\<close>
    by (rule eq_trans[OF falseE[OF disjI3[OF h zero_false]] eqSym[OF falseE[OF h]]])
qed

lemma not_not [simp]:
  assumes p: \<open>p B\<close>
  shows \<open>(\<not> \<not> p) \<equiv> p\<close>
proof (rule eq_reflection, rule cases_bool[OF p])
  assume h: \<open>p\<close>
  show \<open>(\<not> \<not> p) = p\<close> by (rule eq_trans[OF trueE[OF dNegI[OF h]] eqSym[OF trueE[OF h]]])
next
  assume h: \<open>\<not> p\<close>
  have nnn: \<open>\<not> \<not> \<not> p\<close> by (rule dNegI[OF h])
  show \<open>(\<not> \<not> p) = p\<close> by (rule eq_trans[OF falseE[OF nnn] eqSym[OF falseE[OF h]]])
qed


lemma conj_zero_l [simp]: \<open>(0 \<and> p) \<equiv> 0\<close>
  unfolding conj_def by simp

lemma conj_zero_r [simp]: \<open>(p \<and> 0) \<equiv> 0\<close>
  unfolding conj_def by simp

lemma conj_one_l [simp]:
  assumes p: \<open>p B\<close>
  shows \<open>(1 \<and> p) \<equiv> p\<close>
  unfolding conj_def not_one_eq disj_zero_l[OF not_bool[OF p]] not_not[OF p] by (rule Pure.reflexive)

lemma conj_one_r [simp]:
  assumes p: \<open>p B\<close>
  shows \<open>(p \<and> 1) \<equiv> p\<close>
  unfolding conj_def not_one_eq disj_zero_r[OF not_bool[OF p]] not_not[OF p] by (rule Pure.reflexive)


section \<open>Automation\<close>

ML_file \<open>gd_auto.ML\<close>
ML_file \<open>gd_simp.ML\<close>
ML_file \<open>gd_unfold.ML\<close>

lemmas [auto] = nat0 natS eqBool sucNonZero

lemmas [simp] = eq_self_N pred0 predSuc condT condF


section \<open>Proof methods: subst, induct, cases\<close>

text \<open>
  subst h: rewrite the goal with h, an equation a = b (used as a \<equiv> b) or a
  meta-equality, at the outermost occurrences only and without rewriting the
  result again (so a recursive equation is unfolded once, as with unfold_def).  Unconditional rewriting with a = b is sound because a
  grounded equation is a meta-equality (eq_reflection).
\<close>

method_setup subst =
  \<open>Attrib.thms >> (fn ths => fn ctxt =>
    SIMPLE_METHOD' (fn i =>
      CHANGED (CONVERSION (Conv.top_sweep_rewrs_conv
        (map (fn th => (th RS @{thm eq_reflection}) handle THM _ => th) ths) ctxt) i)))\<close>
  "rewrite the goal with grounded equations a = b or meta-equalities"

text \<open>
  A fact of the form  \<And>y. A y \<Longrightarrow> B y  (an unfolded motive, or a local
  assumption) cannot be used with OF directly: the outer \<And> hides its premises.
  inst_all turns the outer \<And> into schematic variables first.
\<close>

attribute_setup inst_all =
  \<open>Scan.succeed (Thm.rule_attribute [] (fn _ => fn th =>
      Thm.forall_elim_vars (Thm.maxidx_of th + 1) th))\<close>
  "outer \<And> to schematic variables"

lemma nat_cases_rule [case_names HQ Zero Suc]:
  assumes \<open>a N\<close>
  shows \<open>(a = 0 \<Longrightarrow> PROP R) \<Longrightarrow> (\<And>b. b N \<Longrightarrow> a = S b \<Longrightarrow> PROP R) \<Longrightarrow> PROP R\<close>
  by (rule nat_cases[OF assms])

named_theorems induct "induction rules for the induct method (first premise: the subject is N)"
named_theorems cases "case rules for the cases method (first premise: the subject is N)"

ML_file \<open>gd_induct.ML\<close>

end
