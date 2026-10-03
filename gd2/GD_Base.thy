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


section \<open>Automation\<close>

ML_file \<open>gd_auto.ML\<close>
ML_file \<open>gd_simp.ML\<close>
ML_file \<open>gd_unfold.ML\<close>

lemmas [auto] = nat0 natS eqBool sucNonZero

lemmas [simp] = eq_self_N pred0 predSuc condT condF

end
