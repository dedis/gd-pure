theory GD_NPair
  imports GD_Arith
begin

text \<open>
  Pairing on numerals, by definitions only (no axioms beyond GD_Core):

      npair a b = 2^a * (2b + 1)

  a bijection from pairs of numerals onto the positive numerals, so 0 is left
  over as an atom (nil).  nfst and nsnd invert it by halving.  Everything is
  proved once here; afterwards simp works with the lemmas and never computes
  an encoding (npair is never unfolded).
\<close>


section \<open>Halving and parity\<close>

gd_def half :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>half n \<equiv> if n = 0 then 0 else if n = 1 then 0 else S (half (P (P n)))\<close>

gd_def par :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>par n \<equiv> if n = 0 then 0 else if n = 1 then 1 else par (P (P n))\<close>

lemma half_0 [simp]: \<open>half 0 \<equiv> 0\<close> using half_def[of 0] by simp
lemma half_1 [simp]: \<open>half 1 \<equiv> 0\<close> using half_def[of 1] by simp
lemma half_SS [simp]: \<open>n N \<Longrightarrow> half (S (S n)) \<equiv> S (half n)\<close>
  using half_def[of \<open>S (S n)\<close>] by simp
lemma par_0 [simp]: \<open>par 0 \<equiv> 0\<close> using par_def[of 0] by simp
lemma par_1 [simp]: \<open>par 1 \<equiv> 1\<close> using par_def[of 1] by simp
lemma par_SS [simp]: \<open>n N \<Longrightarrow> par (S (S n)) \<equiv> par n\<close>
  using par_def[of \<open>S (S n)\<close>] by simp

lemma add_SS: \<open>m N \<Longrightarrow> S m + S m = S (S (m + m))\<close>
  by simp

lemma par_double [simp]: \<open>m N \<Longrightarrow> par (m + m) = 0\<close>
  by (induct m) (simp_all add: add_SS)

lemma half_double [simp]: \<open>m N \<Longrightarrow> half (m + m) = m\<close>
  by (induct m) (simp_all add: add_SS)

lemma par_odd [simp]: \<open>m N \<Longrightarrow> par (S (m + m)) = 1\<close>
  by (induct m) (simp_all add: add_SS)

lemma half_odd [simp]: \<open>m N \<Longrightarrow> half (S (m + m)) = m\<close>
  by (induct m) (simp_all add: add_SS)

lemma half_par_N [auto]: \<open>n N \<Longrightarrow> half n N\<close> and par_N [auto]: \<open>n N \<Longrightarrow> par n N\<close>
proof -
  have H: \<open>(half n N) \<and> (par n N)\<close> if n: \<open>n N\<close> for n
    using n
  proof (induct less n)
    case (Step n)
    show ?case using Step(1)
    proof (cases n)
      case Zero
      show ?thesis by (rule conjI, simp_all add: Zero)
    next
      case (Suc m)
      show ?thesis using Suc(1)
      proof (cases m)
        case Zero
        show ?thesis by (rule conjI, simp_all add: Suc Zero)
      next
        case (Suc k)
        have lt: \<open>k < n = 1\<close> using \<open>n = S m\<close> \<open>m = S k\<close> \<open>k N\<close> by (simp add: less_Sleq leq_S_self)
        have ih: \<open>(half k N) \<and> (par k N)\<close> by (rule Step(2)[inst_all, OF \<open>k N\<close> lt])
        show ?thesis
          by (rule conjI, simp_all add: \<open>n = S m\<close> \<open>m = S k\<close> \<open>k N\<close> conjE1[OF ih] conjE2[OF ih])
      qed
    qed
  qed
  show \<open>n N \<Longrightarrow> half n N\<close> by (rule conjE1, rule H)
  show \<open>n N \<Longrightarrow> par n N\<close> by (rule conjE2, rule H)
qed

text \<open>Every numeral is even or odd.\<close>

lemma parity_cases:
  assumes n: \<open>n N\<close>
    and ev: \<open>par n = 0 \<Longrightarrow> half n + half n = n \<Longrightarrow> PROP R\<close>
    and od: \<open>par n = 1 \<Longrightarrow> S (half n + half n) = n \<Longrightarrow> PROP R\<close>
  shows \<open>PROP R\<close>
  using n ev od
proof (induct less n arbitrary: R)
  case (Step n R)
  note ev = Step(3) and od = Step(4)
  show \<open>PROP R\<close> using Step(1)
  proof (cases n)
    case Zero
    show \<open>PROP R\<close> by (rule ev, simp_all add: Zero)
  next
    case (Suc m)
    show \<open>PROP R\<close> using Suc(1)
    proof (cases m)
      case Zero
      show \<open>PROP R\<close> by (rule od, simp_all add: \<open>n = S m\<close> Zero)
    next
      case (Suc k)
      have lt: \<open>k < n = 1\<close> using \<open>n = S m\<close> \<open>m = S k\<close> \<open>k N\<close> by (simp add: less_Sleq leq_S_self)
      show \<open>PROP R\<close>
      proof (rule Step(2)[inst_all, OF \<open>k N\<close> lt])
        assume p: \<open>par k = 0\<close> and h: \<open>half k + half k = k\<close>
        have e1: \<open>par n = 0\<close> using \<open>k N\<close> by (simp add: \<open>n = S m\<close> \<open>m = S k\<close> p)
        have e2: \<open>half n + half n = n\<close> using \<open>k N\<close> by (simp add: \<open>n = S m\<close> \<open>m = S k\<close> add_SS h)
        show \<open>PROP R\<close> by (rule ev[OF e1 e2])
      next
        assume p: \<open>par k = 1\<close> and h: \<open>S (half k + half k) = k\<close>
        have e1: \<open>par n = 1\<close> using \<open>k N\<close> by (simp add: \<open>n = S m\<close> \<open>m = S k\<close> p)
        have e2: \<open>S (half n + half n) = n\<close> using \<open>k N\<close> by (simp add: \<open>n = S m\<close> \<open>m = S k\<close> add_SS h)
        show \<open>PROP R\<close> by (rule od[OF e1 e2])
      qed
    qed
  qed
qed


section \<open>The pairing function\<close>

gd_def npair :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>
  where \<open>npair a b \<equiv> if a = 0 then S (b + b) else npair (P a) b + npair (P a) b\<close>

gd_def nfst :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>nfst n \<equiv> if par n = 1 then 0 else S (nfst (half n))\<close>

gd_def nsnd :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>nsnd n \<equiv> if par n = 1 then half n else nsnd (half n)\<close>

lemma npair_0: \<open>npair 0 b \<equiv> S (b + b)\<close>
  using npair_def[of 0 b] by simp

lemma npair_S: \<open>a N \<Longrightarrow> npair (S a) b \<equiv> npair a b + npair a b\<close>
  using npair_def[of \<open>S a\<close> b] by simp

lemma nfst_odd: \<open>par n = 1 \<Longrightarrow> nfst n \<equiv> 0\<close>
  using nfst_def[of n] by simp

lemma nfst_even: \<open>\<not> (par n = 1) \<Longrightarrow> nfst n \<equiv> S (nfst (half n))\<close>
  using nfst_def[of n] by simp

lemma nsnd_odd: \<open>par n = 1 \<Longrightarrow> nsnd n \<equiv> half n\<close>
  using nsnd_def[of n] by simp

lemma nsnd_even: \<open>\<not> (par n = 1) \<Longrightarrow> nsnd n \<equiv> nsnd (half n)\<close>
  using nsnd_def[of n] by simp

lemma npair_N [auto]:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close>
  shows \<open>npair a b N\<close>
  using a b by (induct a) (simp_all add: npair_0 npair_S)

lemma nfst_npair [simp]:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close>
  shows \<open>nfst (npair a b) = a\<close>
  using a b
proof (induct a)
  case Base
  show ?case using Base by (simp add: npair_0 nfst_odd)
next
  case (Step a)
  have m: \<open>npair a b N\<close> using Step(1,3) by auto
  show ?case using Step m by (simp add: npair_S nfst_even)
qed

lemma nsnd_npair [simp]:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close>
  shows \<open>nsnd (npair a b) = b\<close>
  using a b
proof (induct a)
  case Base
  show ?case using Base by (simp add: npair_0 nsnd_odd)
next
  case (Step a)
  have m: \<open>npair a b N\<close> using Step(1,3) by auto
  show ?case using Step m by (simp add: npair_S nsnd_even)
qed

lemma less_leq_trans:
  assumes x: \<open>x N\<close> and y: \<open>y N\<close> and z: \<open>z N\<close> and xy: \<open>x < y = 1\<close> and yz: \<open>y \<le> z = 1\<close>
  shows \<open>x < z = 1\<close>
proof -
  have \<open>S x \<le> y = 1\<close> using xy unfolding less_Sleq[OF x y] .
  then have \<open>S x \<le> z = 1\<close> by (rule leq_trans[OF natS[OF x] y z _ yz])
  then show ?thesis unfolding less_Sleq[OF x z] .
qed

lemma npair_pos:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close>
  shows \<open>0 < npair a b = 1\<close>
  using a b
proof (induct a)
  case Base
  show ?case using Base by (simp add: npair_0)
next
  case (Step a)
  have m: \<open>npair a b N\<close> using Step(1,3) by auto
  show ?case unfolding npair_S[OF Step(1)]
    by (rule less_leq_trans[OF nat0 m add_N[OF m m] Step(2) leq_add[OF m m]])
qed

lemma npair_neq_0 [simp]: \<open>a N \<Longrightarrow> b N \<Longrightarrow> (npair a b = 0) \<equiv> 0\<close>
proof -
  assume a: \<open>a N\<close> and b: \<open>b N\<close>
  have p: \<open>0 < npair a b = 1\<close> by (rule npair_pos[OF a b])
  have \<open>\<not> (npair a b = 0)\<close>
  proof (rule eq_cases[OF npair_N[OF a b] nat0])
    assume e: \<open>npair a b = 0\<close>
    have \<open>0\<close> using p unfolding eq_reflection[OF e] by simp
    then show \<open>\<not> (npair a b = 0)\<close> by (rule false_elim)
  qed
  then show \<open>(npair a b = 0) \<equiv> 0\<close> by (rule eq_reflection[OF falseE])
qed

text \<open>Components are smaller than the pair: the basis of structural induction.\<close>

lemma nsnd_less:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close>
  shows \<open>b < npair a b = 1\<close>
  using a b
proof (induct a)
  case Base
  show ?case unfolding npair_0
    by (rule leq_imp_less_S[OF Base add_N[OF Base Base] leq_add[OF Base Base]])
next
  case (Step a)
  have m: \<open>npair a b N\<close> using Step(1,3) by auto
  show ?case unfolding npair_S[OF Step(1)]
    by (rule less_leq_trans[OF Step(3) m add_N[OF m m] Step(2) leq_add[OF m m]])
qed

lemma self_less_double:
  assumes m: \<open>m N\<close> and p: \<open>0 < m = 1\<close>
  shows \<open>m < m + m = 1\<close>
  using m p
proof (cases m)
  case Zero
  then show ?thesis using p by simp
next
  case (Suc k)
  have \<open>m \<le> m + k = 1\<close> by (rule leq_add[OF m \<open>k N\<close>])
  then have \<open>S m \<le> S (m + k) = 1\<close> using m \<open>k N\<close> by simp
  then show ?thesis unfolding less_Sleq[OF m add_N[OF m m]] using \<open>m = S k\<close> \<open>k N\<close> m by simp
qed

lemma nfst_less:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close>
  shows \<open>a < npair a b = 1\<close>
  using a b
proof (induct a)
  case Base
  show ?case by (rule npair_pos[OF nat0 Base])
next
  case (Step a)
  have m: \<open>npair a b N\<close> using Step(1,3) by auto
  have Sa: \<open>S a \<le> npair a b = 1\<close> using Step(2) unfolding less_Sleq[OF Step(1) m] .
  have mm: \<open>npair a b < npair a b + npair a b = 1\<close>
    by (rule self_less_double[OF m npair_pos[OF Step(1) Step(3)]])
  have \<open>S a < npair a b + npair a b = 1\<close>
  proof -
    have \<open>S (S a) \<le> S (npair a b) = 1\<close> using Sa Step(1) m by simp
    have \<open>S (npair a b) \<le> npair a b + npair a b = 1\<close> using mm unfolding less_Sleq[OF m add_N[OF m m]] .
    show ?thesis unfolding less_Sleq[OF natS[OF Step(1)] add_N[OF m m]]
      by (rule leq_trans[OF natS[OF natS[OF Step(1)]] natS[OF m] add_N[OF m m]
            \<open>S (S a) \<le> S (npair a b) = 1\<close> \<open>S (npair a b) \<le> npair a b + npair a b = 1\<close>])
  qed
  then show ?case unfolding npair_S[OF Step(1)] .
qed


section \<open>Every positive numeral is a pair\<close>

lemma npair_surj:
  assumes n: \<open>n N\<close> and p: \<open>0 < n = 1\<close>
  shows \<open>nfst n N\<close> and \<open>nsnd n N\<close> and \<open>npair (nfst n) (nsnd n) = n\<close>
proof -
  have H: \<open>((nfst n N) \<and> (nsnd n N)) \<and> npair (nfst n) (nsnd n) = n\<close>
    if n: \<open>n N\<close> and p: \<open>0 < n = 1\<close> for n
    using n p
  proof (induct less n)
    case (Step n)
    note nN = Step(1) and IH = Step(2) and pos = Step(3)
    show ?case
    proof (rule parity_cases[OF nN])
      assume par: \<open>par n = 1\<close> and h: \<open>S (half n + half n) = n\<close>
      have hN: \<open>half n N\<close> by (rule half_par_N(1)[OF nN])
      show ?case
        unfolding nfst_odd[OF par] nsnd_odd[OF par] npair_0
        by (rule conjI, rule conjI, rule nat0, rule hN, rule h)
    next
      assume par: \<open>par n = 0\<close> and h: \<open>half n + half n = n\<close>
      have hN: \<open>half n N\<close> by (rule half_par_N(1)[OF nN])
      have np: \<open>\<not> (par n = 1)\<close> using par by simp
      have hpos: \<open>0 < half n = 1\<close>
      proof (rule nat_cases[OF hN])
        assume z: \<open>half n = 0\<close>
        have e0: \<open>0 = n\<close> using h unfolding eq_reflection[OF z] add_0 .
        have \<open>0\<close> using pos unfolding eq_reflection[OF eqSym[OF e0]] by simp
        then show ?thesis by (rule false_elim)
      next
        fix k assume \<open>k N\<close> and \<open>half n = S k\<close>
        then show ?thesis by simp
      qed
      have lt: \<open>half n < n = 1\<close>
        using self_less_double[OF hN hpos] unfolding eq_reflection[OF h] .
      have ih: \<open>((nfst (half n) N) \<and> (nsnd (half n) N)) \<and> npair (nfst (half n)) (nsnd (half n)) = half n\<close>
        by (rule IH[inst_all, OF hN lt hpos])
      have f: \<open>nfst (half n) N\<close> by (rule conjE1[OF conjE1[OF ih]])
      have s: \<open>nsnd (half n) N\<close> by (rule conjE2[OF conjE1[OF ih]])
      have e: \<open>npair (nfst (half n)) (nsnd (half n)) = half n\<close> by (rule conjE2[OF ih])
      show ?case
        unfolding nfst_even[OF np] nsnd_even[OF np] npair_S[OF f] eq_reflection[OF e]
        by (rule conjI, rule conjI, rule natS[OF f], rule s, rule h)
    qed
  qed
  show \<open>nfst n N\<close> by (rule conjE1[OF conjE1[OF H[OF n p]]])
  show \<open>nsnd n N\<close> by (rule conjE2[OF conjE1[OF H[OF n p]]])
  show \<open>npair (nfst n) (nsnd n) = n\<close> by (rule conjE2[OF H[OF n p]])
qed

lemma npair_cases [case_names HQ Zero Pair]:
  assumes n: \<open>n N\<close>
  shows \<open>(n = 0 \<Longrightarrow> PROP R) \<Longrightarrow> (\<And>a b. a N \<Longrightarrow> b N \<Longrightarrow> n = npair a b \<Longrightarrow> PROP R) \<Longrightarrow> PROP R\<close>
proof (rule nat_cases[OF n])
  assume z: \<open>n = 0\<close> and h: \<open>n = 0 \<Longrightarrow> PROP R\<close>
  show \<open>PROP R\<close> by (rule h[OF z])
next
  fix k
  assume k: \<open>k N\<close> and e: \<open>n = S k\<close>
  assume h: \<open>\<And>a b. a N \<Longrightarrow> b N \<Longrightarrow> n = npair a b \<Longrightarrow> PROP R\<close>
  have p: \<open>0 < n = 1\<close> using e k by simp
  show \<open>PROP R\<close>
    by (rule h[inst_all, OF npair_surj(1)[OF n p] npair_surj(2)[OF n p] eqSym[OF npair_surj(3)[OF n p]]])
qed

end
