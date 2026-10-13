theory GD_NList
  imports GD_NPair
begin

text \<open>
  Lists over the numeric pairing of GD_NPair: nil is 0 and h ## t is npair h t.
  No axioms beyond GD_Core.  Every numeral is a list of numerals (npair is a
  bijection onto the positive numerals), so the list check is just N, and an
  equation between lists is ordinary grounded equality.
\<close>

abbreviation ncons :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixr \<open>##\<close> 65)
  where \<open>h ## t \<equiv> npair h t\<close>

lemma npair_N_eq [simp]: \<open>a N \<Longrightarrow> b N \<Longrightarrow> (a ## b N) \<equiv> 1\<close>
  by (rule eq_reflection, rule trueE, rule npair_N)

lemma nlist_induct [case_names HQ Nil Cons]:
  assumes xs: \<open>xs N\<close>
    and nil: \<open>PROP Q 0\<close>
    and cons: \<open>\<And>h t. h N \<Longrightarrow> t N \<Longrightarrow> PROP Q t \<Longrightarrow> PROP Q (h ## t)\<close>
  shows \<open>PROP Q xs\<close>
  using xs
proof (induct less xs)
  case (Step x)
  show \<open>PROP Q x\<close>
    using Step(1)
  proof (rule npair_cases)
    assume z: \<open>x = 0\<close>
    show \<open>PROP Q x\<close> unfolding eq_reflection[OF z] by (rule nil)
  next
    fix a b
    assume a: \<open>a N\<close> and b: \<open>b N\<close> and e: \<open>x = a ## b\<close>
    have lt: \<open>b < x = 1\<close> unfolding eq_reflection[OF e] by (rule nsnd_less[OF a b])
    have Qb: \<open>PROP Q b\<close> by (rule Step(2)[inst_all, OF b lt])
    show \<open>PROP Q x\<close> unfolding eq_reflection[OF e] by (rule cons[OF a b Qb])
  qed
qed

lemma npair_inj:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close> and c: \<open>c N\<close> and d: \<open>d N\<close> and e: \<open>a ## b = c ## d\<close>
  shows \<open>a = c\<close> and \<open>b = d\<close>
proof -
  have \<open>nfst (a ## b) = c\<close> unfolding eq_reflection[OF e] by (rule nfst_npair[OF c d])
  then show \<open>a = c\<close> unfolding eq_reflection[OF nfst_npair[OF a b]] .
  have \<open>nsnd (a ## b) = d\<close> unfolding eq_reflection[OF e] by (rule nsnd_npair[OF c d])
  then show \<open>b = d\<close> unfolding eq_reflection[OF nsnd_npair[OF a b]] .
qed

text \<open>Equality of lists is decided componentwise, so simp can decide it.\<close>

lemma npair_eq [simp]:
  assumes a: \<open>a N\<close> and b: \<open>b N\<close> and c: \<open>c N\<close> and d: \<open>d N\<close>
  shows \<open>(a ## b = c ## d) \<equiv> ((a = c) \<and> (b = d))\<close>
proof (rule eq_reflection, rule iff_eq, rule iffI)
  show \<open>(a ## b = c ## d) B\<close> by (rule eqBool[OF npair_N[OF a b] npair_N[OF c d]])
  show \<open>((a = c) \<and> (b = d)) B\<close> by (rule conj_B[OF eqBool[OF a c] eqBool[OF b d]])
  assume e: \<open>a ## b = c ## d\<close>
  show \<open>(a = c) \<and> (b = d)\<close> by (rule conjI[OF npair_inj(1)[OF a b c d e] npair_inj(2)[OF a b c d e]])
next
  assume h: \<open>(a = c) \<and> (b = d)\<close>
  show \<open>a ## b = c ## d\<close>
    unfolding eq_reflection[OF conjE1[OF h]] eq_reflection[OF conjE2[OF h]]
    by (rule natD[OF npair_N[OF c d]])
qed

lemma ncons_neq_nil [simp]: \<open>h N \<Longrightarrow> t N \<Longrightarrow> (0 = h ## t) \<equiv> 0\<close>
  by (rule eq_reflection, rule falseE, rule neq_sym, rule falseI, simp)


section \<open>Functions on lists\<close>

gd_def nlen :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>nlen xs \<equiv> if xs = 0 then 0 else S (nlen (nsnd xs))\<close>

gd_def napp :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixr \<open>+++\<close> 65)
  where \<open>xs +++ ys \<equiv> if xs = 0 then ys else nfst xs ## (nsnd xs +++ ys)\<close>

gd_def nrev :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>nrev xs \<equiv> if xs = 0 then 0 else nrev (nsnd xs) +++ (nfst xs ## 0)\<close>

gd_def nmap :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>
  where \<open>nmap f xs \<equiv> if xs = 0 then 0 else (f \<cdot> nfst xs) ## nmap f (nsnd xs)\<close>

gd_def nsum :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>nsum xs \<equiv> if xs = 0 then 0 else nfst xs + nsum (nsnd xs)\<close>

gd_def nnth :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>
  where \<open>nnth xs n \<equiv> if n = 0 then nfst xs else nnth (nsnd xs) (P n)\<close>

text \<open>Computation rules.  Unlike the primitive pairs of GD_List, the cons
  rules need h N and t N: npair is strict, so h ## t has a value (and is not
  0) only when both components do.\<close>

lemma nlen_0 [simp]: \<open>nlen 0 \<equiv> 0\<close> using nlen_def[of 0] by simp
lemma nlen_cons [simp]: \<open>h N \<Longrightarrow> t N \<Longrightarrow> nlen (h ## t) \<equiv> S (nlen t)\<close>
  using nlen_def[of \<open>h ## t\<close>] by simp
lemma napp_0 [simp]: \<open>0 +++ ys \<equiv> ys\<close> using napp_def[of 0 ys] by simp
lemma napp_cons [simp]: \<open>h N \<Longrightarrow> t N \<Longrightarrow> (h ## t) +++ ys \<equiv> h ## (t +++ ys)\<close>
  using napp_def[of \<open>h ## t\<close> ys] by simp
lemma nrev_0 [simp]: \<open>nrev 0 \<equiv> 0\<close> using nrev_def[of 0] by simp
lemma nrev_cons [simp]: \<open>h N \<Longrightarrow> t N \<Longrightarrow> nrev (h ## t) \<equiv> nrev t +++ (h ## 0)\<close>
  using nrev_def[of \<open>h ## t\<close>] by simp
lemma nmap_0 [simp]: \<open>nmap f 0 \<equiv> 0\<close> using nmap_def[of f 0] by simp
lemma nmap_cons [simp]: \<open>h N \<Longrightarrow> t N \<Longrightarrow> nmap f (h ## t) \<equiv> (f \<cdot> h) ## nmap f t\<close>
  using nmap_def[of f \<open>h ## t\<close>] by simp
lemma nsum_0 [simp]: \<open>nsum 0 \<equiv> 0\<close> using nsum_def[of 0] by simp
lemma nsum_cons [simp]: \<open>h N \<Longrightarrow> t N \<Longrightarrow> nsum (h ## t) \<equiv> h + nsum t\<close>
  using nsum_def[of \<open>h ## t\<close>] by simp
lemma nnth_0 [simp]: \<open>nnth xs 0 \<equiv> nfst xs\<close> using nnth_def[of xs 0] by simp
lemma nnth_S [simp]: \<open>n N \<Longrightarrow> nnth xs (S n) \<equiv> nnth (nsnd xs) n\<close>
  using nnth_def[of xs \<open>S n\<close>] by simp


section \<open>Theorems\<close>

lemma nlen_N [auto]: \<open>xs N \<Longrightarrow> nlen xs N\<close>
  by (induct xs rule: nlist_induct) simp_all

lemma napp_N [auto]:
  assumes xs: \<open>xs N\<close> and ys: \<open>ys N\<close>
  shows \<open>xs +++ ys N\<close>
  using xs ys by (induct xs rule: nlist_induct) simp_all

lemma nlen_app:
  assumes xs: \<open>xs N\<close> and ys: \<open>ys N\<close>
  shows \<open>nlen (xs +++ ys) = nlen xs + nlen ys\<close>
  using xs ys by (induct xs rule: nlist_induct) simp_all

lemma napp_0_right [simp]: \<open>xs N \<Longrightarrow> xs +++ 0 = xs\<close>
  by (induct xs rule: nlist_induct) simp_all

lemma napp_assoc:
  assumes xs: \<open>xs N\<close> and ys: \<open>ys N\<close> and zs: \<open>zs N\<close>
  shows \<open>(xs +++ ys) +++ zs = xs +++ (ys +++ zs)\<close>
  using xs ys zs by (induct xs rule: nlist_induct) simp_all

lemma nrev_N [auto]: \<open>xs N \<Longrightarrow> nrev xs N\<close>
  by (induct xs rule: nlist_induct) simp_all

lemma nrev_app:
  assumes xs: \<open>xs N\<close> and ys: \<open>ys N\<close>
  shows \<open>nrev (xs +++ ys) = nrev ys +++ nrev xs\<close>
  using xs ys by (induct xs rule: nlist_induct) (simp_all add: napp_assoc)

lemma nrev_nrev [simp]: \<open>xs N \<Longrightarrow> nrev (nrev xs) = xs\<close>
  by (induct xs rule: nlist_induct) (simp_all add: nrev_app)

lemma nlen_nrev: \<open>xs N \<Longrightarrow> nlen (nrev xs) = nlen xs\<close>
  by (induct xs rule: nlist_induct) (simp_all add: nlen_app add_one)

text \<open>nmap needs f to return numerals, otherwise f \<cdot> h ## ... has no value.\<close>

lemma nmap_N [auto]:
  assumes f: \<open>\<And>x. x N \<Longrightarrow> f \<cdot> x N\<close> and xs: \<open>xs N\<close>
  shows \<open>nmap f xs N\<close>
  using xs by (induct xs rule: nlist_induct) (simp_all add: f)

lemma nmap_app:
  assumes f: \<open>\<And>x. x N \<Longrightarrow> f \<cdot> x N\<close> and xs: \<open>xs N\<close> and ys: \<open>ys N\<close>
  shows \<open>nmap f (xs +++ ys) = nmap f xs +++ nmap f ys\<close>
  using xs ys
proof (induct xs rule: nlist_induct)
  case Nil
  show ?case using ys nmap_N[OF f ys] by simp
next
  case (Cons h t)
  have fh: \<open>f \<cdot> h N\<close> by (rule f[OF Cons(1)])
  have mt: \<open>nmap f t N\<close> by (rule nmap_N[OF f Cons(2)])
  have my: \<open>nmap f ys N\<close> by (rule nmap_N[OF f ys])
  have ty: \<open>t +++ ys N\<close> by (rule napp_N[OF Cons(2) ys])
  show ?case using Cons(1,2) ty fh mt my Cons(3) by simp
qed

end
