theory GD_Pairs_Compare
  imports GD_List GD_NList
begin

text \<open>
  Two ways to get pairs, and lists on top of them, compared on the same
  examples.

  Primitive (GD_Data, GD_List): new constants pair, fst, snd, ispair and five
  axioms.  Pairs are a new kind of value, lazy like \<Lambda>.  Nil is 0, h # t is
  \<langle>h, t\<rangle>, a list satisfies xs L.

  Numeric (GD_NPair, GD_NList): npair a b = 2^a (2b + 1), with nfst and nsnd
  defined by gd_def.  No axioms.  Nil is 0, h ## t is npair h t, every
  numeral is a list of numerals, so a list satisfies xs N.

  Functions are named alike: len/nlen, @/+++, rev/nrev, map/nmap, sum/nsum,
  nth/nnth.
\<close>


section \<open>1. Trusted base\<close>

text \<open>Primitive: everything rests on these.  The first four are evaluation
  steps of the extended model; data_induct is a new induction principle.\<close>

thm fst_pair snd_pair ispair_pair ispair_N data_induct

text \<open>Numeric: the corresponding facts are theorems of GD_Core, proved from
  the definitions of npair, nfst, nsnd and induction on numerals.\<close>

thm nfst_npair nsnd_npair npair_cases nlist_induct


section \<open>2. Evaluation\<close>

lemma \<open>rev (1 # 2 # 3 # []) \<equiv> 3 # 2 # 1 # []\<close> by simp
lemma \<open>nrev (1 ## 2 ## 3 ## 0) = 3 ## 2 ## 1 ## 0\<close> by simp

lemma \<open>sum (1 # 2 # 3 # []) = 6\<close> by simp
lemma \<open>nsum (1 ## 2 ## 3 ## 0) = 6\<close> by simp

lemma \<open>nth (5 # 6 # 7 # []) 2 = 7\<close> by simp
lemma \<open>nnth (5 ## 6 ## 7 ## 0) 2 = 7\<close> by simp

text \<open>The numeric encoding is never computed.  20 ## 7 is the numeral
  2^20 \<cdot> 15, about fifteen million applications of S; simp works on the
  npair form through nfst_npair and nsnd_npair and never unfolds it.\<close>

lemma \<open>nfst (20 ## 7) = 20\<close> by simp
lemma \<open>nlen (20 ## 30 ## 0) = 2\<close> by simp


section \<open>3. Computation rules\<close>

text \<open>Primitive cons rules are unconditional; numeric ones need both
  components to be numerals, because npair is strict.\<close>

thm len_Cons map_Cons app_Cons
thm nlen_cons nmap_cons napp_cons


section \<open>4. Laziness\<close>

text \<open>A primitive pair need not have evaluated components.\<close>

lemma \<open>fst \<langle>1, \<bottom>\<rangle> \<equiv> 1\<close> by simp
lemma \<open>len (\<bottom> # \<bottom> # []) = 2\<close> by simp
lemma \<open>len (map (\<Lambda> x. \<bottom>) (1 # 2 # [])) = 2\<close> by simp

text \<open>A numeric pair has a value only if both components do, and so do the
  list functions.  The same examples have no value.\<close>

lemma eqB_N:
  assumes h: \<open>(x = y) B\<close>
  shows \<open>x N\<close>
  by (rule cases_bool[OF h], erule eq_natL, erule neqE1)

lemma add_val_R:
  assumes h: \<open>x + y N\<close>
  shows \<open>y N\<close>
  by (rule eqB_N[OF condE[OF h[unfolded add_def[of x y]]]])

lemma ncons_val:
  assumes h: \<open>(a ## b) N\<close>
  shows \<open>a N\<close> and \<open>b N\<close>
proof -
  show a: \<open>a N\<close> by (rule eqB_N[OF condE[OF h[unfolded npair_def[of a b]]]])
  show \<open>b N\<close>
    using a h
  proof (induct a)
    case Base
    have \<open>S (b + b) N\<close> using Base(1) unfolding npair_0 .
    then show \<open>b N\<close> by (rule add_val_R[OF natSE])
  next
    case (Step j)
    have \<open>npair j b + npair j b N\<close> using Step(3) unfolding npair_S[OF Step(1)] .
    then show \<open>b N\<close> by (rule Step(2)[OF add_val_R])
  qed
qed

lemma nlen_val:
  assumes h: \<open>nlen xs N\<close>
  shows \<open>xs N\<close>
  by (rule eqB_N[OF condE[OF h[unfolded nlen_def[of xs]]]])

lemma \<open>(1 ## \<bottom>) N \<Longrightarrow> PROP R\<close>
  by (rule botE, erule ncons_val(2))

lemma
  assumes h: \<open>nlen (nmap (\<Lambda> x. \<bottom>) (1 ## 2 ## 0)) N\<close>
  shows \<open>PROP R\<close>
proof -
  have e: \<open>nmap (\<Lambda> x. \<bottom>) (1 ## 2 ## 0) \<equiv> \<bottom> ## nmap (\<Lambda> x. \<bottom>) (2 ## 0)\<close>
    by (simp add: beta)
  have \<open>(\<bottom> ## nmap (\<Lambda> x. \<bottom>) (2 ## 0)) N\<close> using nlen_val[OF h] unfolding e .
  then show \<open>PROP R\<close> by (rule botE[OF ncons_val(1)])
qed


section \<open>5. Equality\<close>

text \<open>Numeric lists are numerals, so = is decided on them, and simp decides
  it componentwise through npair_eq without computing the encodings.\<close>

lemma \<open>(1 ## 2 ## 0 = 1 ## 2 ## 0) \<equiv> 1\<close> by simp
lemma \<open>(1 ## 2 ## 0 = 1 ## 3 ## 0) \<equiv> 0\<close> by simp
lemma \<open>xs N \<Longrightarrow> ys N \<Longrightarrow> (nrev xs = ys) B\<close> by (rule eqBool, rule nrev_N, assumption+)

text \<open>A primitive pair is not a numeral, so = has no value on it: neither
  \<langle>1, 0\<rangle> = \<langle>1, 0\<rangle> nor its negation can hold.\<close>

lemma pair_not_N:
  assumes h: \<open>\<langle>a, b\<rangle> N\<close>
  shows \<open>PROP R\<close>
proof -
  have \<open>ispair \<langle>a, b\<rangle> = 0\<close> by (rule ispair_N[OF h])
  then have e: \<open>1 = 0\<close> unfolding ispair_pair .
  show \<open>PROP R\<close> by (rule exF[OF e sucNonZero[OF nat0]])
qed

lemma \<open>\<langle>1, 0\<rangle> = \<langle>1, 0\<rangle> \<Longrightarrow> PROP R\<close> by (rule pair_not_N, erule eq_natL)
lemma \<open>\<not> (\<langle>1, 0\<rangle> = \<langle>2, 0\<rangle>) \<Longrightarrow> PROP R\<close> by (rule pair_not_N, erule neqE1)

text \<open>Comparing primitive data needs its own recursive function.  Using it
  as equality (deq x y \<Longrightarrow> x \<equiv> y for data) would need a further induction
  proof; the numeric side gets this from = for free.\<close>

gd_def deq :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>
  where \<open>deq x y \<equiv> if ispair x then (if ispair y then deq (fst x) (fst y) \<and> deq (snd x) (snd y) else 0)
                   else (if ispair y then 0 else x = y)\<close>

lemma deq_pair [simp]: \<open>deq \<langle>a, b\<rangle> \<langle>c, d\<rangle> \<equiv> deq a c \<and> deq b d\<close>
  using deq_def[of \<open>\<langle>a, b\<rangle>\<close> \<open>\<langle>c, d\<rangle>\<close>] by simp
lemma deq_num [simp]: \<open>m N \<Longrightarrow> n N \<Longrightarrow> deq m n \<equiv> (m = n)\<close>
  using deq_def[of m n] by simp

lemma \<open>deq (1 # 2 # []) (1 # 2 # []) \<equiv> 1\<close> by simp
lemma \<open>deq (1 # 2 # []) (1 # 3 # []) \<equiv> 0\<close> by simp


section \<open>6. Induction and the form of theorems\<close>

text \<open>Both have structural induction (list_induct from data_induct,
  nlist_induct from strong induction on numerals).  The theorems differ in
  form: primitive ones are usually \<equiv> and need fewer premises, since the
  cons rules are unconditional; numeric ones are = between numerals and
  need every argument to be a numeral, including the results of f.\<close>

thm rev_rev nrev_nrev
thm map_app nmap_app

lemma \<open>xs L \<Longrightarrow> len (rev (rev xs)) = len xs\<close> by (simp add: len_N)
lemma \<open>xs N \<Longrightarrow> nlen (nrev (nrev xs)) = nlen xs\<close> by simp


section \<open>7. What can be stored\<close>

text \<open>Primitive pairs hold any term, including functions (though such a
  pair is not data, so list_induct does not cover it).\<close>

lemma \<open>fst \<langle>\<Lambda> x. S x, 0\<rangle> \<cdot> 2 = 3\<close> by (simp add: beta)

text \<open>Numeric pairs hold numerals only.  npair (\<Lambda> x. x) 0 has no value in
  the model, though GD_Core has no rule to refute (\<Lambda> x. x) N, so this is
  not even provable.  Other objects need a numeral code, as in the plan of
  building usable numbers on top of the numerals.\<close>


section \<open>8. Approximation\<close>

gd_approx nlen

thm nlen_approx

end
