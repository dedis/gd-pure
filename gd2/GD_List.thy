theory GD_List
  imports GD_Data
begin

text \<open>
  Lists, as data: [] is 0 and h # t is the pair \<langle>h, t\<rangle>.  Everything here is
  a definition or a theorem; the only axioms used are those of GD_Data.

  xs L says that xs is a finite list whose elements are data.  Equations
  between lists are meta-equalities (\<equiv>): grounded equality = compares
  numerals only, and \<equiv> is what rewriting needs anyway.
\<close>

abbreviation Nil :: \<open>tm\<close>  (\<open>[]\<close>)
  where \<open>[] \<equiv> 0\<close>

abbreviation Cons :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixr \<open>#\<close> 65)
  where \<open>h # t \<equiv> \<langle>h, t\<rangle>\<close>

gd_def lshape :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>lshape xs \<equiv> if ispair xs then lshape (snd xs) else xs = 0\<close>

definition isList :: \<open>tm \<Rightarrow> tm\<close>  (\<open>_ L\<close> [21] 20)
  where \<open>xs L \<equiv> (xs D) \<and> (lshape xs)\<close>


section \<open>The list predicate and induction\<close>

lemma lshape_Nil: \<open>lshape [] \<equiv> 1\<close>
  using lshape_def[of 0] by simp

lemma lshape_Cons: \<open>lshape (h # t) \<equiv> lshape t\<close>
  using lshape_def[of \<open>h # t\<close>] by simp

lemma Nil_L [auto]: \<open>[] L\<close>
  unfolding isList_def lshape_Nil by (rule conjI, rule data_N[OF nat0], rule one_true)

lemma Cons_L [auto]:
  assumes h: \<open>h D\<close> and t: \<open>t L\<close>
  shows \<open>(h # t) L\<close>
proof -
  have tD: \<open>t D\<close> by (rule conjE1[OF t[unfolded isList_def]])
  have ts: \<open>lshape t\<close> by (rule conjE2[OF t[unfolded isList_def]])
  show ?thesis unfolding isList_def lshape_Cons by (rule conjI[OF data_pair[OF h tD] ts])
qed

lemma Cons_L_E:
  assumes l: \<open>(h # t) L\<close>
  shows \<open>h D\<close> and \<open>t L\<close>
proof -
  have d: \<open>(h # t) D\<close> by (rule conjE1[OF l[unfolded isList_def]])
  have s: \<open>lshape t\<close> using conjE2[OF l[unfolded isList_def]] unfolding lshape_Cons .
  show \<open>h D\<close> by (rule data_pair_E(1)[OF d])
  show \<open>t L\<close> unfolding isList_def by (rule conjI[OF data_pair_E(2)[OF d] s])
qed

lemma list_D: \<open>xs L \<Longrightarrow> xs D\<close>
  unfolding isList_def by (rule conjE1)

lemma list_induct [case_names HQ Nil Cons, induct]:
  assumes xs: \<open>xs L\<close>
    and nil: \<open>PROP Q ([])\<close>
    and cons: \<open>\<And>h t. h D \<Longrightarrow> t L \<Longrightarrow> PROP Q t \<Longrightarrow> PROP Q (h # t)\<close>
  shows \<open>PROP Q xs\<close>
proof -
  have H: \<open>xs L \<Longrightarrow> PROP Q xs\<close>
  proof (rule data_induct[where Q=\<open>\<lambda>y. (y L \<Longrightarrow> PROP Q y)\<close>, OF list_D[OF xs]])
    fix n
    assume n: \<open>n N\<close>
    assume l: \<open>n L\<close>
    have s: \<open>lshape n\<close> by (rule conjE2[OF l[unfolded isList_def]])
    have z: \<open>n = 0\<close> using n s[unfolded lshape_def[of n]] by simp
    show \<open>PROP Q n\<close> unfolding eq_reflection[OF z] by (rule nil)
  next
    fix a b
    assume a: \<open>a D\<close> and b: \<open>b D\<close>
    assume IHa: \<open>a L \<Longrightarrow> PROP Q a\<close> and IHb: \<open>b L \<Longrightarrow> PROP Q b\<close>
    assume l: \<open>\<langle>a, b\<rangle> L\<close>
    have bL: \<open>b L\<close> by (rule Cons_L_E(2)[OF l])
    show \<open>PROP Q \<langle>a, b\<rangle>\<close> by (rule cons[OF a bL IHb[OF bL]])
  qed
  show \<open>PROP Q xs\<close> by (rule H[OF xs])
qed

lemma list_cases [case_names HQ Nil Cons, cases]:
  assumes xs: \<open>xs L\<close>
  shows \<open>(xs \<equiv> [] \<Longrightarrow> PROP R) \<Longrightarrow> (\<And>h t. h D \<Longrightarrow> t L \<Longrightarrow> xs \<equiv> h # t \<Longrightarrow> PROP R) \<Longrightarrow> PROP R\<close>
proof (rule list_induct[where Q=\<open>\<lambda>y. ((y \<equiv> [] \<Longrightarrow> PROP R) \<Longrightarrow>
    (\<And>h t. h D \<Longrightarrow> t L \<Longrightarrow> y \<equiv> h # t \<Longrightarrow> PROP R) \<Longrightarrow> PROP R)\<close>, OF xs])
  assume n: \<open>[] \<equiv> [] \<Longrightarrow> PROP R\<close>
  show \<open>PROP R\<close> by (rule n, rule Pure.reflexive)
next
  fix h t
  assume h: \<open>h D\<close> and t: \<open>t L\<close>
  assume c: \<open>\<And>h' t'. h' D \<Longrightarrow> t' L \<Longrightarrow> h # t \<equiv> h' # t' \<Longrightarrow> PROP R\<close>
  show \<open>PROP R\<close> by (rule c[inst_all, OF h t], rule Pure.reflexive)
qed


section \<open>Functions on lists\<close>

gd_def len :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>len xs \<equiv> if ispair xs then S (len (snd xs)) else 0\<close>

gd_def app :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>  (infixr \<open>@\<close> 65)
  where \<open>xs @ ys \<equiv> if ispair xs then fst xs # (snd xs @ ys) else ys\<close>

gd_def rev :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>rev xs \<equiv> if ispair xs then rev (snd xs) @ (fst xs # []) else []\<close>

gd_def map :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>
  where \<open>map f xs \<equiv> if ispair xs then (f \<cdot> fst xs) # map f (snd xs) else []\<close>

gd_def sum :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>sum xs \<equiv> if ispair xs then fst xs + sum (snd xs) else 0\<close>

gd_def nth :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm\<close>
  where \<open>nth xs n \<equiv> if n = 0 then fst xs else nth (snd xs) (P n)\<close>

text \<open>Computation rules.  Those for h # t need no premises: pairs are lazy, so
  h and t are never evaluated by the step.\<close>

lemma len_Nil [simp]: \<open>len [] \<equiv> 0\<close> using len_def[of 0] by simp
lemma len_Cons [simp]: \<open>len (h # t) \<equiv> S (len t)\<close> using len_def[of \<open>h # t\<close>] by simp
lemma app_Nil [simp]: \<open>[] @ ys \<equiv> ys\<close> using app_def[of 0 ys] by simp
lemma app_Cons [simp]: \<open>(h # t) @ ys \<equiv> h # (t @ ys)\<close> using app_def[of \<open>h # t\<close> ys] by simp
lemma rev_Nil [simp]: \<open>rev [] \<equiv> []\<close> using rev_def[of 0] by simp
lemma rev_Cons [simp]: \<open>rev (h # t) \<equiv> rev t @ (h # [])\<close> using rev_def[of \<open>h # t\<close>] by simp
lemma map_Nil [simp]: \<open>map f [] \<equiv> []\<close> using map_def[of f 0] by simp
lemma map_Cons [simp]: \<open>map f (h # t) \<equiv> (f \<cdot> h) # map f t\<close> using map_def[of f \<open>h # t\<close>] by simp
lemma sum_Nil [simp]: \<open>sum [] \<equiv> 0\<close> using sum_def[of 0] by simp
lemma sum_Cons [simp]: \<open>sum (h # t) \<equiv> h + sum t\<close> using sum_def[of \<open>h # t\<close>] by simp
lemma nth_0 [simp]: \<open>nth xs 0 \<equiv> fst xs\<close> using nth_def[of xs 0] by simp
lemma nth_S [simp]: \<open>n N \<Longrightarrow> nth xs (S n) \<equiv> nth (snd xs) n\<close> using nth_def[of xs \<open>S n\<close>] by simp


section \<open>Theorems\<close>

lemma len_N [auto]: \<open>xs L \<Longrightarrow> len xs N\<close>
  by (induct xs) simp_all

lemma app_L [auto]:
  assumes xs: \<open>xs L\<close> and ys: \<open>ys L\<close>
  shows \<open>(xs @ ys) L\<close>
  using xs ys by (induct xs) (simp_all add: Cons_L)

lemma len_app:
  assumes xs: \<open>xs L\<close> and ys: \<open>ys L\<close>
  shows \<open>len (xs @ ys) = len xs + len ys\<close>
  using xs ys by (induct xs) simp_all

lemma app_Nil_right [simp]:
  assumes xs: \<open>xs L\<close>
  shows \<open>xs @ [] \<equiv> xs\<close>
  using xs
proof (induct xs)
  case Nil
  show \<open>PROP ?case\<close> by simp
next
  case (Cons h t)
  show \<open>PROP ?case\<close> using Cons(3) by simp
qed

lemma app_assoc:
  assumes xs: \<open>xs L\<close>
  shows \<open>(xs @ ys) @ zs \<equiv> xs @ (ys @ zs)\<close>
  using xs
proof (induct xs)
  case Nil
  show \<open>PROP ?case\<close> by simp
next
  case (Cons h t)
  show \<open>PROP ?case\<close> using Cons(3) by simp
qed

lemma rev_L [auto]:
  assumes xs: \<open>xs L\<close>
  shows \<open>rev xs L\<close>
  using xs by (induct xs) (simp_all add: app_L Cons_L)

lemma rev_app:
  assumes xs: \<open>xs L\<close> and ys: \<open>ys L\<close>
  shows \<open>rev (xs @ ys) \<equiv> rev ys @ rev xs\<close>
  using xs ys
proof (induct xs)
  case Nil
  show \<open>PROP ?case\<close> using Nil by (simp add: rev_L)
next
  case (Cons h t)
  show \<open>PROP ?case\<close> using Cons(1,2,4) by (simp add: Cons(3) app_assoc rev_L)
qed

lemma rev_rev [simp]:
  assumes xs: \<open>xs L\<close>
  shows \<open>rev (rev xs) \<equiv> xs\<close>
  using xs
proof (induct xs)
  case Nil
  show \<open>PROP ?case\<close> by simp
next
  case (Cons h t)
  have hL: \<open>(h # []) L\<close> by (rule Cons_L[OF Cons(1) Nil_L])
  show \<open>PROP ?case\<close> using Cons(1,2) by (simp add: rev_app[OF rev_L[OF Cons(2)] hL] Cons(3))
qed

lemma len_rev:
  assumes xs: \<open>xs L\<close>
  shows \<open>len (rev xs) = len xs\<close>
  using xs
proof (induct xs)
  case Nil
  show ?case by simp
next
  case (Cons h t)
  have hL: \<open>(h # []) L\<close> by (rule Cons_L[OF Cons(1) Nil_L])
  show ?case using Cons by (simp add: len_app[OF rev_L[OF Cons(2)] hL] add_one)
qed

lemma map_app:
  assumes xs: \<open>xs L\<close>
  shows \<open>map f (xs @ ys) \<equiv> map f xs @ map f ys\<close>
  using xs
proof (induct xs)
  case Nil
  show \<open>PROP ?case\<close> by simp
next
  case (Cons h t)
  show \<open>PROP ?case\<close> using Cons(3) by simp
qed

lemma len_map:
  assumes xs: \<open>xs L\<close>
  shows \<open>len (map f xs) = len xs\<close>
  using xs by (induct xs) simp_all

text \<open>Evaluation.\<close>

lemma \<open>rev (1 # 2 # 3 # []) \<equiv> 3 # 2 # 1 # []\<close> by simp
lemma \<open>sum (1 # 2 # 3 # []) = 6\<close> by simp
lemma \<open>len ((1 # 2 # []) @ (3 # [])) = 3\<close> by simp
lemma \<open>nth (5 # 6 # 7 # []) 2 = 7\<close> by simp

end
