theory GD_Tree
  imports GD_List
begin

text \<open>
  Binary trees with data at the nodes, following the same recipe as lists:
  an encoding into data, a shape predicate, an induction rule derived from
  data induction, computation rules for the constructors.  This recipe is
  what a datatype command would generate.

  Leaf is 0 and Node l v r is \<langle>l, \<langle>v, r\<rangle>\<rangle>.
\<close>

abbreviation Leaf :: \<open>tm\<close>
  where \<open>Leaf \<equiv> 0\<close>

abbreviation Node :: \<open>tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm\<close>
  where \<open>Node l v r \<equiv> \<langle>l, \<langle>v, r\<rangle>\<rangle>\<close>

gd_def tshape :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>tshape t \<equiv> if ispair t then tshape (fst t) \<and> ispair (snd t) \<and> tshape (snd (snd t))
                   else t = 0\<close>

definition isTree :: \<open>tm \<Rightarrow> tm\<close>  (\<open>_ T\<close> [21] 20)
  where \<open>t T \<equiv> (t D) \<and> (tshape t)\<close>


section \<open>The tree predicate and induction\<close>

lemma tshape_Leaf: \<open>tshape Leaf \<equiv> 1\<close>
  using tshape_def[of 0] by simp

lemma tshape_Node: \<open>tshape (Node l v r) \<equiv> tshape l \<and> 1 \<and> tshape r\<close>
  using tshape_def[of \<open>Node l v r\<close>] by simp

lemma Leaf_T [auto]: \<open>Leaf T\<close>
  unfolding isTree_def tshape_Leaf by (rule conjI, rule data_N[OF nat0], rule one_true)

lemma tree_D: \<open>t T \<Longrightarrow> t D\<close>
  unfolding isTree_def by (rule conjE1)

lemma Node_T [auto]:
  assumes l: \<open>l T\<close> and v: \<open>v D\<close> and r: \<open>r T\<close>
  shows \<open>Node l v r T\<close>
proof -
  have sl: \<open>tshape l\<close> by (rule conjE2[OF l[unfolded isTree_def]])
  have sr: \<open>tshape r\<close> by (rule conjE2[OF r[unfolded isTree_def]])
  show ?thesis unfolding isTree_def tshape_Node
    by (rule conjI, rule data_pair[OF tree_D[OF l] data_pair[OF v tree_D[OF r]]],
        rule conjI, rule conjI, rule sl, rule one_true, rule sr)
qed

lemma Node_T_E:
  assumes h: \<open>Node l v r T\<close>
  shows \<open>l T\<close> and \<open>v D\<close> and \<open>r T\<close>
proof -
  have d: \<open>Node l v r D\<close> by (rule tree_D[OF h])
  have s: \<open>tshape l \<and> 1 \<and> tshape r\<close> using conjE2[OF h[unfolded isTree_def]] unfolding tshape_Node .
  have dl: \<open>l D\<close> by (rule data_pair_E(1)[OF d])
  have dvr: \<open>\<langle>v, r\<rangle> D\<close> by (rule data_pair_E(2)[OF d])
  show \<open>l T\<close> unfolding isTree_def by (rule conjI[OF dl conjE1[OF conjE1[OF s]]])
  show \<open>v D\<close> by (rule data_pair_E(1)[OF dvr])
  show \<open>r T\<close> unfolding isTree_def by (rule conjI[OF data_pair_E(2)[OF dvr] conjE2[OF s]])
qed

lemma tree_induct [case_names HQ Leaf Node, induct]:
  assumes t: \<open>t T\<close>
    and leaf: \<open>PROP Q Leaf\<close>
    and node: \<open>\<And>l v r. l T \<Longrightarrow> v D \<Longrightarrow> r T \<Longrightarrow> PROP Q l \<Longrightarrow> PROP Q r \<Longrightarrow> PROP Q (Node l v r)\<close>
  shows \<open>PROP Q t\<close>
proof -
  have H: \<open>t T \<Longrightarrow> PROP Q t\<close>
  proof (rule data_strong_induct[where Q=\<open>\<lambda>y. (y T \<Longrightarrow> PROP Q y)\<close>, OF tree_D[OF t]])
    fix y
    assume y: \<open>y D\<close>
    assume IH: \<open>\<And>z. z D \<Longrightarrow> dsize z < dsize y = 1 \<Longrightarrow> z T \<Longrightarrow> PROP Q z\<close>
    assume yT: \<open>y T\<close>
    show \<open>PROP Q y\<close>
      using y
    proof (rule data_cases)
      assume n: \<open>y N\<close>
      have s: \<open>tshape y\<close> by (rule conjE2[OF yT[unfolded isTree_def]])
      have z: \<open>y = 0\<close> using n s[unfolded tshape_def[of y]] by simp
      show \<open>PROP Q y\<close> unfolding eq_reflection[OF z] by (rule leaf)
    next
      fix a b
      assume a: \<open>a D\<close> and b: \<open>b D\<close> and e: \<open>y \<equiv> \<langle>a, b\<rangle>\<close>
      have s: \<open>tshape a \<and> ispair b \<and> tshape (snd b)\<close>
        using conjE2[OF yT[unfolded isTree_def]] unfolding e tshape_def[of \<open>\<langle>a, b\<rangle>\<close>] by simp
      have pb: \<open>ispair b\<close> by (rule conjE2[OF conjE1[OF s]])
      have eb: \<open>b \<equiv> \<langle>fst b, snd b\<rangle>\<close> by (rule pair_eta[OF b pb])
      have db: \<open>\<langle>fst b, snd b\<rangle> D\<close> using b unfolding eb[symmetric] .
      have v: \<open>fst b D\<close> by (rule data_pair_E(1)[OF db])
      have r: \<open>snd b D\<close> by (rule data_pair_E(2)[OF db])
      have eN: \<open>\<langle>a, b\<rangle> \<equiv> Node a (fst b) (snd b)\<close>
        unfolding eb[symmetric] by (rule Pure.reflexive)
      have nodeT: \<open>Node a (fst b) (snd b) T\<close> using yT unfolding e eN .
      have lt_a: \<open>dsize a < dsize y = 1\<close> unfolding e by (rule dsize_fst[OF a b])
      have lt_b: \<open>dsize b < dsize y = 1\<close> unfolding e by (rule dsize_snd[OF a b])
      have lt_rb: \<open>dsize (snd b) < dsize b = 1\<close>
        using dsize_snd[OF v r] unfolding eb[symmetric] .
      have lt_r: \<open>dsize (snd b) < dsize y = 1\<close>
        by (rule less_trans[OF dsize_N[OF r] dsize_N[OF b] dsize_N[OF y] lt_rb lt_b])
      have Qa: \<open>PROP Q a\<close> by (rule IH[inst_all, OF a lt_a Node_T_E(1)[OF nodeT]])
      have Qr: \<open>PROP Q (snd b)\<close> by (rule IH[inst_all, OF r lt_r Node_T_E(3)[OF nodeT]])
      show \<open>PROP Q y\<close> unfolding e eN
        by (rule node[OF Node_T_E(1)[OF nodeT] v Node_T_E(3)[OF nodeT] Qa Qr])
    qed
  qed
  show \<open>PROP Q t\<close> by (rule H[OF t])
qed


section \<open>Functions on trees\<close>

gd_def size :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>size t \<equiv> if ispair t then S (size (fst t) + size (snd (snd t))) else 0\<close>

gd_def mirror :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>mirror t \<equiv> if ispair t then Node (mirror (snd (snd t))) (fst (snd t)) (mirror (fst t))
                   else Leaf\<close>

gd_def inorder :: \<open>tm \<Rightarrow> tm\<close>
  where \<open>inorder t \<equiv> if ispair t then inorder (fst t) @ (fst (snd t) # inorder (snd (snd t)))
                    else []\<close>

lemma size_Leaf [simp]: \<open>size Leaf \<equiv> 0\<close> using size_def[of 0] by simp
lemma size_Node [simp]: \<open>size (Node l v r) \<equiv> S (size l + size r)\<close>
  using size_def[of \<open>Node l v r\<close>] by simp
lemma mirror_Leaf [simp]: \<open>mirror Leaf \<equiv> Leaf\<close> using mirror_def[of 0] by simp
lemma mirror_Node [simp]: \<open>mirror (Node l v r) \<equiv> Node (mirror r) v (mirror l)\<close>
  using mirror_def[of \<open>Node l v r\<close>] by simp
lemma inorder_Leaf [simp]: \<open>inorder Leaf \<equiv> []\<close> using inorder_def[of 0] by simp
lemma inorder_Node [simp]: \<open>inorder (Node l v r) \<equiv> inorder l @ (v # inorder r)\<close>
  using inorder_def[of \<open>Node l v r\<close>] by simp


section \<open>Theorems\<close>

lemma size_N [auto]: \<open>t T \<Longrightarrow> size t N\<close>
  by (induct t) simp_all

lemma mirror_T [auto]: \<open>t T \<Longrightarrow> mirror t T\<close>
  by (induct t) (simp_all add: Node_T)

lemma mirror_mirror [simp]:
  assumes t: \<open>t T\<close>
  shows \<open>mirror (mirror t) \<equiv> t\<close>
  using t
proof (induct t)
  case Leaf
  show \<open>PROP ?case\<close> by simp
next
  case (Node l v r)
  show \<open>PROP ?case\<close> using Node(4,5) by simp
qed

lemma size_mirror:
  assumes t: \<open>t T\<close>
  shows \<open>size (mirror t) = size t\<close>
  using t
proof (induct t)
  case Leaf
  show ?case by simp
next
  case (Node l v r)
  show ?case using Node by (simp add: add_comm[of \<open>size r\<close> \<open>size l\<close>])
qed

lemma inorder_L [auto]: \<open>t T \<Longrightarrow> inorder t L\<close>
  by (induct t) (simp_all add: app_L Cons_L)

lemma len_inorder:
  assumes t: \<open>t T\<close>
  shows \<open>len (inorder t) = size t\<close>
  using t
proof (induct t)
  case Leaf
  show ?case by simp
next
  case (Node l v r)
  have il: \<open>inorder l L\<close> by (rule inorder_L[OF Node(1)])
  have ir: \<open>(v # inorder r) L\<close> by (rule Cons_L[OF Node(2) inorder_L[OF Node(3)]])
  show ?case using Node by (simp add: len_app[OF il ir])
qed

lemma \<open>inorder (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) \<equiv> 1 # 2 # 3 # []\<close> by simp

end
