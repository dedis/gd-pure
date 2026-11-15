lemma tag_pack_F:
  assumes t: "t N" and L: "L N" shows "tag_F (pack_F t L) = t"
  unfolding tag_F_def pack_F_def by (rule cpx_proj[OF t L])

lemma load_pack_F:
  assumes t: "t N" and L: "L N" shows "load_F (pack_F t L) = L"
  unfolding load_F_def pack_F_def by (rule cpy_proj[OF t L])

lemma tag_pack_T:
  assumes t: "t N" and L: "L N" shows "tag_T (pack_T t L) = t"
  unfolding tag_T_def pack_T_def
  using t by (simp add: cpx_proj[OF swap01_N[OF t] L] swap01_inv[OF t])

lemma load_pack_T:
  assumes t: "t N" and L: "L N" shows "load_T (pack_T t L) = L"
  unfolding load_T_def pack_T_def by (rule cpy_proj[OF swap01_N[OF t] L])

lemma pack_tag_F:
