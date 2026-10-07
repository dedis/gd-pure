lemma pack_F_N:
  assumes t: "t N" and L: "L N" shows "pack_F t L N"
  unfolding pack_F_def by (rule cpair_terminates[OF t L])

lemma tag_F_N:
  assumes f: "f N" shows "tag_F f N"
  unfolding tag_F_def by (rule cpx_terminates[OF f])

lemma load_F_N:
  assumes f: "f N" shows "load_F f N"
  unfolding load_F_def by (rule cpy_terminates[OF f])

lemma pack_T_N:
  assumes t: "t N" and L: "L N" shows "pack_T t L N"
  unfolding pack_T_def by (rule cpair_terminates[OF swap01_N[OF t] L])

lemma tag_T_N:
  assumes t: "t N" shows "tag_T t N"
  unfolding tag_T_def by (rule swap01_N[OF cpx_terminates[OF t]])

lemma load_T_N:
  assumes t: "t N" shows "load_T t N"
  unfolding load_T_def by (rule cpy_terminates[OF t])
