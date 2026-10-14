lemma mono_pack_T:
  assumes tg: "tg N" and x: "x N" and y: "y N" and h: "x ≤ y = 1"
  shows "pack_T tg x ≤ pack_T tg y = 1"
  unfolding pack_T_def by (rule pair_mono_2[OF swap01_N[OF tg] x y h])

lemma mono_pack_F:
  assumes tg: "tg N" and x: "x N" and y: "y N" and h: "x ≤ y = 1"
  shows "pack_F tg x ≤ pack_F tg y = 1"
  unfolding pack_F_def by (rule pair_mono_2[OF tg x y h])
