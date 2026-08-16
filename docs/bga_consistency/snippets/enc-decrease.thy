lemma decrease_F:
  assumes f: "f N" and nz: "f ≠ 0" shows "load_F f < f = 1"
  unfolding load_F_def using f nz by simp

lemma decrease_T:
  assumes t: "t N" and nz: "t ≠ 0" shows "load_T t < t = 1"
  unfolding load_T_def using t nz by simp

lemma tag_T_zero: "tag_T 0 = T_ZERO"
  unfolding tag_T_def by simp
