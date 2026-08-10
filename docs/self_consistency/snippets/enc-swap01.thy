lemma swap01_0 [simp]: "swap01 0 = 1"
  unfolding swap01_def by (cases bool: "(0::num) = 0", simp+)

lemma swap01_N [simp, auto]: "t N ⟹ swap01 t N"
  unfolding swap01_def
  apply (cases bool: "t = 0", simp+)
  done
