lemma evals_functional:
  assumes t: "t N" and A: "A N" and left: "evals t A r" and right: "evals t A q"
  shows "r = q"
