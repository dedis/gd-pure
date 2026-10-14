lemma eval_fuel_success_unique:
  assumes k: "k N" and l: "l N" and t: "t N" and A: "A N"
      and left: "eval_fuel k t A = S r" and right: "eval_fuel l t A = S q"
  shows "r = q"
