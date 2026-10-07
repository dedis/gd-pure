lemma eval_fuel_success_add:
  assumes k: "k N" and n: "n N" and t: "t N" and A: "A N" and result: "eval_fuel k t A = S r"
  shows "eval_fuel (k + n) t A = S r"
