lemma sat_fuel_mk_neqE:
  assumes a: "a N" and b: "b N" and sat: "sat_fuel (mk_neq a b) A"
  obtains x y where "x N" and "y N" and "evals a A x" and "evals b A y" and "x ≠ y"
