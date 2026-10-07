lemma sat_fuel_mk_eqE:
  assumes a: "a N" and b: "b N" and sat: "sat_fuel (mk_eq a b) A"
  obtains q where "q N" and "evals a A q" and "evals b A q"
