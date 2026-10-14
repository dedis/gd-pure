lemma sat_fuel_subst_FI:
  assumes f: "f N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and evs: "evals s A v" and sat: "sat_fuel f (asn_put A i v)"
  shows "sat_fuel (subst_F f i s) A"
