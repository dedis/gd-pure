lemma sat_fuel_subst_FD:
  assumes f: "f N" and i: "i N" and s: "s N" and A: "A N" and v: "v N"
      and evs: "evals s A v" and sat: "sat_fuel (subst_F f i s) A"
  shows "sat_fuel f (asn_put A i v)"
