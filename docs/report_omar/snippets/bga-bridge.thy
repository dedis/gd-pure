lemma soundness_bridge_fuel:
  assumes vp: "is_valid_proof p J"
      and satG: "sat_hyp_fuel (hyp_of J) A"
      and AN: "A N"
  shows "sat_fuel (conc_of J) A"
