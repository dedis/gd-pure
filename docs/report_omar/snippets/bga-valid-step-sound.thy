lemma valid_step_sound_fuel:
  assumes J: "J N" and rest: "rest N" and A: "A N"
      and vs: "valid_step J rest"
      and prev:
        "⋀K A2. A2 N ⟹ K N ⟹ mem K rest ⟹
          sat_hyp_fuel (hyp_of K) A2 ⟹
          sat_fuel (conc_of K) A2"
      and satG: "sat_hyp_fuel (hyp_of J) A"
  shows "sat_fuel (conc_of J) A"
