lemma check_list_sound_fuel_N:
  assumes pf: "pf N"
  shows "⋀J A. A N ⟹ check_list pf ⟹
    J N ⟹ mem J pf ⟹
    sat_hyp_fuel (hyp_of J) A ⟹
    sat_fuel (conc_of J) A"
