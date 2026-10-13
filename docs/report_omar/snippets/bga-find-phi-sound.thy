lemma find_phi_sound_fuel:
  assumes J: "J N" and a: "a N" and b: "b N"
      and rest: "rest N" and ptr: "ptr N" and A: "A N"
      and sub: "subset ptr rest"
      and fp: "find_phi J a b ptr"
      and prev: "⋀K. K N ⟹ mem K rest ⟹
        sat_hyp_fuel (hyp_of K) A ⟹
        sat_fuel (conc_of K) A"
      and satG: "sat_hyp_fuel (hyp_of J) A"
      and tr: "⋀q. q N ⟹ evals a A q ⟹ evals b A q"
  shows "sat_fuel (conc_of J) A"
