lemma nat_ind_sound_put_fuel:
  assumes p: "p N" and i: "i N" and a: "a N"
      and G: "G N" and A: "A N" and n: "n N"
      and fresh: "fresh_H i G"
      and satG: "sat_hyp_fuel G A"
      and base: "sat_fuel (subst_F p i (pack_T T_ZERO 0)) A"
      and step:
        "⋀m. m N ⟹
          sat_hyp_fuel
            (pack_F F_EQ
               ⟨pack_T T_VAR i, pack_T T_VAR i⟩
               ▹ p ▹ G)
            (asn_put A i m) ⟹
          sat_fuel
            (subst_F p i
              (pack_T T_SUC (pack_T T_VAR i)))
            (asn_put A i m)"
      and eva: "evals a A n"
  shows "sat_fuel (subst_F p i a) A"
