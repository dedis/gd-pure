lemma template_instance_sound_fuel:
  assumes p: "p N" and i: "i N" and a: "a N" and b: "b N"
      and phi: "phi N" and f: "f N" and A: "A N" and v: "v N"
      and pa: "subst_F p i a = phi"
      and pb: "subst_F p i b = f"
      and sphi: "sat_fuel phi A"
      and eva: "evals a A v"
      and evb: "evals b A v"
  shows "sat_fuel f A"
