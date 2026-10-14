locale consistent =  suff_semantics +
  (* Valid proofs yield satisfied formulas *)
  assumes soundness: "⟦is_valid_proof p J; sat_hyp (hyp_of J) A; A N⟧ ⟹ sat_fm (conc_of J) A"
begin

lemma syntactically_consistent:
  assumes a_nat: "a N"
  assumes b_nat: "b N"
  assumes p1_nat: "p1 N"
  assumes p2_nat: "p2 N"
  shows " ¬ (is_valid_proof p1 ⟨Nil, (mk_eq a b)⟩ ∧ is_valid_proof p2 ⟨Nil, (mk_neq a b)⟩)"
