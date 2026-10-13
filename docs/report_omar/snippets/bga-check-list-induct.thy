lemma check_list_induct_N:
  assumes pf: "pf N"
      and base: "⋀J A. A N ⟹ check_list Nil ⟹ J N ⟹ mem J Nil ⟹
                   sat_hyp (hyp_of J) A ⟹ sat (conc_of J) A"
      and step: "⋀h t. h N ⟹ t N ⟹
                   (⋀J A. A N ⟹ check_list t ⟹ J N ⟹ mem J t ⟹
                      sat_hyp (hyp_of J) A ⟹ sat (conc_of J) A) ⟹
                   (⋀J A. A N ⟹ check_list (Cons h t) ⟹
                      J N ⟹ mem J (Cons h t) ⟹
                      sat_hyp (hyp_of J) A ⟹ sat (conc_of J) A)"
  shows "⋀J A. A N ⟹ check_list pf ⟹ J N ⟹ mem J pf ⟹
                sat_hyp (hyp_of J) A ⟹ sat (conc_of J) A"
