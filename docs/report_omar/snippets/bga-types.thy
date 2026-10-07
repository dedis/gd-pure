type_synonym tm  = num  (* BGA Term *)
type_synonym fm  = num  (* BGA Formula *)
type_synonym asn = num  (* Assignment *)
type_synonym dfn = num  (* Definition *)
type_synonym pf = num  (* Proof: List of judgements *)
type_synonym val = num  (* Evaluated Value *)

type_synonym hyp = num  (* Hypothesis: list/set of formulas *)
type_synonym jdg = num  (* Judgment: ⟨hyp, fm⟩ *)

abbreviation hyp_of :: "jdg ⇒ hyp" where "hyp_of J ≡ cpx J"
abbreviation conc_of :: "jdg ⇒ fm" where "conc_of J ≡ cpy J"

abbreviation mk_jdg :: "hyp ⇒ fm ⇒ jdg" (infix "⊩" 50)
  where "G ⊩ c ≡ ⟨G, c⟩"
abbreviation emptyH :: "hyp" ("∅")
  where "∅ ≡ Nil"
abbreviation cons  :: "fm ⇒ List ⇒ List" (infixr "▹" 65)
  where "f ▹ G ≡ Cons f G"
