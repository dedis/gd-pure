lemma cpx_proj [simp]: "a N ⟹ b N ⟹ cpx ⟨a, b⟩ = a"
apply (rule conjE1)
apply (rule cpx_cpy_proj)
apply (assumption)+
done

(* separated lemma for cpy*)
lemma cpy_proj [simp]: "a N ⟹ b N ⟹ cpy ⟨a, b⟩ = b"
