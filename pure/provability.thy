theory provability
  imports BGA_on_GA
begin

context bga_full
begin

(* Provability of a closed formula: some proof p certifies \<langle>Nil, c\<rangle>. *)
definition Bew :: "fm \<Rightarrow> o" where
  "Bew c \<equiv> \<exists>p. is_valid_proof p \<langle>Nil, c\<rangle>"

lemma Bew_I:
  assumes p_nat: "p N"
  assumes valid: "is_valid_proof p \<langle>Nil, c\<rangle>"
  shows "Bew c"
  unfolding Bew_def
  using valid by (rule existsI[OF p_nat])

lemma Bew_consistent:
  assumes a_nat: "a N" and b_nat: "b N"
  assumes eq_prov:  "Bew (mk_eq a b)"
  assumes neq_prov: "Bew (mk_neq a b)"
  shows False
proof -
  from eq_prov[unfolded Bew_def] obtain p1
    where p1_nat: "p1 N" and p1_valid: "is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle>"
    by (rule existsE)
  from neq_prov[unfolded Bew_def] obtain p2
    where p2_nat: "p2 N" and p2_valid: "is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>"
    by (rule existsE)
  show False
  proof (rule exF)
    show "is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>"
      using p1_valid p2_valid by (rule conjI)
    show "\<not> (is_valid_proof p1 \<langle>Nil, mk_eq a b\<rangle> \<and> is_valid_proof p2 \<langle>Nil, mk_neq a b\<rangle>)"
      using a_nat b_nat p1_nat p2_nat by (rule syntactically_consistent)
  qed
qed

end

end