  assumes pack_F_N: "⟦t N; L N⟧ ⟹ pack_F t L N"
  assumes tag_F_N:  "f N ⟹ tag_F f N"
  assumes load_F_N: "f N ⟹ load_F f N"

  assumes pack_T_N: "⟦t N; L N⟧ ⟹ (pack_T t L) N"
  assumes tag_T_N:  "t N ⟹ tag_T t N"
  assumes load_T_N: "t N ⟹ load_T t N"

  (*Injective *)
  assumes tag_pack_F:  "⟦t N; L N⟧ ⟹ tag_F (pack_F t L) = t"
  assumes load_pack_F: "⟦t N; L N⟧ ⟹ load_F (pack_F t L) = L"
  
  assumes tag_pack_T:  "⟦t N; L N⟧ ⟹ tag_T (pack_T t L) = t"
  assumes load_pack_T: "⟦t N; L N⟧ ⟹ load_T (pack_T t L) = L"

  (*Surjective *)
  assumes pack_tag_F:  "f N ⟹ pack_F (tag_F f) (load_F f) = f"
  assumes pack_tag_T:  "t N ⟹ pack_T (tag_T t) (load_T t) = t"

  (*Structural Decrease (For Induction) *)
  (* This will require load of atomic terms(without arguments) to return 0 *)
  assumes decrease_F: "⟦f N; f ≠ 0 ⟧ ⟹ load_F f < f = 1"
  assumes decrease_T: "⟦t N; t ≠ 0⟧ ⟹ load_T t < t = 1"

  assumes tag_T_zero: "tag_T 0 = T_ZERO"

  (*Monotone assumptions for Bounding *)
  assumes mono_pack_T: "⟦tg N; x N; y N; x ≤ y = 1⟧ ⟹ (pack_T tg x ≤ pack_T tg y = 1)"
  assumes mono_pack_F: "⟦tg N; x N; y N; x ≤ y = 1⟧ ⟹ (pack_F tg x ≤ pack_F tg y = 1)"
