  cond :: ‹o ⇒ 'a ⇒ 'a ⇒ 'a› (‹if _ then _ else _› [25, 24, 24] 24)

axiomatization where
  condI1: ‹⟦c; a N⟧ ⟹ (if c then a else b) = a› and
  condI2: ‹⟦¬c; b N⟧ ⟹ (if c then a else b) = b› and
  (*condT: ‹⟦c B; a N; b N⟧ ⟹ if c then a else b N› and*)
  condI1B: ‹⟦c; d B⟧ ⟹ (if c then d else e) ⟷ d› and
  condI2B: ‹⟦¬c; e B⟧ ⟹ (if c then d else e) ⟷ e› and
  (*condTB: ‹⟦c B; d B; e B⟧ ⟹ if c then d else e B›*)
  (*New additions*)
  condE1: ‹⟦c;  (if c then a else b) N⟧ ⟹ (a N)› and
  condE2: ‹⟦¬c;  (if c then a else b) N⟧ ⟹ (b N)› and
  condE3: ‹⟦(if c then a else b) N⟧ ⟹ (c B)› and
  condE1B: ‹⟦c;  (if c then d else e) B⟧ ⟹ (d B)› and
  condE2B: ‹⟦¬c;  (if c then d else e) B⟧ ⟹ (e B)› and
  condE3B: ‹⟦(if c then d else e) B⟧ ⟹ (c B)› and
  (* lazy conditional rules *) 
  cond_thenQ_E: "c ⟹ Q (if c then a else b) ⟹ Q a" and
  cond_thenQ_I: "c ⟹ Q a ⟹ Q (if c then a else b)" and
  cond_elseQ_E: "¬ c ⟹ Q (if c then a else b) ⟹ Q b" and
  cond_elseQ_I: "¬ c ⟹ Q b ⟹ Q (if c then a else b)"
