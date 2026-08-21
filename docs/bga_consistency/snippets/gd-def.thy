  def :: ‹'a ⇒ 'a ⇒ o› (infix ‹:=› 10)
where
  defE: ‹⟦a := b; Q b⟧ ⟹ Q a› and
  defI: ‹⟦a := b; Q a⟧ ⟹ Q b›
