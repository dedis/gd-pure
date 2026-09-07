theory GD_Hammer
  imports GD_Classical
  keywords "gd_hammer" :: diag
begin

text \<open>
  A relevance oracle for GD. \<^theory_text>\<open>gd_hammer\<close> translates the current goal and the
  \<open>[auto]\<close>/\<open>[cond]\<close> fact pool into first-order logic, runs E, and reports which
  facts the proof used. The proof itself is discarded --- the answer is a list
  of lemma names to try, and the kernel still checks whatever you replay, so a
  lossy translation costs at most a bad suggestion.

  The translation is classical, hence faithful on the decided fragment (see
  \<open>GD_Classical.thy\<close>). Two consequences worth knowing: \<open>p B\<close> becomes \<open>$true\<close>,
  so B-plumbing lemmas never appear in a suggestion even when the replay needs
  them; and \<open>a = b\<close> becomes \<open>gnat(a) & a = b\<close>, so the prover gets native
  equality while groundedness stays tracked.
\<close>

ML_file \<open>gd_hammer.ML\<close>

end
