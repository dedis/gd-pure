definition swap01 :: "num ⇒ num" where
  "swap01 t ≡ if t = 0 then 1 else if t = 1 then 0 else t"

definition tag_T  :: "tm ⇒ tmtag"        where "tag_T  n    ≡ swap01 (cpx n)"
definition load_T :: "tm ⇒ tm"           where "load_T n    ≡ cpy n"
definition pack_T :: "tmtag ⇒ tm ⇒ tm"   where "pack_T tg L ≡ ⟨swap01 tg, L⟩"
definition tag_F  :: "fm ⇒ fmtag"        where "tag_F  n    ≡ cpx n"
definition load_F :: "fm ⇒ tm"           where "load_F n    ≡ cpy n"
definition pack_F :: "fmtag ⇒ fm ⇒ fm"   where "pack_F tg L ≡ ⟨tg, L⟩"
