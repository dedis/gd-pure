  asn_put_def: "asn_put A i v :=
      if i = 0 then
        if A = Nil then v ▹ Nil
        else v ▹ list_tl A
      else if A = Nil then 0 ▹ asn_put Nil (i - 1) v
      else list_hd A ▹ asn_put (list_tl A) (i - 1) v" and
