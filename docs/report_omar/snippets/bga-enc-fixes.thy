locale bga_encoding =
  (*Term Encoding *)
  (* Tag of the current Constructor *)
  fixes tag_T :: "tm ⇒ tmtag"
  (* Encoding of the argument *)
  fixes load_T :: "tm ⇒ tm"
  (* Encodes the term *)
  fixes pack_T :: "tmtag ⇒ tm ⇒ tm"

  (* Formula Encoding *)
  fixes tag_F :: "fm ⇒ fmtag"
  fixes load_F :: "fm ⇒ tm"
  fixes pack_F :: "fmtag ⇒ fm ⇒ fm"

(* Fixing Definition*)
  fixes fresh_T :: "num ⇒ tm ⇒ o"
  fixes fresh_F :: "num ⇒ fm ⇒ o"
  fixes fresh_H :: "num ⇒ hyp ⇒ o"

  assumes fresh_T_def:
    "fresh_T k t :=
       if tag_T t = T_VAR then load_T t < k = 1
       else if tag_T t = T_ZERO then True
       else if tag_T t = T_SUC then fresh_T k (load_T t)
       else if tag_T t = T_PRED then fresh_T k (load_T t)
       else if tag_T t = T_IFZ then
         fresh_T k (cpx (load_T t)) ∧
         fresh_T k (cpx (cpy (load_T t))) ∧
         fresh_T k (cpy (cpy (load_T t)))
       else if tag_T t = T_APP then
         fresh_T k (cpx (cpy (load_T t))) ∧
         fresh_T k (cpy (cpy (load_T t)))
       else False"
  assumes fresh_F_def: "fresh_F k f := fresh_T k (cpx (load_F f)) ∧ fresh_T k (cpy (load_F f))"
  assumes fresh_H_def: "fresh_H k G := if G = Nil then True else fresh_F k (list_hd G) ∧ fresh_H k (list_tl G)"
