// =====================================================
// This file contains styling constructs.
// =====================================================

#import "@preview/curryst:0.5.1": rule, prooftree

#let definition-box(title, body, font_size: 1em) = {
  block(
    fill: luma(240),
    inset: 10pt,
    radius: 4pt,
    width: 100%,
    {
      if title != none {
        text(weight: "bold", title)
      }
      set text(size: font_size)
      body
    }
  )
}

#let tree(body) = {
  align(center)[
    #prooftree(body)
  ]
}

#let thm_cnt = counter("thm-cnt")

#let theorem(title, body, font_size: 1em) = context {
  thm_cnt.step()

  block(
    fill: luma(247),
    stroke: (left: 3pt + blue.darken(50%)),
    inset: 10pt,
    radius: 4pt,
    width: 100%,
    {
      text(weight: "bold", [Theorem #context thm_cnt.display(). ])
      text(style: "italic", [#title])
      set text(size: font_size)
      body
    }
  )
}

#let proof(body, name: [Proof.]) = {
  text(weight: "bold")[#name]
  v(0em)
  body
  h(1fr)
  $qed$
}
