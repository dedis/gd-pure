// =====================================================
// This file contains styling constructs.
// =====================================================

#let definition-box(title, body) = {
  block(
    fill: luma(240),
    inset: 10pt,
    radius: 4pt,
    width: 100%,
    {
      if title != none {
        text(weight: "bold", title)
      }
      body
    }
  )
}

