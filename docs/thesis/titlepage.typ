// =====================================================
// This file constructs the title page.
// =====================================================

#let consecutive-line-spacing = 0.6em

#let title-page(
  title: none,
  thesistype: none,
  author: none,
  email: none,
  supervisors: none,
  institute: none,
  image-left: none,
  image-right: none,
  date: none
) = {
  set align(center)
  
  let logo-row = grid(
    columns: (1fr, 1fr),
    align(left)[#image-left],
    align(right)[#image-right]
  )

  let title-block = stack(
    spacing: 1.0em,
    text(17pt, weight: "bold")[#title],
    text(12pt)[#thesistype],
  )

  let author-block = stack(
    spacing: consecutive-line-spacing,
    author,
    email,
  )

  let institute-block = stack(
    spacing: consecutive-line-spacing,
    ..institute
  )

  let supervisor-block = stack(
    spacing: consecutive-line-spacing,
    [*Supervisors*:],
    ..supervisors
  )

  stack(
    dir: ttb,
    logo-row,
    v(2fr),
    title-block,
    v(1fr),
    author-block,
    v(1fr),
    institute-block,
    v(1.5fr),
    supervisor-block,
    v(0.5fr),
    [#date.display("30.09.2025")],
  )
}
