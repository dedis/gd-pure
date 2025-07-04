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
  set page(numbering: none)
  set align(center)
  
  let logo-row = grid(
    columns: (1fr, 1fr),
    align(left)[#image-left],
    align(right)[#image-right]
  )

  let title-block = stack(
    spacing: 1.5em,
    text(16pt, weight: "bold")[#title],
    text(12pt)[#thesistype],
  )

  let author-block = stack(
    spacing: 0.5em,
    author,
    email,
  )

  let supervisor-block = stack(
    spacing: 0.6em,
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
    institute,
    v(1.5fr),
    supervisor-block,
    v(1em),
    date,
  )
}
