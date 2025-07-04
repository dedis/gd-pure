// =====================================================
// This file contains all formalisms, definitions,
// formulae and tables to clean up the main thesis.typ
// file.
// =====================================================

#let pure-types = {
  $ tau ::= &alpha "(type variable)" \
        | &tau => tau "(function type)"\
        | &"prop" "(type of propositions)"
  $
}

#let pure-terms = { 
  $ t ::= &x "(variable)" \
      | &c "(constant)" \
      | &t " " t "(application)" \
      | &lambda x: tau. t "(lambda abstraction)" \
      | &t arrow.double.long t "(ipmlication)"\ 
      | &t equiv t "(equality)"\ 
      | &Lambda x: tau. t "(universal quantification)"
  $
}

#let pure-implication-rules = {
  let tall-implication-premise = stack(dir: ttb, spacing: 0.4em, [$[phi]$], [$psi$], v(0.3em))

  let implication-intro = $
    frac(
      #tall-implication-premise,
      phi arrow.double.long psi
    ) #h(1em) (arrow.double.long I)
  $


  let implication-elim = $
    frac(
      phi arrow.double.long psi #h(2em) phi #hide(tall-implication-premise),
      psi
    ) #h(1em) (arrow.double.long E)
  $

  set align(center)

  grid(
    columns: (1fr, 1fr),
    column-gutter: 10em,
    row-gutter: 4em,
    implication-intro,
    implication-elim
  )
}

#let pure-forall-rules = {
  let universal-intro = $
    frac(
      phi[x],
      and.big x . phi[x]
    )* #h(1em) (forall I)
  $

  let universal-elim = $
    frac(
      and.big x . phi[x],
      phi[t]
    ) #h(1em) (forall E)
  $

  set align(center)

  grid(
    columns: (1fr, 1fr),
    column-gutter: 10em,
    row-gutter: 4em,
    universal-intro,
    universal-elim
  )

  v(1em)

  [\* The variable `x` must not be free in the assumptions.]
}
