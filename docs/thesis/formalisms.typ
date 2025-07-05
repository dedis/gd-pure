// =====================================================
// This file contains all formalisms, definitions,
// formulae and tables to clean up the main thesis.typ
// file.
// =====================================================
#let deduction-rule(
  premise,
  conclusion,
  name
) = {
  $
  frac(
    premise,
    conclusion
  ) #h(1em) (name)
  $
}

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
      | &lambda x:: tau. t "(lambda abstraction)" \
      | &t arrow.double.long t "(implication)"\ 
      | &t equiv t "(equality)"\ 
      | &and.big x:: tau. t "(universal quantification)"
  $
}

#let pure-type-constructors = {
  $
  equiv ""&:: alpha => alpha => "prop"\
  arrow.double.long ""&:: "prop" => "prop" => "prop"\
  and.big ""&:: (alpha => "prop") => "prop"
  $
}

#let pure-implication-rules = {
  let implication-intro = deduction-rule(
      $Gamma union A tack.r B$,
      $Gamma tack.r A arrow.double.long B$,
      $arrow.double.long I$
    )

  let implication-elim = deduction-rule(
      $Gamma_1 tack.r A arrow.double.long B #h(1.5em) Gamma_2 tack.r A$,
      $Gamma_1 union Gamma_2 tack.r B$,
      $arrow.double.long E$
  )

  grid(
    columns: (1fr, 1.3fr),
    column-gutter: 6em,
    align: (left, right),
    implication-intro,
    implication-elim
  )
}

#let pure-forall-rules = {
  let universal-intro = $
    frac(
      Gamma tack.r B(x) #h(1.5em) x "not free in" Gamma,
      Gamma tack.r and.big x . B(x)
    ) #h(1em) (and.big I)
  $

  let universal-elim = $
    frac(
      Gamma tack.r and.big x . B(x),
      Gamma tack.r B(a)
    ) #h(1em) (and.big E)
  $

  grid(
    columns: (1.6fr, 1fr),
    column-gutter: 8em,
    align: left,
    universal-intro,
    universal-elim
  )
}

#let pure-basic-rules = {
  let axiom-rule = $
    frac(
      A "axiom",
      Gamma tack.r A
    ) #h(1em) ("Axiom")
  $

  let assumption-rule = $
    frac(
      A in Gamma,
      Gamma tack.r A 
    ) #h(1em) ("Ass")
  $

  grid(
    columns: (1fr, 1fr),
    column-gutter: 10em,
    axiom-rule,
    assumption-rule
  )
}

#let pure-equality-rules = {
  let reflexivity = $
    frac(
    #hide($Gamma$),
      Gamma tack.r a equiv a
    ) #h(1em) (equiv "Refl")
  $

  let symmetry = $
    frac(
      Gamma tack.r b equiv a,
      Gamma tack.r a equiv b
    ) #h(1em) (equiv "Sym")
  $

  let transitivity = $
    frac(
      Gamma tack.r a equiv b #h(1.5em) Gamma tack.r b equiv c,
      Gamma tack.r a equiv c
    ) #h(1em) (equiv "Trans")
  $

  let abstraction = $
    frac(
      Gamma tack.r a equiv b,
      Gamma tack.r (lambda x.a) equiv (lambda x.b)
    ) #h(1em) (equiv "Lam")
  $

  let application = deduction-rule(
     $Gamma tack.r a arrow.double.long b #h(1.5em) Gamma tack.r b arrow.double.long a$,
      $Gamma tack.r a equiv b$,
      $equiv "Prop"$
  )

  grid(
    columns: (1fr, 1fr, 1.6fr),
    row-gutter: 3em,
    column-gutter: 1em,
    reflexivity,
    symmetry,
    transitivity,
    grid.cell(
      colspan: 2,
      abstraction
    ),
    application
  )
}

#let pure-lambda-conversion-rules = {
  let alpha-conversion = deduction-rule(
    $"y not free in" a$,
    $Gamma tack.r (lambda x.a) equiv (lambda y.a[y\/x])$,
    $alpha"-Conv"$
  )

  let beta-conversion = deduction-rule(
    hide($Gamma$),
    $Gamma tack.r (lambda x.a) " " b equiv a[b\/x]$,
    $beta "-Conv"$
  )

  let extensionality = deduction-rule(
    $Gamma tack.r f " " x equiv g " " x #h(1.5em) "x not free in" Gamma, f, "and" g$,
    $Gamma tack.r f equiv g$,
    "Ext" )

  grid(
    columns: (1.3fr, 1fr),
    row-gutter: 3em,
    column-gutter: 5em,
    alpha-conversion,
    beta-conversion,
    grid.cell(extensionality, colspan: 2)
  )
}

#let equiv-elimination-rule = {
  deduction-rule(
    $Gamma tack.r a equiv b #h(1.5em) Gamma tack.r a$,
    $Gamma tack.r b$,
    $equiv E$
  )
}
