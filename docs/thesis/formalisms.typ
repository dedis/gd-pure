// =====================================================
// This file contains all formalisms, definitions,
// formulae and tables to clean up the main thesis.typ
// file.
// =====================================================

#import "@preview/ouset:0.2.0": ouset
#import "@preview/curryst:0.5.1": rule, prooftree
 
#let pred(n) = $#math.bold(math.upright("P"))\(#n\)$
#let suc(n) = $#math.bold(math.upright("S"))\(#n\)$
#let predf = $#math.bold(math.upright("P"))$
#let sucf = $#math.bold(math.upright("S"))$
#let judgment(body, font: "Roboto") = {
  text(font: font)[#body]
}
#let nat = { judgment("N") }
#let bool = { judgment("B") }
#let cond(c,a,b) = { $"if" #c "then" #a "else" #b$ }
#let ctxt(a) = { $K #h(0.3em) #a$ }
#let vec(a) = $accent(#a, arrow)$
#let to = $arrow.r.double$
#let impl = $arrow.r.double.long$

#let prems(sep: h(1.3em), ..premises) = {
  $
    #premises.pos().join(sep)
  $
}

#let prem(premise, ..assm) = {
  if (assm.pos().len() == 0) {
    $Gamma tack.r #premise$
  } else {
    $Gamma union {#assm.pos().join(", ")} tack.r #premise$
  }
}

#let deduction-rule(
  premise,
  conclusion,
  name,
  sym: false,
  spacing: 0.4em,
  line-sep: 2pt,
  thickness: 0.5pt,
) = context {
  let premise-width = measure(premise).width
  let conclusion-width = measure(conclusion).width
  let max-width = calc.max(premise-width, conclusion-width)
  let div = if sym {
    stack(
      spacing: line-sep,
      line(length: max-width, stroke: thickness),
      line(length: max-width, stroke: thickness)
    )
  } else {
    line(length: max-width, stroke: thickness)
  }
  let name-tag = if name == none {$$} else {$#h(1em) (#name)$}
  $
  #stack(
    spacing: spacing,
    premise,
    box(
      width: auto,
      div
    ),
    conclusion
  ) #name-tag
  $
}

#let pure-types = {
  grid(
    columns: (1.2fr, 1fr),
    align(left)[
      $ tau ::= &alpha \
            | &tau => tau \
            | &"prop"
      $
  ],
    align(left)[
      #set par(leading: 0.94em)
      type variable \
      function type \
      type of propositions \
    ])
}

#let pure-terms = { 
  grid(
    columns: (1.2fr, 1fr),
    align(left)[
      $ t ::= &x \
          | &c \
          | &t " " t \
          | &lambda x:: tau. t \
          | &t arrow.double.long t \ 
          | &t equiv t \ 
          | &and.big x:: tau. t \
      $
    ],
    align(left)[
      #set par(leading: 1em)
      variable \
      constant \
      application \
      lambda abstraction \
      implication \
      equality \
      universal quantification \
    ]
  )
}

#let pure-prime-types = {
  grid(
    columns: (1.1fr, 1fr),
    align(left)[
      $ tau ::= &alpha \
            | &tau => tau \
            | &"prop" \
            | &o
      $
  ],
    align(left)[
      #set par(leading: 0.94em)
      type variable \
      function type \
      type of propositions \
      type of object logic propositions \
    ])
}

#let pure-prime-terms = { 
  grid(
    columns: (1.1fr, 1fr),
    align(left)[
      $ t ::= &x \
          | &c \
          | &t " " t \
          | &lambda x:: tau. t \
          | &t arrow.double.long t \ 
          | &t equiv t \ 
          | &and.big x:: tau. t \
          | &"True" \
          | &t or t \
          | &"Trueprop" t 
      $
    ],
    align(left)[
      #set par(leading: 1em)
      variable \
      constant \
      application \
      lambda abstraction \
      implication \
      equality \
      universal quantification \
      `o`-typed true constant \
      `o`-typed logical or \
      conversion function `o` to `prop` \
    ]
  )
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
      $Gamma union {A} tack.r B$,
      $Gamma tack.r A arrow.double.long B$,
      $arrow.double.long I$
    )
  let implication-elim = deduction-rule(
      $Gamma_1 tack.r A arrow.double.long B #h(1.5em) Gamma_2 tack.r A$,
      $Gamma_1 union Gamma_2 tack.r B$,
      $arrow.double.long E$
  )

  grid(
    columns: (1fr, 1.1fr),
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
    columns: (1.4fr, 1fr),
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
      $equiv "prop"$
  )

  grid(
    columns: (1fr, 1fr, 1.7fr),
    row-gutter: 3em,
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

#let or-intro-rules = {
  let or-i1 = deduction-rule(
    $Gamma tack.r "Trueprop" P$,
    $Gamma tack.r "Trueprop" P or Q$,
    $"disjI1"$
  )

  let or-i2 = deduction-rule(
    $Gamma tack.r "Trueprop" Q$,
    $Gamma tack.r "Trueprop" P or Q$,
    $"disjI2"$
  )

  grid(
    columns: (1.3fr, 1fr),
    row-gutter: 3em,
    column-gutter: 5em,
    or-i1,
    or-i2
  )
}

#let true-axiom = deduction-rule(
  $$,
  $Gamma tack.r "Trueprop True"$,
  $"true"$
)

#let bga-term-syntax = {
  grid(
    columns: (1fr, 1fr),
    align(left)[
      $ t ::= & x          \
          |   & 0          \
          |   & suc(t)       \
          |   & pred(t)       \
          |   & not t      \
          |   & t or t     \
          |   & t = t      \
          |   & cond(t,t,t)\
          |   & d(t,...,t) \
      $
    ],
    align(left)[
      #set par(leading: 0.94em)
      variable \
      natural-number constant zero \
      natural-number successor \
      natural-number predecessor \
      logical negation \
      logical disjunction \
      natural-number equality \
      conditional evaluation \
      application of recursive definition \
    ]
  )
}

#let ga-term-syntax = {
  grid(
    columns: (1fr, 1fr),
    align(left)[
      $ t ::= & x          \
          |   & 0          \
          |   & suc(t)     \
          |   & pred(t)    \
          |   & not t      \
          |   & t or t     \
          |   & t = t      \
          |   & cond(t,t,t)\
          |   & d(t,...,t) \
          |   & forall x. t\
          |   & exists x. t\
      $
    ],
    align(left)[
      #set par(leading: 0.94em)
      variable \
      natural-number constant zero \
      natural-number successor \
      natural-number predecessor \
      logical negation \
      logical disjunction \
      natural-number equality \
      conditional evaluation \
      application of recursive definition \
      universal quantifier \
      existential quantifier \
    ]
  )
}

#let ga-definitional-shorthands = {
  grid(
    columns: (1.7fr, 1fr),
    align(center)[
      $
       "True"        &equiv 0 = 0                           \
       "False"       &equiv 0 = S(0)                        \
       a nat         &equiv a = a                           \
       p bool        &equiv p or not p                      \
       p and q       &equiv not (not p or not q)            \
       p arrow.r q   &equiv not p or q                      \
       p arrow.l.r q &equiv (p arrow.r q) and (q arrow.r p) \
       a eq.not b    &equiv not (a = b)                     \
      $
    ],
    align(left)[
      #set par(leading: 0.86em)
      true constant \
      false constant \
      number type    \
      boolean type \
      logical conjunction \
      implication \
      biconditional \
      inequality \
    ]
  )
}

#let bga-prop-logic-axioms = {
  let disjI1 = deduction-rule(
    prem($p$),
    prem($p or q$),
    $or "I1"$
  )
  let disjI2 = deduction-rule(
    prem($q$),
    prem($p or q$),
    $or "I2"$
  )
  let disjI3 = deduction-rule(
    prems(
      prem($not p$),
      prem($not q$),
    ),
    prem($not (p or q)$),
    $or "I3"$
  )
  let dNegIE = deduction-rule(
    prem($p$),
    prem($not not p$),
    $not not "IE"$,
    sym: true
  )
  let exF = deduction-rule(
    prems(
      prem($p$),
      prem($not p$),
    ),
    prem($q$),
    $not E$
  )
  let disjE1 = deduction-rule(
    prem($not (p or q)$),
    prem($not p$),
    $or "E1"$
  )
  let disjE2 = deduction-rule(
    prem($not (p or q)$),
    prem($not q$),
    $or "E2"$
  )
  let disjE3 = deduction-rule(
    prems(
      prem($p or q$),
      prem($r$, $p$),
      prem($r$, $q$)
    ),
    prem($r$),
    $or "E3"$
  )

  grid(
    columns: (1fr, 1fr, 1fr),
    row-gutter: 2em,
    disjI1,
    disjI2,
    disjI3,
    dNegIE,
    exF,
    disjE1,
    disjE2,
    grid.cell(
      colspan: 2,
      disjE3
    ),
  )
}

#let bga-nat-axioms = {
  let zeroI = deduction-rule(
    $$,
    prem($0 nat$),
    $0 I$
  )
  let sucIE = deduction-rule(
    prem($a=b$),
    prem($suc(a) = suc(b)$),
    $sucf=I E$,
    sym: true
  )
  let predI = deduction-rule(
    prem($a=b$),
    prem($pred(a) = pred(b)$),
    $predf=I$,
  )
  let sucNz = deduction-rule(
    prem($a nat$),
    prem($suc(a) eq.not 0$),
    $sucf eq.not 0I$
  )
  let predSucInv = deduction-rule(
    prem($a nat$),
    prem($pred(suc(a)) = a$),
    $predf=I 2$
  )
  let condI1 = deduction-rule(
    prems(
      prem($c$),
      prem($a nat$)
    ),
    prem($(cond(c,a,b)) = a$),
    $?I 1$
  )
  let condI2 = deduction-rule(
    prems(
      prem($not c$),
      prem($b nat$)
    ),
    prem($(cond(c,a,b)) = b$),
    $?I 2$
  )
  let induct = deduction-rule(
    prems(
      prem($ctxt(0)$),
      prem($ctxt(suc(x))$,
           $x nat$,
           $ctxt(x)$
      ),
      prem($a nat$)
    ),
    prem($ctxt(a)$),
    $"Ind"$
  )
  let eqNat = deduction-rule(
    prems(
      prem($a nat$),
      prem($b nat$),
    ),
    prem($a = b nat$),
    $="TI"$
  )
  let condT = deduction-rule(
    prems(
      prem($c bool$),
      prem($a nat$),
      prem($b nat$),
    ),
    prem($cond(c,a,b) nat$),
    $?"TI"$
  )

  grid(
    columns: (1fr, 0.9fr, 1fr),
    row-gutter: 2em,
    zeroI,
    sucIE,
    predI,
    predSucInv,
    sucNz,
    condI1,
    condI2,
    grid.cell(
      colspan: 2,
      induct
    ),
    eqNat,
    grid.cell(
      colspan: 2,
      condT
    ),
  )
}

#let bga-eq-axioms = {
  let eqSym = deduction-rule(
    prem($a = b$),
    prem($b = a$),
    $=S$
  )
  let eqSubst = deduction-rule(
    prems(
      prem($a = b$),
      prem($ctxt(a)$)
    ),
    prem($ctxt(b)$),
    $=E$ 
  )

  grid(
    columns: (1fr, 1fr),
    row-gutter: 2em,
    eqSym,
    eqSubst,
  )
}

#let bga-def-axioms = {
  let defE = deduction-rule(
    prems(
      prem($s(vec(x)) equiv d(vec(x))$),
      prem($ctxt(d(vec(a)))$)
    ),
    prem($ctxt(s(vec(a)))$),
    $equiv E$
  )
  let defI = deduction-rule(
    prems(
      prem($s(vec(x)) equiv d(vec(x))$),
      prem($ctxt(s(vec(a)))$)
    ),
    prem($ctxt(d(vec(a)))$),
    $equiv I$
  )

  grid(
    columns: (1fr, 1fr),
    row-gutter: 2em,
    defE,
    defI,
  )
}

#let structural-rules = {
  let H = deduction-rule(
    $$,
    prem($p$, $p$),
    "H"
  )
  let W = deduction-rule(
    prem($q$),
    prem($q$, $p$),
    "W"
  )
  grid(
    columns: (1fr, 1fr),
    row-gutter: 2em,
    H, W
  )
}

#let grounded-contradiction = deduction-rule(
  prems(
    prem($p bool$),
    prem($q$, $not p$),
    prem($not q$, $not p$),
  ),
  prem($p$),
  none
)

#let grounded-contradiction-deriv = rule(
  name: $or "E3"$,
  prem($p$),
  rule(
    name: $bool "def"$,
    prem($p or not p$),
    prem($p bool$)
  ),
  rule(
    name: "H",
    prem($p$, $p$)
  ),
  rule(
    name: $not E$,
    prem($p$, $not p$),
    prem($q$, $not p$),
    prem($not q$, $not p$),
  )
)

#let modus-ponens = deduction-rule(
  prems(
    prem($p$),
    prem($p arrow.r q$)
  ),
  prem($q$),
  $arrow.r E$
)

#let modus-ponens-deriv = rule(
  name: $or "E3"$,
  prem($q$),
  rule(
    name: "H",
    prem($q$, $q$)
  ),
  rule(
    name: $not E$,
    prem($q$, $not p$),
    rule(
      name: "H",
      prem($not p$, $not p$),
    ),
    rule(
      name: "W",
      prem($p$, $not p$),
      prem($p$),
    )
  ),
  rule(
    name: $arrow.r "def"$,
    prem($not p or q$),
    prem($p arrow.r q$)
  )
)

#let implI = deduction-rule(
  prems(
    prem($p bool$),
    prem($q$, $p$),
  ),
  prem($p arrow.r q$),
  $arrow.r I$
)

#let implI-deriv = rule(
  name: $arrow.r "def"$,
  prem($p arrow.r q$),
  rule(
    name: $or "E3"$,
    prem($not p or q$),
    rule(
      name: $bool "def"$,
      prem($p or not p$),
      prem($p bool$)
    ),
    rule(
      name: $or "E2"$,
      prem($not p or q$, $p$),
      prem($q$, $p$)
    ),
    rule(
      name: $or "I1"$,
      prem($not p or q$, $not p$),
      rule(
        name: "H",
        prem($not p$, $not p$)
      )
    )
  )
)

#let bga-quantifier-axioms = {
  let forallI = deduction-rule(
    prem($ctxt(x)$, $x nat$),
    prem($forall x. ctxt(x)$),
    $forall I$
  )
  let forallE = deduction-rule(
    prems(
      prem($forall x. ctxt(x)$),
      prem($a nat$),
    ),
    prem($ctxt(a)$),
    $forall E$
  )
  let existsI = deduction-rule(
    prems(
      prem($a nat$),
      prem($ctxt(a)$)
    ),
    prem($exists x. ctxt(x)$),
    $exists I$
  )
  let existsE = deduction-rule(
    prems(
      prem($exists x. ctxt(x)$),
      prem($q$, $x nat$, $ctxt(x)$)
    ),
    prem($q$),
    $exists E$
  )

  grid(
    columns: (1fr, 1fr),
    row-gutter: 2em,
    forallI,
    forallE,
    existsI,
    existsE,
  )
}

#let nat-deduct-rule = deduction-rule(
  prems(
    $Gamma union A_1 tack.r P_1$,
    $Gamma union A_2 tack.r P_2$,
    $...$,
    $Gamma union A_n tack.r P_n$,
  ),
  prem($C$),
  none
)

#let nat-typing-rules = {
  let natS = deduction-rule(
    prem($a nat$),
    prem($suc(a) nat$),
    $sucf nat$
  )
  let natP = deduction-rule(
    prem($a nat$),
    prem($pred(a) nat$),
    $predf nat$
  )
  
  grid(
    columns: (1fr, 1fr),
    row-gutter: 2em,
    natS,
    natP
  )
}

#let add-def = $"add" x " " y := cond(y = 0, x, suc("add" x pred(y)))$

#let not-less-zero = deduction-rule(
  none,
  prem($x < 0 = 0$),
  none
)

#let add-term = deduction-rule(
  prems(
    prem($x nat$),
    prem($y nat$),
  ),
  prem($x + y nat$),
  none
)

#let leq-term = deduction-rule(
  prems(
    prem($x nat$),
    prem($y nat$),
  ),
  prem($x <= y nat$),
  none
)

#let div-term = deduction-rule(
  prems(
    prem($x nat$),
    prem($y nat$),
  ),
  prem($"div" x " " y nat$),
  none
)

#let ack-term = deduction-rule(
  prems(
    prem($x nat$),
    prem($y nat$),
  ),
  prem($"ack" x " " y nat$),
  none
)

#let strong-induct = deduction-rule(
  prems(
    prem($a nat$),
    prem($ctxt(0)$),
    prem($ctxt(suc(x))$, $x nat$, $\{y nat, " " y <= x = 1\} tack.r ctxt(y))$)
  ),
  prem($ctxt(a)$),
  none
)

#let eq-reflection-axiom = deduction-rule(
  prem($a = b$),
  prem($a equiv b$),
  none  
)
