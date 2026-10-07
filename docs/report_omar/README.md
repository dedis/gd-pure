# Self-consistency report

LaTeX source of *Self-Consistency of Basic Grounded Arithmetic*: the QGA
axiomatization (`pure/GD.thy`), the arithmetization of BGA over it
(`pure/BGA_on_GA.thy`), an outline of the consistency proof, and the concrete
encoding that instantiates it (`pure/encode.thy`).

```
report.tex               main document
preamble.tex             fonts, snippet setup, theorem and rule macros
sections/01-qga.tex      QGA rules and definitions
sections/02-bga.tex      BGA arithmetized, proof rules, checker
sections/03-proof.tex    outline of the consistency proof
sections/04-encode.tex   the concrete encoding
sections/05-reduction.tex  reduction of QGA to BGA (to be written)
snippets/*.thy           Isabelle snippets, GENERATED, do not edit by hand
extract.sh               regenerates snippets/ from ../../pure
```

## Building

```
make            # bash extract.sh, then xelatex twice
```

XeLaTeX or LuaLaTeX is required, since the snippets are Unicode. pdfLaTeX
cannot build this document at all. Editors normally invoke
`latexmk -pdf`, which means pdflatex, so `.latexmkrc` in this directory
redirects that engine name to xelatex; build-on-save then works with no
editor configuration. If latexmk has already failed once it remembers the
failure, so run `latexmk -C` (or delete `report.fdb_latexmk`) after changing
engines.

Fonts: TeX
Gyre Pagella for text and math, DejaVu Sans Mono for snippets, DejaVu Sans for
three glyphs missing from DejaVu Sans Mono. If Isabelle's own
`Isabelle DejaVu Sans Mono` is installed, pointing `\isafont` at it in
`preamble.tex` makes that fallback unnecessary.

## Snippets

`extract.sh` pulls each quoted block out of the theory files by start and end
regex, strips CRs, and rewrites Isabelle's ASCII escapes (`\<Longrightarrow>`
and friends) as Unicode. It fails loudly when a pattern stops matching, so
editing the theories breaks the build instead of silently leaving the report
stale. Patterns are written against the raw sources, that is, with the ASCII
escapes rather than the Unicode.

Snippets are typeset with `fancyvrb` rather than `listings`. `listings`
reorders characters above U+00FF that sit next to ASCII (it renders `⟦a N⟧ ⟹`
as `⟦a ⟧N ⟹`) and its `literate` key never fires for those characters under
XeTeX. Character fidelity matters more here than keyword colouring.
