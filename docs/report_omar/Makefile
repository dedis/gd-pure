# Build the report.  XeLaTeX is required (the snippets are Unicode).
#
#   make            -- regenerate snippets, then build report.pdf
#   make snippets   -- re-extract the Isabelle snippets from ../../pure
#   make clean      -- remove build artifacts (keeps report.pdf)

LATEX  ?= xelatex
SRC     = report.tex preamble.tex $(wildcard sections/*.tex) $(wildcard snippets/*.thy)

report.pdf: snippets $(SRC)
	$(LATEX) -interaction=nonstopmode report.tex
	$(LATEX) -interaction=nonstopmode report.tex

.PHONY: snippets clean
snippets:
	bash extract.sh

clean:
	rm -f report.aux report.log report.out report.toc
