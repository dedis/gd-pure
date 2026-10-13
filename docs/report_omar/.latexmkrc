# This document requires XeLaTeX (fontspec, unicode-math, Unicode snippets).
# Editors and latexmk default to pdflatex, so route that engine name to
# xelatex; this works even when latexmk is invoked with -pdf.
$pdf_mode  = 5;
$pdflatex  = 'xelatex -synctex=1 -interaction=nonstopmode -file-line-error %O %S';
$xelatex   = 'xelatex -synctex=1 -interaction=nonstopmode -file-line-error %O %S';
$clean_ext = 'synctex.gz run.xml bbl fdb_latexmk fls';
