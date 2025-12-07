## Makefile for paper

BIBFILES =yao.bib ref.bib
TEXS =paper.tex equiv.tex directives.tex appendix.tex translation.tex

TOP=paper
PDFS=paper.pdf 

all: $(TOP).pdf
main: $(TOP).pdf

paper.pdf : $(TEXS) $(BIBFILES) lstcoq.sty
	latexmk -shell-escape -bibtex -pdf paper.tex

paperclean:
	rm -if *.log ./*~ *.aux $(PDFS) *.bbl *.blg *.fdb_latexmk *.fls *.out

clean: paperclean
