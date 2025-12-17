## Makefile for paper

BIBFILES =yao.bib ref.bib
TEXS =paper.tex intro.tex motivating-example.tex translation.tex equiv.tex case-study.tex directives.tex appendix.tex related-work.tex limitations.tex

TOP=paper
PDFS=paper.pdf 

all: $(TOP).pdf
main: $(TOP).pdf

paper.pdf : $(TEXS) $(BIBFILES) lstcoq.sty
	latexmk -shell-escape -bibtex -pdf paper.tex

paperclean:
	rm -if *.log ./*~ *.aux $(PDFS) *.bbl *.blg *.fdb_latexmk *.fls *.out

clean: paperclean
