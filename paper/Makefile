## Makefile for paper

BIBFILES =yao.bib ref.bib
TEXS =paper.tex intro.tex motivating-example.tex translation.tex equiv.tex case-study.tex directives.tex appendix.tex related-work.tex conclusion.tex
PAPER = paper
PAPERTEX = $(PAPER).tex
PAPERPDF = $(PAPER).pdf
DIFF_REVISION = flops-submission
DIFF = diff
DIFFTEX = $(DIFF).tex
DIFFPDF = $(DIFF).pdf

main: $(PAPERPDF)
all: $(PAPERPDF) $(DIFFPDF)

$(DIFFTEX): $(TEXS) $(BIBFILES)
	./latexdiff-vc -c latexdiff.cfg --flatten --git --force -r $(DIFF_REVISION) $(PAPERTEX)
	mv $(PAPER)-diff$(DIFF_REVISION).tex $@

%.pdf: %.tex $(TEXS) $(BIBFILES)
	latexmk -shell-escape -bibtex -pdf $<

clean:
	rm -if *.log ./*~ *.aux *.dvi *.pdf *.bbl *.blg *.fdb_latexmk *.fls *.out $(DIFFTEX)
