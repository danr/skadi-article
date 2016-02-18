Paper.pdf : Paper.tex Paper.bbl
	pdflatex Paper.tex && ( grep -s "Rerun to get" Paper.log && pdflatex Paper.tex || true )

Paper.tex : Paper.lhs Abstract.lhs Introduction.lhs Content.lhs ExamplesExperiments.lhs RelatedWork.lhs DiscussionConclusion.lhs
	lhs2TeX Paper.lhs > Paper.tex

Paper.aux : Paper.tex
	pdflatex Paper.tex

Paper.bbl : Paper.aux Paper.bib
	bibtex Paper
