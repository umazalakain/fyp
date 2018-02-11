OUT=latex
AGDA=agda
STY=agda
AFLAGS=-i. --latex --latex-dir=$(OUT)
SOURCE=report
BIBLIOGRAPHY=bibliography
POSTPROCESS=postprocess-latex.pl
COMPILER=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'

report.pdf: report.lagda bibliography.bib
	mkdir -p $(OUT)
	cp $(BIBLIOGRAPHY).bib $(OUT)
	cp $(STY).sty $(OUT)
	$(AGDA) $(AFLAGS) $(SOURCE).lagda
	cd $(OUT) && \
                 perl ../$(POSTPROCESS) $(SOURCE).tex > $(SOURCE).processed && \
                 mv $(SOURCE).processed $(SOURCE).tex && \
	$(COMPILER) $(SOURCE).tex && \
                 mv $(SOURCE).pdf ..

clean:
	rm $(SOURCE).pdf
	rm -r $(OUT)
