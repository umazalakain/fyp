OUT=latex
AGDA=agda
STY="agda.sty"
AFLAGS=-i. --latex --latex-dir=$(OUT)
COMPILER=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'

RESOURCES=bibliography.bib agda.sty chi.png
MODULES=Presburger.lagda Monoids.lagda Adaptation.lagda Normalisation.lagda CommutativeRings.lagda
MAIN=report
POSTPROCESS=postprocess-latex.pl

report.pdf: resources modules xetex

xetex: $(POSTPROCESS)
	$(AGDA) $(AFLAGS) $(MAIN).lagda
	cd $(OUT) && \
                 perl ../$(POSTPROCESS) $(MAIN).tex > $(MAIN).processed && \
                 mv $(MAIN).processed $(MAIN).tex && \
	$(COMPILER) $(MAIN).tex && \
                 mv $(MAIN).pdf ..

resources: $(RESOURCES)
	mkdir -p $(OUT)
	cp $(RESOURCES) $(OUT)

modules: $(MODULES)
	$(foreach module,$?,$(AGDA) $(AFLAGS) $(module);)

clean:
	rm -r $(OUT)
	rm $(MAIN).pdf
