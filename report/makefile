COMPILER=latexmk -pdf -use-make -e '$$pdflatex=q/xelatex %O %S/'

report.pdf: report.lagda bibliography.bib
	agda --latex report.lagda; \
	cd latex && \
	$(COMPILER) report.tex && \
                 mv report.pdf ..
