%.dvi:   %.tex book.def
	amstex $<

getall: textsources tablesources

textsources: book.def contents.tex chapter1.tex chapter2.tex examples.tex \
		chapter3.tex chapter4.tex biblio.tex

tablesources:  book.def table1source table2source table3source table4source
table1source:  table1.tex table1.def table1.dat
table2source:  table2.tex table2.dat
table3source:  table3.tex table3.dat
table4source:  table4.tex table4.dat
table5source:  table5.tex table5.dat

chapter1: chapter1.dvi
chapter2: chapter2.dvi
chapter3: chapter3.dvi
chapter4: chapter4.dvi
biblio: biblio.dvi
contents: contents.dvi
examples: examples.dvi

table1: table1.tex table1.def table1.dat book.def
	amstex table1

table2: table2.tex table2.dat book.def
	amstex table2

table3: table3.tex table3.dat book.def
	amstex table3

table4: table4.tex table4.dat book.def
	amstex table4

table5: table5.tex table5.dat book.def
	amstex table5

tables: table1 table2 table3 table4 table5 addenda

text: contents chapter1 chapter2 examples chapter3 biblio errata

errata.dvi: errata.tex
	tex errata

errata: errata.dvi errata.doc

addenda: addenda.dvi addenda.doc

all: text tables

DVIFILES = biblio.dvi chapter1.dvi chapter2.dvi chapter3.dvi chapter4.dvi \
          contents.dvi errata.dvi examples.dvi table1.dvi table2.dvi \
          table3.dvi table4.dvi table5.dvi

PSFILES = biblio.ps chapter1.ps chapter2.ps chapter3.ps chapter4.ps \
          contents.ps errata.ps examples.ps table1.ps table2.ps \
          table3.ps table4.ps table5.ps

PDFFILES = biblio.pdf chapter1.pdf chapter2.pdf chapter3.pdf chapter4.pdf \
          contents.pdf errata.pdf examples.pdf table1.pdf table2.pdf \
          table3.pdf table4.pdf table5.pdf

RES = -D600

%.ps:	%.dvi
	dvips $(RES)  -Z* -t a4 -P pdf $<

%.pdf:	%.ps
	ps2pdf $<

chapter1.ps: chapter1.dvi
	dvips $(RES) -Z* -t a4 -P pdf -O 0.0in,-0.4in chapter1.dvi

chapter2.ps: chapter2.dvi
	dvips $(RES) -Z* -t a4 -P pdf -O 0.0in,-0.4in chapter2.dvi

chapter3.ps: chapter3.dvi
	dvips $(RES) -Z* -t a4 -P pdf -O 0.0in,-0.4in chapter3.dvi

chapter4.ps: chapter4.dvi
	dvips $(RES) -Z* -t a4 -P pdf -O 0.0in,-0.4in chapter4.dvi

examples.ps: examples.dvi
	dvips $(RES) -Z* -t a4 -P pdf -O 0.0in,-0.4in examples.dvi

contents.ps: contents.dvi
	dvips $(RES) -Z* -t a4 -P pdf -O 0.0in,-0.4in contents.dvi

biblio.ps: biblio.dvi
	dvips $(RES) -Z* -t a4 -P pdf -O 0.0in,-0.4in biblio.dvi

table1.ps: table1.dvi
	dvips $(RES) -Z* -t a4 -P pdf table1.dvi

table2.ps: table2.dvi
	dvips $(RES) -Z* -t a4 -P pdf table2.dvi

table3.ps: table3.dvi
	dvips $(RES) -Z* -t a4 -P pdf table3.dvi

table4.ps: table4.dvi
	dvips $(RES) -Z* -t a4 -P pdf table4.dvi

table5.ps: table5.dvi
	dvips $(RES) -Z* -t a4 -P pdf table5.dvi

allps: $(PSFILES)

allpdf: $(PDFFILES)

clean: 
	rm -f *.dvi *.ps *.pdf *.log *~
	rcsclean
#	sccs clean


