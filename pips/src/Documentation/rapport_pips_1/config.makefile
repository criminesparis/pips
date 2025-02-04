# $Id: config.makefile 14268 2009-06-10 15:55:56Z coelho $

SOURCES=analyses.ftex \
	benchmarks.ftex \
	bibliographie.ftex \
	conclusion.ftex \
	hierarchie.ftex \
	interfaces.ftex \
	introduction.ftex \
	newgen.ftex \
	presentation.ftex \
	rapport.ftex \
	structures.ftex \
	transformations.ftex \
	utilitaires.ftex

dvi: rapport.dvi

clean: local-clean
local-clean:
	$(RM) rapport.dvi
