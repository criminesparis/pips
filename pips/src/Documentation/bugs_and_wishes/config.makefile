# $Id: config.makefile 14268 2009-06-10 15:55:56Z coelho $

ETEX = 	pips_bugs.tex

SOURCES = $(ETEX)

DVI = $(ETEX:.tex=.dvi)
PS = $(DVI:.dvi=.ps)

INSTALL_DOC= $(PS)

all: $(PS)
dvi: $(DVI)
ps: $(PS)

clean: local-clean
local-clean:
	$(RM) $(DVI) $(PS)
