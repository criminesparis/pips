# $Id: Makefile 23372 2017-05-05 15:35:30Z lossing $
#
# Copyright 1989-2016 MINES ParisTech
#
# This file is part of PIPS.
#
# PIPS is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# any later version.
#
# PIPS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.
#
# See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with PIPS.  If not, see <http://www.gnu.org/licenses/>.
#

ROOT    = ../../..

# unused: dcdg.tex

use_pdflatex	= 1

include newgen.mk

SOURCES = $(F_tex) unstructured.idraw newgen_domain.sty optimizer.tex

# Install in a newgen subdirectory:
HTM.subd = newgen
DOC.subd = newgen


ALLHS =	all_newgen_headers.h specs.h

INSTALL_INC=	$(F_h) $(F_newgen) $(F_c) $(F_spec) $(ALLHS)
INSTALL_DOC=	$(F_newgen:%.newgen=%.pdf)
INSTALL_HTM=	$(F_tex:%.tex=%.htdoc)

all: $(ALLHS) $(INSTALL_DOC)

dvi: $(F_newgen:%.newgen=%.dvi)
pdf: $(F_newgen:%.newgen=%.pdf)
newgen: $(F_newgen)
allhs: $(ALLHS)

%.newgen: %.tex
	$(RM) $@
	./remove-latex-comments $<
	chmod a-w $@

ri.pdf: unstructured.pdf

all_newgen_headers.h: specs.h
	#
	# building $@ (ordered as specs.h!)
	#
	$(RM) $@
	sed -n 's,^\(.*\)_spec.*,#include "\1.h",p' $< > $@
	chmod a+r-w $@

ENV.ng = \
	PATH=$$PATH:$(EXE.d):$(BIN.d) \
	LD_LIBRARY_PATH=$(NEWGEN_ROOT)/lib/$(ARCH):$(NEWGEN_ROOT)/lib:$$LD_LIBRARY_PATH

specs.def $(F_spec): $(F_newgen)
	$(ENV.ng) newgen -c $(F_newgen) > $@ || $(RM) $@

specs.h: specs.def
	#
	# building specs.h
	#
	make_all_specs < $< > $@

lisp_internal_representation: $(F_newgen)
	#
	# building $@
	#
	$(ENV.ng) newgen -lisp $(F_newgen)
	touch $@

clean: local-clean

local-clean:
	$(RM) $(INSTALL_INC) $(F_newgen) $(F_cl)
	$(RM) *.dvi *.ind *.log *.ps *.pdf *.aux *.idx *.ilg *.toc *.out *.brf *.bbl *.blg
	$(RM) -r $(INSTALL_HTM) ri.html dg.html specs.def


# what to do depending on phases
phase1: allhs

# common stuff
include $(ROOT)/makes/main.mk
