# $Id: Makefile 23065 2016-03-02 09:05:50Z coelho $
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

use_pdflatex	= 1

SOURCES =	pipsmake-rc.tex \
		make-pips-menu \
		make-builder-map \
		generate_all_menu_documentation \
		user-and-source-files.idraw

INSTALL_ETC =	epips_view_menu_layout.el \
		epips_transform_menu_layout.el \
		pipsmake.rc \
		properties.rc \
		properties-2009-10-31.rc \
		pipsdep.rc \
		wpips.rc

DERIVED_INC =	resources.h \
		pips-libs.h \
		printable_resources.h \
		phases.h \
		builder_map.h \
		wpips_transform_menu_layout.h \
		wpips_view_menu_layout.h

INSTALL_INC =	$(DERIVED_INC)
INSTALL_DOC =	pipsmake-rc.pdf
INSTALL_HTM =	pipsmake-rc.htdoc
# Hide the PDF into the HTML documentation directory
DOC.subd = $(INSTALL_HTM)

DERIVED_FILES=	$(INSTALL_ETC) $(DERIVED_INC) $(INSTALL_DOC)

all: $(DERIVED_FILES)

# the documentation must generate its derived headers as soon as possible
# because it is expected to compute the dependencies of some librairies
# especially Passes/tpips
phase0: .build_inc .build_etc

# skip latex 2 html if needed:
simple: $(DERIVED_INC) $(INSTALL_ETC) $(INSTALL_DOC)
simpleinstall: simple; $(MAKE) INSTALL_HTM= install

pipsmake.full	= ./pipsmake-filter.pl --makes
pipsmake.flt	= ./pipsmake-filter.pl --makes
pipsprop.flt	= ./pipsmake-filter.pl --props
alias.flt	= ./pipsmake-filter.pl --alias

ifdef PIPS_SPECIAL
pipsmake.flt	+= --subset=$(PIPS_SPECIAL).conf
alias.flt	+= --subset=$(PIPS_SPECIAL).conf
endif # PIPS_SPECIAL

pipsmake.rc: pipsmake-rc.tex
	#
	# building $@
	#
	$(pipsmake.flt) $< > $@

properties.rc: pipsmake-rc.tex
	#
	# building $@
	#
	{ \
	  if [ "$(PIPS_SPECIAL)" ] ; then \
	    echo 'PIPS_VERSION "$(PIPS_SPECIAL)"' ; \
	  else \
	    echo 'PIPS_VERSION "full"' ; \
	  fi ; \
	  $(pipsprop.flt) $< ; \
	} > $@

properties-2009-10-31.rc: properties-2009-10-31.rc.model
	#
	# building $@
	#
	cp properties-2009-10-31.rc.model properties-2009-10-31.rc

pipsdep.rc: pipspassdep.pl pipsmake-rc.tex
	#
	# buidling $@
	#
	./$^ > $@

wpips.rc: pipsmake-rc.tex
	#
	# buidling $@
	#
	$(alias.flt) $< > $@

ifdef PIPS_SPECIAL
# PIPS_SPECIAL issue:
# some libraries still need many DBR definition,
# even if they are not really used...
resources.h: pipsmake-rc.tex
	#
	# building full $@
	#
	{ \
	  echo "// pips generated resources" ; \
	  $(pipsmake.full) $< | sed -f resources.sed | \
	  $(UPPER) | sort -u | sed 's/.*/#define DBR_& "&"/' ; \
	} > $@

pips-libs.h: $(PIPS_SPECIAL).libs
	#
	# building $@
	#
	{ \
	  echo "// pips libraries used by this built" ; \
	  for lib in $$(cat $(PIPS_SPECIAL).libs | tr '-' '_') ; do \
	    echo "#define HAVE_PIPS_$${lib}_LIBRARY" ; \
	  done ; \
	} > $@

else
resources.h: pipsmake.rc
	#
	# building $@
	#
	{ \
	  echo "// pips generated resources" ; \
	  sed -f resources.sed $< | \
	  $(UPPER) | sort -u | sed 's/.*/#define DBR_& "&"/' ; \
	} > $@

pips-libs.h: all.libs
	#
	# building $@
	#
	{ \
	  echo "// pips libraries used by this built" ; \
	  for lib in $$(cat all.libs | tr '-' '_') ; do \
	    echo "#define HAVE_PIPS_$${lib}_LIBRARY" ; \
	  done ; \
	} > $@
endif # PIPS_SPECIAL

printable_resources.h: resources.h
	#
	# building $@
	#
	sed '/define.*FILE/!d' $< > $@

phases.h: pipsmake.rc
	#
	# building $@
	#
	# The -u option for sort hides redeclared phases
	sed '/^[a-z]/!d;s/ .*//g;' $< | tr '[a-z]' '[A-Z]' | sort -u | \
	sed 's/.*/#define BUILDER_& "&"/' > $@

builder_map.h: pipsmake.rc
	#
	# building builder_map.h
	#
	./make-builder-map < $< > $@

#
# specialized pips generation
#

all.conf: pipsmake-rc.tex
	$(pipsmake.full) $< | grep '^[a-z]' | cut -d' ' -f1 | sort > $@

%.deps: %.conf
	./pass2lib.sh $< > $@

%.libs: %.deps %.conf
	./pass2libs.pl $^ > $@

epips_transform_menu_layout.el wpips_transform_menu_layout.h epips_view_menu_layout.el wpips_view_menu_layout.h:  pipsmake-rc.tex generate_all_menu_documentation
	#
	# building menu layout files:
	#
	./generate_all_menu_documentation -layout < $<

headers: $(DERIVED_INC)

pipsmake-rc.pdf: user-and-source-files.pdf
pipsmake-rc.dvi: user-and-source-files.eps

clean: local-clean

check: pispmake-rc.tex
	@echo "missing properties label:"
	pdflatex pipsmake-rc.tex 2>&1 | grep 'LaTeX Warning: Reference' | grep -E -o "prop:[^']+" | cut -d ':' -f 2


local-clean:
	$(RM) -r $(DERIVED_FILES) pipsmake-rc.htdoc \
		user-and-source-files.pdf user-and-source-files.eps \
		*.aux *.log *.ind *.idx *.toc *.ilg *.dvi *.ps *.out *.brf \
		all.conf *.deps *.libs

# common stuff
ROOT    = ../../..
include $(ROOT)/makes/main.mk
