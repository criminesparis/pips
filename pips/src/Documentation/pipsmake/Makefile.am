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

if WITH_DOC
doc_DATA=pipsmake-rc.pdf
endif
include $(top_srcdir)/makes/latex.mk

# Convert idraw/eps files.
pipsmake-rc.pdf:user-and-source-files.pdf

dist_noinst_SCRIPTS=make-pips-menu make-builder-map generate_all_menu_documentation pipspassdep.pl pipsmake-filter.pl

nodist_sysconf_DATA=pipsmake.rc properties.rc pipsdep.rc wpips.rc properties-2009-10-31.rc
dist_noinst_DATA=pipsmake-rc.tex properties-2009-10-31.rc.model resources.sed user-and-source-files.idraw

BUILT_SOURCES=resources.h printable_resources.h phases.h builder_map.h wpips_transform_menu_layout.h wpips_view_menu_layout.h pips-libs.h
nodist_include_HEADERS=resources.h printable_resources.h phases.h builder_map.h wpips_transform_menu_layout.h wpips_view_menu_layout.h pips-libs.h

# hmmm... this is generated locally to the virtual directory
pipsmake.full	= $(srcdir)/pipsmake-filter.pl --makes
pipsmake.flt	= $(srcdir)/pipsmake-filter.pl --makes
pipsprop.flt	= $(srcdir)/pipsmake-filter.pl --props
alias.flt	= $(srcdir)/pipsmake-filter.pl --alias

# Hmmm. It seems that ifdef is not supported by automake
# TODO: PIPS_SPECIAL full handling...
if PIPS_SPECIAL
pipsmake.flt	+= --subset=$(PIPS_SPECIAL).conf
alias.flt	+= --subset=$(PIPS_SPECIAL).conf
endif # PIPS_SPECIAL

UPPER	= tr '[a-z]' '[A-Z]'

pipsmake.rc:pipsmake-rc.tex
	$(pipsmake.flt) $(srcdir)/pipsmake-rc.tex > $@

properties.rc: pipsmake-rc.tex
	{ \
	  echo 'PIPS_VERSION "full"' ; \
	  $(pipsprop.flt) $(srcdir)/pipsmake-rc.tex ; \
	} > $@

properties-2009-10-31.rc: properties-2009-10-31.rc.model
	cp $(srcdir)/properties-2009-10-31.rc.model $@

pipsdep.rc: pipspassdep.pl pipsmake-rc.tex
	$(PERL) $(srcdir)/pipspassdep.pl $(srcdir)/pipsmake-rc.tex > $@

wpips.rc: pipsmake-rc.tex
	$(alias.flt) $(srcdir)/pipsmake-rc.tex > $@

resources.h: pipsmake-rc.tex
	$(pipsmake.full) $(srcdir)/pipsmake-rc.tex | \
		$(SED) -f $(srcdir)/resources.sed | \
		$(UPPER) | sort -u | \
		$(SED) 's/.*/#define DBR_& "&"/' > $@

all.conf: pipsmake-rc.tex
	$(pipsmake.full) $(srcdir)/pipsmake-rc.tex | \
		grep '^[a-z]' | cut -d' ' -f1 | sort > $@

%.deps: %.conf
	$(srcdir)/pass2lib.sh $< $(srcdir) > $@

%.libs: %.deps %.conf
	$(srcdir)/pass2libs.pl $^ > $@

pips-libs.h: all.libs
	{ \
	  echo "// pips libraries used by this built" ; \
	  for lib in $$(cat all.libs | tr '-' '_') ; do \
	    echo "#define HAVE_PIPS_$${lib}_LIBRARY" ; \
	  done ; \
	} > $@

printable_resources.h: resources.h
	$(SED) '/define.*FILE/!d' resources.h > $@

phases.h: pipsmake.rc
	$(SED) '/^[a-z]/!d;s/ .*//g;' pipsmake.rc | \
		tr '[a-z]' '[A-Z]' | sort -u | \
		$(SED) 's/.*/#define BUILDER_& "&"/' > $@

builder_map.h: pipsmake.rc $(srcdir)/make-builder-map
	$(srcdir)/make-builder-map < pipsmake.rc > $@


epips_transform_menu_layout.el wpips_transform_menu_layout.h epips_view_menu_layout.el wpips_view_menu_layout.h:  pipsmake-rc.tex generate_all_menu_documentation
	$(srcdir)/generate_all_menu_documentation -layout < $(srcdir)/pipsmake-rc.tex

CLEANFILES=$(nodist_include_HEADERS) $(sysconf_DATA) $(BUILT_SOURCES) epips_transform_menu_layout.el epips_view_menu_layout.el user-and-source-files.pdf $(nodist_sysconf_DATA)
