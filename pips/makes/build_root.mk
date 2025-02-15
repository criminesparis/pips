# $Id: build_root.mk 1251 2017-09-18 05:26:26Z coelho $
#
# Copyright 1989-2016 MINES ParisTech
#
# This file is part of PIPS.
#
# PIPS is free software: you can redistribute it and/or modify it
# under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# any later version.
#
# PIPS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.
#
# See the GNU Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public License
# along with PIPS.  If not, see <http://www.gnu.org/licenses/>.
#
FWD_DIRS	= src makes

# needed for PIPS_NO_TAGS
-include makes/config.mk

# default is to "build" (phase 0 to 6)
all: build

# specialized pips compilation require to define
# the list of libraries to actually compile in
# this should be skipt for newgen & linear compilation.
# .PHONY?
ifdef PIPS_SPECIAL
pm.dir = ./src/Documentation/pipsmake
compile: $(pm.dir)/$(PIPS_SPECIAL).libs
$(pm.dir)/$(PIPS_SPECIAL).libs:
	@echo "### pips special compilation"
	if [ -d $(pm.dir) ] ; then \
	  $(MAKE) -C $(pm.dir) $(PIPS_SPECIAL).libs ; \
	fi
endif

.PHONY: compile
compile:
	-test -d ./makes && $(MAKE) -C ./makes build
	@echo "### pips compile phase0 (depends)"
	$(MAKE) -C src phase0
	@echo "### pips compile phase1 (etc & py)"
	$(MAKE) -C src phase1
	@echo "### pips compile phase2 (include)"
	$(MAKE) -C src phase2
	@echo "### pips compile phase3 (nope?)"
	$(MAKE) -C src phase3
	@echo "### pips compile phase4 (lib)"
	$(MAKE) -C src phase4
	@echo "### pips compile phase5 (bin)"
	$(MAKE) -C src phase5
	#@echo "### pips compile phase6 (doc)"
	#$(MAKE) -C src phase5
ifndef PIPS_NO_TAGS
	@echo "### tags"
	$(MAKE) tags
endif

.PHONY: compiler-version
compiler-version:
	@$(CC) --version | head -1

# hmmm... not sure it is a good idea to go on errors.
.PHONY: doc
doc: compile
	$(MAKE) -C src FWD_STOP_ON_ERROR= phase6

.PHONY: htdoc
htdoc: doc
	$(MAKE) -C src FWD_STOP_ON_ERROR= phase7

# various convenient short-hands
.PHONY: build
build: doc

.PHONY: full-build
full-build: htdoc

# more documentation
.PHONY: doxygen
doxygen: htdoc

# do not include dependencies for some target
clean: NO_INCLUDES=1
unbuild: NO_INCLUDES=1
export NO_INCLUDES

# Clean up everything below:
.PHONY: clean
clean:
	$(MAKE) -C src clean

.PHONY: unbuild
unbuild: clean tags-clean
	$(MAKE) -C src unbuild
	$(MAKE) -C makes unbuild
	$(RM) -r bin lib etc share runtime

.PHONY: rebuild
rebuild:
	$(MAKE) unbuild
	$(MAKE) build

.PHONY: recompile
recompile:
	$(MAKE) clean
	$(MAKE) compile

.PHONY: install
install:
	$(MAKE) -C src install

.PHONY:  uninstall
uninstall:unbuild

# all about tags, with temporary files
# should it generate tags only for src/?
etags	= /tmp/etags.$$$$
# may be overrident in config
ETAGS	?= ctags -e
TAGS:
	find $(CURDIR) -name '*.[chly]' -print0 | \
		xargs -0 $(ETAGS) --append -o $(etags) ; \
	mv $(etags) TAGS

ctags	= /tmp/ctags.$$$$
CTAGS:
	find $(CURDIR) -name '*.[chly]' -print0 | \
		xargs -0 ctags --append -o $(ctags) ; \
	mv $(ctags) CTAGS

cscope.out:cscope-clean
	cd / && \
		find $(CURDIR) -name '*-local.h' -type f -prune -o -name include -type d -prune -o -name '*.[ch]' -print >  $(CURDIR)/cscope.files && \
		cd - && \
		cscope -b && \
		rm -f $(CURDIR)/cscope.files

cscope-clean:
	$(RM) cscope.out

# autoconf compilation
# --enable-doc --enable-devel-mode
BUILD.dir	= _build
HERE	:= $(shell pwd)
INSTALL.dir	= $(HERE)/../../install
DOWNLOAD.dir	= $(HERE)/../..
ifndef EXTERN_ROOT
EXTERN_ROOT	= $(HERE)/../extern
endif

# add ENABLE='doc devel-mode paws fortran95'
ENABLE	= hpfc pyps gpips

.PHONY: auto auto-comp auto-clean
auto-clean:
	$(RM) -r $(BUILD.dir) autom4te.cache
	$(RM) configure depcomp config.guess config.sub ltmain.sh config.log \
	       config.h.in missing aclocal.m4 install-sh compile py-compile \
	       makes/m4/libtool.m4 makes/m4/ltoptions.m4 makes/m4/ltsugar.m4 \
	       makes/m4/ltversion.m4 makes/m4/lt~obsolete.m4
	find . -name .svn -prune -o -name Makefile.in -print0 | xargs -0 rm -f

# initial configuration
libpkg	= lib/pkgconfig
$(BUILD.dir):
	autoreconf -vi
	mkdir $(BUILD.dir) && cd $(BUILD.dir) ; \
	../configure --prefix=$(INSTALL.dir) \
	    PATH=$(INSTALL.dir)/bin:$$PATH \
	    PKG_CONFIG_PATH=$(INSTALL.dir)/$(libpkg):$(EXTERN_ROOT)/$(libpkg) \
	    --disable-static $(ENABLE:%=--enable-%)

# just compile
auto-comp: $(BUILD.dir)
	$(MAKE) -C $(BUILD.dir) DL.d=$(DOWNLOAD.dir)
	$(MAKE) -C $(BUILD.dir) install
	# manual fix...
	-[ -d $(BUILD.dir)/src/Scripts/validation ] && \
	  $(MAKE) -C $(BUILD.dir)/src/Scripts/validation install

# clean & compile
auto: auto-clean
	$(MAKE) auto-comp

# with paws
auto-paws:; $(MAKE) ENABLE='paws pyps' auto

# force tags target
tags: tags-clean
	$(MAKE) TAGS CTAGS

# Force recompilation if the user ask for explicit TAGS or CTAGS
.PHONY: tags TAGS CTAGS

# ARGH. I want both to forward and to clean locals...
#clean: tags-clean
tags-clean:
	$(RM) TAGS CTAGS
