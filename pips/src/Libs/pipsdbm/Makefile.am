TARGET	= pipsdbm
include_HEADERS=$(TARGET).h
dist_noinst_HEADERS=private.h methods.h methods-inc.h
BUILT_SOURCES=$(TARGET).h
include $(top_srcdir)/makes/cproto.mk
noinst_LTLIBRARIES=libpipsdbm.la
libpipsdbm_la_SOURCES=\
	database.c \
	lowlevel.c \
	workspace.c \
	externals.c \
	util.c \
	misc.c
include $(srcdir)/../pipslibs_includes.mk

clean: local-clean
local-clean:
	$(RM) methods-inc.h

methods.h: methods-inc.h
lowlevel.c: methods-inc.h

# special stuff
if PIPS_SPECIAL
# some resources may not be generated this will require guards
methods-inc.h: methods-inc.spec
	{ \
	  echo "/*" ; \
	  echo " * THIS FILE IS GENERATED AUTOMATICALLY, DO NOT EDIT" ; \
	  echo " */" ; \
	  echo ; \
	  perl -p \
	    -e 's/#/\/\//;' \
	    -e 's/^(\w+):\s*(\w+)/#ifdef $$1%{ $$1, $$2 },%#endif%/;' $< | \
	    tr '%' '\012' ; \
	} > $@
else
methods-inc.h: methods-inc.spec
# all resources are expected
	{ \
	  echo "/*" ; \
	  echo " * THIS FILE IS GENERATED AUTOMATICALLY, DO NOT EDIT" ; \
	  echo " */" ; \
	  echo ; \
	  perl -p \
	    -e 's/#/\/\//;' \
	    -e 's/^(\w+)\s*:\s*(\w+)/{ $$1, $$2 },/;' $< ; \
	} > $@
endif # PIPS_SPECIAL
