TARGET	= modeling
include_HEADERS=$(TARGET).h
BUILT_SOURCES=$(TARGET).h
include $(top_srcdir)/makes/cproto.mk
noinst_LTLIBRARIES=libmodeling.la
libmodeling_la_SOURCES= \
	utils.c \
	claire_prettyprinter.c \
	xml_prettyprinter.c

include $(srcdir)/../pipslibs_includes.mk
