TARGET	= naming
include_HEADERS=$(TARGET).h
BUILT_SOURCES=$(TARGET).h
include $(top_srcdir)/makes/cproto.mk
noinst_LTLIBRARIES=libnaming.la
libnaming_la_SOURCES=	entity_names.c \
			file_names.c

include $(srcdir)/../pipslibs_includes.mk
