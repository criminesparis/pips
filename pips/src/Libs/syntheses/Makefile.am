TARGET	= syntheses
include_HEADERS=$(TARGET).h
#dist_noinst_HEADERS=operator.h
BUILT_SOURCES=$(TARGET).h
include $(top_srcdir)/makes/cproto.mk
noinst_LTLIBRARIES=libsyntheses.la
libsyntheses_la_SOURCES=	initializer.c \
                                clone.c

include $(srcdir)/../pipslibs_includes.mk
