TARGET	= workspace-util
include_HEADERS=$(TARGET).h
#dist_noinst_HEADERS=operator.h
BUILT_SOURCES=$(TARGET).h
include $(top_srcdir)/makes/cproto.mk
noinst_LTLIBRARIES=libworkspace-util.la
libworkspace_util_la_SOURCES=	naming.c \
				expressions.c \
				misc_paf_utils.c \
				module.c

include $(srcdir)/../pipslibs_includes.mk
