TARGET	= bootstrap
include_HEADERS=$(TARGET).h
BUILT_SOURCES=$(TARGET).h
include $(top_srcdir)/makes/cproto.mk
noinst_LTLIBRARIES=libbootstrap.la
libbootstrap_la_SOURCES=	bootstrap.c type_checker.c
include $(srcdir)/../pipslibs_includes.mk
