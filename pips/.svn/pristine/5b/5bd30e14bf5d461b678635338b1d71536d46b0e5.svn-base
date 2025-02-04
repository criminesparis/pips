TARGET	= ri-util
include_HEADERS=$(TARGET).h
dist_noinst_HEADERS=operator.h
BUILT_SOURCES=$(TARGET).h
include $(top_srcdir)/makes/cproto.mk
noinst_LTLIBRARIES=libri-util.la
libri_util_la_SOURCES=	\
		eval.c \
		size.c \
		pragma.c \
		extension.c \
		util.c \
		area.c \
		ordering.c \
		declarations.c \
		loop.c \
		fortran90.c \
		constant.c \
		constraint.c \
		bound_generation.c \
		entity.c \
		variable.c \
		instruction.c \
		statement.c \
		reorder.c \
		clean_up_sequences.c \
		expression.c \
		type.c \
		normalize.c \
		static.c \
		arguments.c \
		module.c \
		control.c \
		hpfc.c \
		convex_hull.c \
		clean.c \
		clone_statement.c \
		allocatable.c \
		replace.c

include $(srcdir)/../pipslibs_includes.mk
