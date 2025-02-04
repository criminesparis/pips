TARGET	= prettyprint
include_HEADERS=$(TARGET).h
BUILT_SOURCES=$(TARGET).h
include $(top_srcdir)/makes/cproto.mk
noinst_LTLIBRARIES=libprettyprint.la
libprettyprint_la_SOURCES= \
	allocatable.c \
	area.c \
	cmfortran.c \
	constraint_to_text.c \
	craft.c \
	declarations.c \
	declarations2.c \
	entity.c \
	expression.c \
	extension.c \
	fortran90.c \
	html_prettyprinter.c \
	loop.c \
	misc.c \
	module.c \
	parameter.c \
	pragma.c \
	print.c \
	print_code_as_a_graph.c \
	same_names.c \
	statement.c \
	symbol_table.c \
	type.c \
	unstructured.c

include $(srcdir)/../pipslibs_includes.mk
