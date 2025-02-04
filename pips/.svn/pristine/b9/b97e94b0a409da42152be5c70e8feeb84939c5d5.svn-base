
TARGET	= step

PARSER_COMMENT = comment2pragma

LEXER_STEP = step_lexer
PARSER_STEP = step_bison_parser


INSTALL_INC = STEP_name.h STEP_RT_bootstrap.h STEP_RT_intrinsic.h

DERIVED_HEADERS = $(INSTALL_INC) $(PARSER_COMMENT).h $(LEXER_STEP).h $(PARSER_STEP).h ../../Runtimes/step/c/STEP.h
DERIVED_CFILES	= $(PARSER_COMMENT).c $(LEXER_STEP).c $(PARSER_STEP).c

INC_CFILES=	directives.c \
		analyse.c \
		compile_RT.c \
		compile_mpi.c \
		compile_regions.c \
		compile.c \
		parser.c \
		install.c

LIB_CFILES = $(DERIVED_CFILES) $(INC_CFILES)

INC_TARGET =    $(TARGET).h

LIB_TARGET =    lib$(TARGET).a


# common stuff
ROOT    = ../../..
PROJECT = pips
CPPFLAGS += -DPIPS_RUNTIME_DIR=\"$(CURDIR)/../../Runtimes\"
include $(ROOT)/makes/main.mk

# local stuff

# FC 2015-07-19: commented-out to avoid a cyclic step.h -> step.h
#   dependency warning from make
#$(TARGET).h: $(DERIVED_HEADERS) $(DERIVED_CFILES)

clean: local-clean

local-clean:
	$(RM) $(DERIVED_CFILES) $(DERIVED_HEADERS) step_api.tmp steprt_f.h

# work around flex 2.6.0 generated code...
FIX2	= sed -e 's/\( number_to_move == YY_MORE_ADJ \)/(int) \1/'

$(PARSER_COMMENT).c: $(PARSER_COMMENT).l
	$(SCAN) --prefix=$(PARSER_COMMENT) -DYY_NO_INPUT -DIN_PIPS \
	  --header-file=$(PARSER_COMMENT).h $< | $(SCANFIX) | $(FIX2) > $@

$(PARSER_COMMENT).h: $(PARSER_COMMENT).c

$(LEXER_STEP).c: $(LEXER_STEP).l $(PARSER_STEP).h
	$(SCAN) --prefix=$(LEXER_STEP) -DYY_NO_INPUT \
	  --header-file=$(LEXER_STEP).h $< | $(SCANFIX) | $(FIX2) > $@

$(PARSER_STEP).c: $(PARSER_STEP).y
	$(BISON) -d --name-prefix=$(LEXER_STEP) $< -o $@

$(PARSER_STEP).h: $(PARSER_STEP).c

srcdir=.
include stepstuff.mk

../../Runtimes/step/c/STEP.h:
	$(MAKE) -C ../../Runtimes/step/c STEP.h
