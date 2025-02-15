# $Id: Makefile 23659 2023-07-07 13:00:14Z coelho $
#
# Copyright 1989-2016 MINES ParisTech
#
# This file is part of PIPS.
#
# PIPS is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# any later version.
#
# PIPS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.
#
# See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with PIPS.  If not, see <http://www.gnu.org/licenses/>.
#

TARGET	= c_syntax

# Rename all the lexer/parser entities c_... instead of yy... since there are
# many other parsers in PIPS:
#YOPT	= --defines --locations --name-prefix=c_
#LOPT	= --bison-bridge --bison-location --prefix=c_
YOPT	= --defines --name-prefix=c_ --report=state --debug --verbose
LOPT	= --prefix=c_

INC_CFILES =	c_parser.c \
		statement.c \
		util.c \
		return.c
INC_YFILES=cyacc.y clex.l

DERIVED_HEADERS = cyacc.h clexer.h
DERIVED_CFILES	= cyacc.tab.c clexer.c

LIB_CFILES = 	$(INC_CFILES) $(DERIVED_CFILES)

INC_TARGET =    $(TARGET).h
LIB_TARGET =    lib$(TARGET).a

# common stuff
ROOT    = ../../..
PROJECT = pips
include $(ROOT)/makes/main.mk

# local stuff
$(TARGET).h: $(DERIVED_HEADERS) $(DERIVED_CFILES)

clean: local-clean

local-clean:
	$(RM) $(DERIVED_CFILES) $(DERIVED_HEADERS) cyacc.[ch] cyacc.output

# C parser
cyacc.tab.c : cyacc.y
	$(BISON) $(YOPT) `pwd`/cyacc.y
	ln -s cyacc.tab.h cyacc.h

cyacc.h: cyacc.tab.c

clexer.c: clex.l cyacc.h
	$(SCAN) --header-file=clexer.h --prefix=c_ $< | $(SCANFIX) > $@

clexer.h: clexer.c
