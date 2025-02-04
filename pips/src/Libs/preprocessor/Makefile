# $Id: Makefile 23662 2023-07-10 11:46:59Z coelho $
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

TARGET	= preprocessor

INC_CFILES = \
	source_file.c \
	split_file.c \
	csplit_file.c \
        f95split_file.c
INC_YFILES = splitc.y lexer.l

DERIVED_HEADERS = splitc.h
DERIVED_CFILES = splitc.c lexer.c

LIB_CFILES =	$(DERIVED_CFILES) $(INC_CFILES)

INC_TARGET = $(TARGET).h
LIB_TARGET = lib$(TARGET).a

YOPT	= -d

# common stuff
ROOT    = ../../..
PROJECT = pips
include $(ROOT)/makes/main.mk

# local stuff
$(TARGET).h: $(DERIVED_HEADERS) $(DERIVED_CFILES)

clean: local-clean

local-clean:
	$(RM) $(DERIVED_CFILES) $(DERIVED_HEADERS) y.tab.c y.tab.h

# split C parser

splitc.c: splitc.y
	$(PARSE) --name-prefix='splitc_' `pwd`/splitc.y
	mv y.tab.c splitc.c
	mv y.tab.h splitc.h

splitc.h: splitc.c

lexer.c: lexer.l splitc.h
	$(SCAN) --prefix='splitc_' `pwd`/lexer.l | $(SCANFIX) > $@
