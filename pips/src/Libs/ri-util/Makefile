# $Id: Makefile 23065 2016-03-02 09:05:50Z coelho $
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

TARGET	= ri-util

LIB_CFILES =	 \
		eval.c \
		size.c \
		pragma.c \
		extension.c \
		area.c \
		util.c \
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

INC_TARGET =	$(TARGET).h

LIB_TARGET =	lib$(TARGET).a

# common stuff
ROOT    = ../../..
PROJECT = pips
include $(ROOT)/makes/main.mk
