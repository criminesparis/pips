/*

  $Id: preprocessor-local.h 23662 2023-07-10 11:46:59Z coelho $

  Copyright 1989-2016 MINES ParisTech

  This file is part of PIPS.

  PIPS is free software: you can redistribute it and/or modify it
  under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  any later version.

  PIPS is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.

  See the GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with PIPS.  If not, see <http://www.gnu.org/licenses/>.

*/
/* Preprocessing and splitting of Fortran and C files
 */

/* the name of the environment variable where source files are searched for. */
#define SRCPATH "PIPS_SRCPATH"

/* pre-processor and added options from environment
 */
#define CPP_PIPS_ENV		"PIPS_CPP"
#define CPP_PIPS_OPTIONS_ENV 	"PIPS_CPP_FLAGS"
#define FPP_PIPS_ENV		"PIPS_FPP"
#define FPP_PIPS_OPTIONS_ENV 	"PIPS_FPP_FLAGS"

/* default preprocessor and basic options
 * -C: do not discard comments...
 * -P: inhibit linemakers (# 1 "file.c")
 * -ffreestanding: ignore "stdc-predef.h"
 */
// alternative values: "gcc -E -C"
// force c99 for gcc/clang validation compatibility
#define CPP_CPP			"cpp -C -std=c99"
/* #define CPP_CPPFLAGS		" -P -D__PIPS__ -D__HPFC__ " */
/* -U__GNUC__ seems to be still useful to avoid spoiling the libC files
    with too many GCC extensions: */
//#define CPP_CPPFLAGS		" -D__PIPS__ -D__HPFC__ "
#define CPP_CPPFLAGS		" -D__PIPS__ -D__HPFC__ -U__GNUC__ "

/** The preprocessor to use for Fortran files.

    Alternative values: "gcc -E -C" or "fpp". The issue with cpp or gcc -E
    is that they don't undestand Fortran and chokes on unbalanced strings
    in Fortran comments and so on.
*/
#define FPP_CPP			"gfortran -E"

/** The default preprocessor flags to use with Fortran files */
#define FPP_CPPFLAGS		" -P -D__PIPS__ -D__HPFC__ "

#define DEFAULT_PIPS_FLINT "gfortran -Wall"

/* See necessary definitions in pipsmake-rc.tex */
//#define DEFAULT_PIPS_CC "gcc -std=c99 -D__PIPS__ -D__HPFC__ "
#define DEFAULT_PIPS_CC "gcc -std=c99 -D__PIPS__ -D__HPFC__ -U__GNUC__ "
#define DEFAULT_PIPS_CC_FLAGS " -Wall "

/* Define some functions from the .l or .y since cproto cannot dig them out: */
void MakeTypedefStack();
void ResetTypedefStack();

#define csplit_parser_warning(...)                                 \
  csplit_parser_warning_func(CURRENT_FUNCTION, __FILE__, __LINE__, \
                             __VA_ARGS__)

/* symbols exported by lex / yacc */
typedef size_t yy_size_t;

extern char * splitc_text;
extern FILE * splitc_in;
extern int splitc_lex();
extern int splitc_lex_destroy();
extern int splitc_parse();
extern void splitc_error(const char*);
