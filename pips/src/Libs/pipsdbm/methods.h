/*

  $Id: methods.h 23065 2016-03-02 09:05:50Z coelho $

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
/*
 * Associated to each resource, the methods to read, write, free or check it.
 * For some reason the is no significant default, although the gen_* methods
 * would fit most needs.
 *
 * NOTE: this is the unload order...
 */

#define NEWGEN_METHODS                          \
  (READER) gen_read,                            \
    (WRITER) gen_write,                         \
    (FREER) gen_free,                           \
    (CHECKER) gen_consistent_p

#define NEWGENNOCHECK_METHODS \
  (READER) gen_read,          \
    (WRITER) gen_write,       \
    (FREER) gen_free,         \
    (CHECKER) gen_true

#define DONOTHING_METHODS                         \
    no_read, no_write, no_free, (CHECKER) gen_true

#define STATEMENT_FUNCTION_METHODS                  \
  (READER) pipsdbm_read_statement_function,         \
    (WRITER) pipsdbm_write_statement_function,      \
    (FREER) gen_free,                               \
    (CHECKER) pipsdbm_consistent_statement_function

#define STATEMENT_MAPPING_METHODS                 \
  (READER)  pipsdbm_read_statement_mapping,       \
    (WRITER)  pipsdbm_write_statement_mapping,    \
    (FREER)   pipsdbm_free_statement_mapping,     \
    (CHECKER) pipsdbm_check_statement_mapping

#define STATIC_STATEMENT_MAPPING_METHODS      \
  (READER) pipsdbm_read_statement_mapping,    \
    (WRITER) pipsdbm_write_statement_mapping, \
    (FREER) free_static_control_mapping,      \
    (CHECKER) pipsdbm_check_statement_mapping

#define GENFREE_METHODS                                   \
    no_read, no_write, (FREER) gen_free, (CHECKER) gen_true

#define STRING_METHODS                          \
    safe_readline,                              \
    writeln_string,                             \
    (FREER) free,                               \
    (CHECKER) gen_true

#define DECLARATIONS_METHODS                    \
  (READER) declarations_read,                   \
    (WRITER) declarations_write,                \
    (FREER) hash_table_free,                    \
    (CHECKER) gen_true

#define ENTITY_METHODS                          \
  (READER) pipsdbm_read_entities,               \
    (WRITER) gen_write_tabulated,               \
    (FREER) pipsdbm_free_entities,              \
    (CHECKER) gen_true

#define UNEXPECTED_METHODS                      \
    (READER) unexpected, (WRITER) unexpected,   \
    (FREER) unexpected, (CHECKER) unexpected

#include "methods-inc.h"


// this one MUST be the last one.
{ NULL,	UNEXPECTED_METHODS }

