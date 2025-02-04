/*

  $Id: naming.h$

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

/*  special characters to build entity names of various kinds
 */
#define MODULE_SEP                       ':'
#define MODULE_SEP_CHAR                  MODULE_SEP

#define MODULE_SEP_STRING                ":"
#define LABEL_PREFIX                     "@"
#define MAIN_PREFIX                      "%"
#define MAIN_PREFIX_CHAR                 '%'
#define COMMON_PREFIX                    "~"
#define BLOCKDATA_PREFIX                 "&"
#define F95MODULE_PREFIX                 "\xa4" // unicode character CURRENCY SIGN

#define FILE_SEP_CHAR                    '!'
#define FILE_SEP                         FILE_SEP_CHAR

#define FILE_SEP_STRING                  "!"

#define MODULE_NAME_CHARS \
  ( "ABCDEFGHIJKLMNOPQRSTUVWXYZ" \
    "0123456789" \
    "abcdefghijklmnopqrstuvwxyz" \
    FILE_SEP_STRING MODULE_SEP_STRING "|_#-." )

/* Scope separator */
#define BLOCK_SEP_STRING                 "`"
#define BLOCK_SEP_CHAR                   '`'

#define MEMBER_SEP_STRING                "^"
#define MEMBER_SEP_CHAR                  '^'

#define STRUCT_PREFIX                    "#" // Conflict with value naming in transformer
#define STRUCT_PREFIX_CHAR               '#'
#define UNION_PREFIX                     "'" /* Conflict with C character constants */
#define UNION_PREFIX_CHAR                '\''
#define ENUM_PREFIX                      "?"
#define ENUM_PREFIX_CHAR                 '?'
#define TYPEDEF_PREFIX                   "$"
#define TYPEDEF_PREFIX_CHAR              '$'

/*  constant names
 */
#define F95_USE_LOCAL_NAME               "*USE*"
#define BLANK_COMMON_LOCAL_NAME          "*BLANK*"
#define DYNAMIC_AREA_LOCAL_NAME          "*DYNAMIC*"
#define STATIC_AREA_LOCAL_NAME           "*STATIC*"
#define HEAP_AREA_LOCAL_NAME             "*HEAP*"
#define STACK_AREA_LOCAL_NAME            "*STACK*"
#define ALLOCATABLE_AREA_LOCAL_NAME      "*ALLOCATABLE*"
// The formal area could have been used for formal parameters
// It is used for the formal context of a function in points-to analysis
#define FORMAL_AREA_LOCAL_NAME           "*FORMAL*"
#define POINTER_DUMMY_TARGETS_AREA_LOCAL_NAME "*POINTER_DUMMY_TARGETS*"

/* The set of all memory areas. FI: this macro is now obsolete and
   should be removed when a new version of alias-classes is
   introduced. Too bad ri-util/effects.c is going to depend on
   alias-classes*/
#define ALL_MEMORY_ENTITY_NAME           "TOP-LEVEL:*MEMORY*"

/* For enum and struct and union without names (see c_syntax/cyacc.y) */
#define DUMMY_ENUM_PREFIX                "_PIPS_ENUM_"
#define DUMMY_STRUCT_PREFIX              "_PIPS_STRUCT_"
#define DUMMY_UNION_PREFIX               "_PIPS_UNION_"
#define DUMMY_ABSTRACT_PREFIX            "_PIPS_ABSTRACT_"
#define DUMMY_MEMBER_PREFIX              "_PIPS_MEMBER_" /* For bit fields */

/* For dmmmy parameters in functions declarations */
#define DUMMY_PARAMETER_PREFIX         "DUMMY-PARAMETER-"

/* Its value is "@", the label prefix followed by nothing */
#define EMPTY_LABEL_NAME                 LABEL_PREFIX
#define LIST_DIRECTED_FORMAT_NAME        "LIST-DIRECTED"


/* Module containing the global variables in Fortran and C */
#define TOP_LEVEL_MODULE_NAME            "TOP-LEVEL"
/* Module containing stub variables used to initialize intraprocedural
   points-to in C */
#define POINTS_TO_MODULE_NAME            "*POINTS-TO-MODULE*"

#define RETURN_LABEL_NAME                "00000"

/* In C, the module name may include file names, the compilation unit
 * name and the user name of the function. It goes well beyond the 36
 * of Fortan (check the standard).
*/
#define MAXIMAL_MODULE_NAME_SIZE 100

/* Constants for pragma management */
#define C_PRAGMA_HEADER_STRING "#pragma"
#define FORTRAN_PRAGMA_HEADER_STRING "!$"
#define FORTRAN_OMP_CONTINUATION_STRING "\n!$omp& "
