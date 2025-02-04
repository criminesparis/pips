/*

  $Id: semantics-local.h 23065 2016-03-02 09:05:50Z coelho $

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
 /* include file for semantic analysis */

#define SEMANTICS_OPTIONS "?Otcfieod-D:"

#define SEQUENTIAL_TRANSFORMER_SUFFIX ".tran"
#define USER_TRANSFORMER_SUFFIX ".utran"
#define SEQUENTIAL_PRECONDITION_SUFFIX ".prec"
#define USER_PRECONDITION_SUFFIX ".uprec"
#define SEQUENTIAL_TOTAL_PRECONDITION_SUFFIX ".tprec"
#define USER_TOTAL_PRECONDITION_SUFFIX ".utprec"

extern bool refine_transformers_p;

typedef struct{
  gen_array_t indices;
  statement statement;
} path;

#if defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 199901L) // C99
#define semantics_user_warning(...) \
  semantics_user_warning_func(CURRENT_FUNCTION, __VA_ARGS__)
#else
#define semantics_user_warning semantics_user_warning_func2
#endif

