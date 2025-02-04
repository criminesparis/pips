/*

  $Id: pragma.c 22777 2015-08-23 20:56:50Z irigoin $

  Copyright 1989-2010 HPC Project

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
#ifdef HAVE_CONFIG_H
    #include "pips_config.h"
#endif
/*
  This file define methods to deal with objects extensions and pragma
  used as extensions to statements in the PIPS internal representation.

  A middle term, extensions method could go in another file.

  It is a trivial implementation based on strings for a proof of concept.

  Pierre.Villalon@hpc-project.com
  Ronan.Keryell@hpc-project.com
*/

#include "linear.h"
#include "genC.h"
#include "misc.h"
#include "ri.h"
#include "ri-util.h"
#include "text-util.h"
#include "prettyprint.h"

/***************************************************** PRETTYPRINT PART
 */
/** @return a new allocated string to close the pragma.
 *  @param p, the pragma to be closed
 *
 */
string close_pragma(pragma p __attribute__ ((unused))) {
  string result = string_undefined;
  if(prettyprint_language_is_fortran_p()) {
    /* STEP -> les pragma ne sont pas toujours fermés par des "omp end parallel do"

      result = strdup(concatenate(FORTRAN_PRAGMA_HEADER,
                                  "omp end parallel do",
                                  NULL));
    */
  }
  return result;
}

/** @return a new allocated string with the pragma textual representation.
 */
string
pragma_to_string (pragma p) {
  bool flg   = false;
  list l_str = NULL; //list of string
  list l_expr = NULL; // list of expression
  size_t line_sz = 0; // the pragma line size
  string s = string_undefined;
  string_buffer sb = string_buffer_make(false);

  switch(pragma_tag (p)) {
    case is_pragma_string:
      s = pragma_string(p);
      break;
    case is_pragma_expression:
      l_expr = gen_nreverse(pragma_expression (p));
      FOREACH (EXPRESSION, e, l_expr)
      {
        if(flg ) {
          string_buffer_append(sb, strdup(" "));
          line_sz += 1;
        }
        flg = true;
	list pdl = NIL;
        l_str = words_expression(e, &pdl);
	gen_free_list(pdl);
        //      l_str = gen_nreverse (l_str);
        if(prettyprint_language_is_fortran_p()) {
          // In fortran line size can not be more than 72
          FOREACH (STRING, str, l_str)
          {
            pips_assert ("algo bug", line_sz < MAX_LINE_LENGTH - 7);
            size_t size = strlen(str);
            pips_assert ("not handled case need to split the str between two lines",
                size < (MAX_LINE_LENGTH - 7));
            line_sz += size;
            if(line_sz >= MAX_LINE_LENGTH - 8) {
              l_str = gen_insert_before(strdup(FORTRAN_OMP_CONTINUATION_STRING),
                                        str,
                                        l_str);
              line_sz = size;
            }
          }
        }
        string_buffer_append_list(sb, l_str);
        gen_free_list(l_str);
      }
      s = string_buffer_to_string(sb);
      // Free the buffer with its strings
      string_buffer_free_all(&sb);
      // restore the list as it was at the begining
      gen_nreverse(l_expr);
      break;
    default:
      pips_internal_error("Unknown pragma type");
      break;
  }
  if(s != string_undefined) {
    switch(get_prettyprint_language_tag()) {
      case is_language_fortran:
      case is_language_fortran95:
        s = strdup(concatenate(FORTRAN_PRAGMA_HEADER_STRING, s, NULL));
        break;
      case is_language_c:
        s = strdup(concatenate(C_PRAGMA_HEADER_STRING, " ", s, NULL));
        break;
      default:
        pips_internal_error("Language unknown !");
        break;
    }
  }
  return s;
}

/** @brief  Add an expression to the pragma current expression list.
 *  @return void
 *  @param  pr, the pragma to process.
 *  @param  ex, the expression to add.
 */
void
add_expr_to_pragma_expr_list (pragma pr, expression ex) {
  pips_assert ("the pragma need to be an expression", pragma_expression_p (pr) );
  /* Add the new pragma to the extension list: */
  list exprs = pragma_expression (pr);
  exprs = gen_expression_cons (ex, exprs);
  pragma_expression (pr) = exprs;
  string str = pragma_to_string (pr);
  pips_debug(5, "after: %s", str);
  free (str);
  return;
}
