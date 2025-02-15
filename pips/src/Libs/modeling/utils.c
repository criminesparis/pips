/*

  $Id: utils.c 23065 2016-03-02 09:05:50Z coelho $

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

#ifdef HAVE_CONFIG_H
    #include "pips_config.h"
#endif

#include <stdio.h>

#include "genC.h"
#include "linear.h"

#include "misc.h"
#include "pipsdbm.h"

#include "ri.h"
#include "effects.h"

#include "ri-util.h"
#include "effects-util.h"
#include "text-util.h"
#include "prettyprint.h"

/* keep a count of spear issues
 */
static int
  spear_warning_count = 0,
  spear_error_count = 0;

/* internal alist-level processing for spear warning & error logging
 */
static void spear_log_alist(
  const char * pips_func,
  const char * pips_file,
  const int pips_line,
  pips_log_t tag,
  statement stat,
  const string hint,
  const string format,
  va_list * args)
{
  pips_assert("spear log", tag == spear_warning_log || tag == spear_error_log);

  if (tag == spear_warning_log)
    spear_warning_count ++;
  else if (tag == spear_error_log)
    spear_error_count ++;

  string module = get_pips_current_module();

  pips_assert("some current module", module != NULL);

  // where is the user code?
  int ln = -1;
  string sstat = NULL;
  string stat_file = NULL;

  if (stat && !statement_undefined_p(stat))
  {
    // what is a really the statement number?
    ln = statement_number(stat);
    sstat = proper_statement_to_string(stat);
    stat_file = db_get_memory_resource(DBR_INPUT_FILE_NAME, module, true);
  }

  pips_log_alist(
    tag, get_pips_current_pass_name(), module,
    // where in pips
    (const string) pips_func, (const string) pips_file, pips_line,
    // where in user code
    module, stat_file, ln, -1,
    sstat, hint, format, args);

  free(sstat);
}

/* generate a spear user warning or spear user error.
 * this function is not expected to be called directly, but it should be
 * redirected here from a macro "spear_error(stat, hing, fmt, ...)"
 */
void spear_log_func(
  // automatically added parameters, see spear_warning & spear_error macros
  const char * pips_func,
  const char * pips_file,
  const int pips_line,
  pips_log_t tag,
  // parameters to provide
  statement stat,
  const string hint,
  const string format,
  ...)
{
  va_list args;
  va_start(args, format);
  spear_log_alist(pips_func, pips_file, pips_line, tag,
                  stat, hint, format, &args);
  va_end(args);
}
