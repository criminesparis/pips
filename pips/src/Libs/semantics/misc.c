/*

  $Id: misc.c 23065 2016-03-02 09:05:50Z coelho $

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
 /* low level routines which should be added to other packages
  *
  * Francois Irigoin, April 1990
  *
  * Modifications:
  *  - passage a l'utilisation de database
  */

#include <stdio.h>

#include "genC.h"
#include "misc.h"
#include "linear.h"
#include "ri.h"
#include "effects.h"
#include "text-util.h"
#include "ri-util.h"
#include "prettyprint.h"
#include "effects-util.h"
#include "semantics.h"
#include "properties.h"

/* probably to add to the future callgraph library */

int call_site_count(m)
entity m;
{
    /* number of "call to m" sites within the current program;
       they are all in m's CALLERS */
    pips_assert("call_site_count", value_code_p(entity_initial(m)));
    /* I do not know yet; let's return 1 to please the semantic analysis */
    user_warning("call_site_count",
		 "not implemented yet, always returns 1\n");
    return 1;
}

int caller_count(m)
entity m;
{
    /* number of modules calling m within the current program;
       i.e. number of modules containing at least one call site to m */
    pips_assert("caller_count", value_code_p(entity_initial(m)));
    /* I do not know yet; let's return 1 to please the semantic analysis */
    user_warning("caller_count",
		 "not implemented yet, always returns 1\n");
    return 1;
}

int dynamic_call_count(entity m)
{
    /* number of call to m during the current program execution;
       return 0 if m is never called, either because it's a call
       graph root or because it was linked by mistake;
       return -1 if the dynamic call count is unknow, for instance
       because one of m's call site is located in a loop of unknown
       bounds;
       return k when it can be evaluated */
    pips_assert("Entity m is a function with defined code",
		value_code_p(entity_initial(m)));
    /* I do not know yet; let's return 1 to please the semantic analysis */
    pips_internal_error("Not implemented yet, always returns -1.\n");
    return -1;
}

/* Some other warnings include the pass name
 */
static void semantics_user_warning_alist(
  const char * func_name,
  const char * format,
  va_list * args)
{
  if (get_bool_property("NO_USER_WARNING"))
    return;

  statement cs = get_current_statement_from_statement_global_stack();
  int ln = statement_undefined_p(cs)? -1: statement_number(cs);

  // this may be big... truncate?
  const string scs = proper_statement_to_string(cs);

  pips_log_alist(
    warning_log,
    get_pips_current_pass_name(), get_pips_current_module(),
    (const string) func_name, NULL, -1,
    (string) get_current_module_name(), NULL, ln, -1,
    (const string) scs, NULL, (const string) format, args);

  free(scs);
  return;
}

void semantics_user_warning_func(
  const char * func_name,
  const char * format,
  ...)
{
  va_list args;
  va_start(args, format);
  semantics_user_warning_alist(func_name, format, &args);
  va_end(args);
}

void semantics_user_warning_func2(
  const char * format,
  ...)
{
  va_list args;
  va_start(args, format);
  semantics_user_warning_alist(pips_unknown_function, format, &args);
  va_end(args);
}
