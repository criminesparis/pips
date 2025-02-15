/*

  $Id: reset_hooks.c 23065 2016-03-02 09:05:50Z coelho $

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
#include <genC.h>
#include "misc.h"

/* reset functions to call on exceptions
 * to be used by pipsmake?
 *
 * should it be a stack?
 * should there by a stack of stacks for different TRY/CATCH levels?
 * should it be processed up to a marker?
 * would an additionnal void* for arguments make sense?
 */
static list reset_hooks = NIL;

/* add function to be called for cleanup if an exception is raised.
 */
void reset_hooks_register(reset_func_t function)
{
  pips_assert("reset function not already in list",
	      !gen_in_list_p(function, reset_hooks));
  reset_hooks = CONS(VOID_STAR, function, reset_hooks);
}

/* this function is expected to be called when catching an exception.
 */
void reset_hooks_call(void)
{
  // call reset functions
  FOREACH(VOID_STAR, f, reset_hooks)
    (*((reset_func_t) f))();

  // cleanup
  gen_free_list(reset_hooks);
  reset_hooks = NIL;
}

/* check that the stack was cleaned.
 */
void reset_hooks_is_empty(void)
{
  pips_assert("no reset functions", reset_hooks == NIL);
}

/* remove registered cleanup hook.
 */
void reset_hooks_unregister(reset_func_t function)
{
  // should it really be the first? probably too optimistic.
  /*
  pips_assert(reset_hooks &&
              VOID_STAR(CAR(reset_hooks)) == function,
              "unregister reset functions in reverse order");
  */
  pips_assert("unregister a function already registered",
	      gen_in_list_p(function, reset_hooks));
  gen_remove_once(&reset_hooks, function);
}

/* That's all */
