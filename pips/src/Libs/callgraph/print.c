/*

  $Id: print.c 23065 2016-03-02 09:05:50Z coelho $

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
/* functions to print a call graph
 *
 * They should be called by pipsmake
 *
 * Lei Zhou, February 91
 * Modification:
 *  - Callgraph prints only callees, nothing else.
 *           January 93
 *  - GO: Decoration of callgraphs, with some analyze results
 *           June 95
 *
 */
#include <stdio.h>
#include <string.h>

#include "linear.h"
#include "genC.h"
#include "misc.h"

#include "ri.h"
#include "ri-util.h"

#include "callgraph.h"

/** Print callees for debugging purpose */
void print_callees(callees c)
{
  list l = callees_callees(c);

  MAP(STRING, mn, {
      printf("%s\n", mn);
    }, l);
}

/*
 * This function prints out any graph that contains callees only
 */
bool print_decorated_call_graph(
  const string module_name,
  text (*module_to_text)(const string))
{
    bool success = false;
    entity mod = module_name_to_entity(module_name);

    debug_on(CALLGRAPH_DEBUG_LEVEL);
    pips_debug(1, "===%s===\n", module_name);
    success = module_to_callgraph(mod, module_to_text);
    debug_off();

    return success;
}

/*
 * Print callgraph with no decoration
 */
bool print_call_graph(const string module_name)
{
  bool success = false;
  success = print_decorated_call_graph(module_name, NULL);
  return success;
}
