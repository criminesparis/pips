/*

  $Id: loop.c 23065 2016-03-02 09:05:50Z coelho $

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

#include "linear.h"
#include "genC.h"

#include "misc.h"
#include "properties.h"

#include "ri.h"
#include "ri-util.h"
#include "text-util.h"
#include "prettyprint.h"

/*========================================================================*/
/* void fprint_loop(fp, lp): print a loop.
 *
 * AC 94/06/07
 */

/* copied from reindexing/reindexing_utils.c for debugging */

void printf_loop(loop lp) {
  FILE *fp = stdout;

  fprintf(fp,"\nLoop index information:");
  fprint_entity_list(fp, CONS(ENTITY, loop_index(lp), NIL));

  fprintf(fp,"\nDomaine (lower, upper, inc):");
  fprint_list_of_exp(fp,
      CONS(EXPRESSION, range_lower(loop_range(lp)), NIL));
  fprintf(fp,", ");
  fprint_list_of_exp(fp,
      CONS(EXPRESSION, range_upper(loop_range(lp)), NIL));
  fprintf(fp,", ");
  fprint_list_of_exp(fp,
      CONS(EXPRESSION, range_increment(loop_range(lp)), NIL));

  fprintf(fp,"\nLabel:");
  fprint_entity_list(fp, CONS(ENTITY, loop_label(lp), NIL));

  fprintf(fp,"\nExecution Type");
  if (execution_sequential_p(loop_execution(lp)))
    fprintf(fp, " ->sequentiel");
  else
    fprintf(fp, " ->parallele");

  fprintf(fp, "\nLocals: ");
  fprint_entity_list(fp, loop_locals(lp));

  fprintf(fp,"\n");
}

void print_loops_list(entity mod, list sl)
{
  FOREACH(LOOP, l, sl) {
    list pdl = NIL;
    text t = text_loop(mod, entity_name(loop_label(l)), 2, l, 0, &pdl, true);
    gen_free_list(pdl);
    print_text(stderr,t);
  }
}
