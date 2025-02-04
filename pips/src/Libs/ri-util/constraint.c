/*

  $Id$

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
#include <string.h>
#include <stdlib.h>

#include "linear.h"

#include "genC.h"

#include "properties.h"
#include "misc.h"
#include "ri.h"
#include "ri-util.h"

/************************************************************* VECTEUR STUFF */

void vect_debug(Pvecteur v)
{
  vect_fprint(stderr, v, (get_variable_name_t) entity_local_name);
}

/* comparison function for Pvecteur in pips, to be used by qsort.
 */
int compare_Pvecteur(Pvecteur * pv1, Pvecteur * pv2)
{
  return compare_entities((const entity*)&var_of(*pv1),
			  (const entity*)&var_of(*pv2));
}

bool vecteur_nul_p(Pvecteur v)
{
  return VECTEUR_NUL_P(v) ||
    // is this possible?
    (!v->succ && var_of(v)==TCST && val_of(v)==0);
}
