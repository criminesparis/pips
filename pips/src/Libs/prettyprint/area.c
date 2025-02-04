/*

  $Id: area.c 23065 2016-03-02 09:05:50Z coelho $

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
/* Functions closely related to the entity class, constructors, predicates,...
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "linear.h"

#include "genC.h"
#include "misc.h"
#include "ri.h"
#include "properties.h"
#include "ri-util.h"

#include "prettyprint.h"

/* returns true if l contains an entity with same type, local name and offset.
 */
static bool comparable_entity_in_list_p(entity common, entity v, list l)
{
  entity ref = entity_undefined;
  bool ok, sn, so = false, st = false;

  /* first find an entity with the same NAME.
   */
  const char* nv = entity_local_name(v);
  MAP(ENTITY, e,
      {
        if (same_string_p(entity_local_name(e),nv))
          {
            ref = e;
            break;
          }
      },
      l);

  ok = sn = !entity_undefined_p(ref);

  pips_assert("v storage ram", storage_ram_p(entity_storage(v)));
  if (ok) pips_assert("ref storage ram", storage_ram_p(entity_storage(ref)));

  /* same OFFSET?
   */
  if (ok) ok = so = (ram_offset(storage_ram(entity_storage(v))) ==
                     ram_offset(storage_ram(entity_storage(ref))));

  /* same TYPE?
   */
  /* SG we cannot rely on same_type_p or type_equal_p because we want a syntactic comparison,
   * there used to be a hack in expression_equal_p to handle this particular case, I prefer to have the hack right here
   */
  if( ok ) {
      if(entity_undefined_p(ref)) ok = st =false;
      else {
          type tv = entity_type(v),
               tref = entity_type(ref);
          ok = st = same_type_name_p(tv,tref);
      }
  }

  pips_debug(4, "%s ~ %s? %d: n=%d,o=%d,t=%d\n", entity_name(v),
             entity_undefined_p(ref)? "<undef>": entity_name(ref),
             ok, sn, so, st);

  /* temporary for CA
   */
  if (!ok) {
    pips_debug(1, "common /%s/: %s != %s (n=%d,o=%d,t=%d)\n",
               entity_name(common), entity_name(v),
               entity_undefined_p(ref)? "<undef>": entity_name(ref),
               sn, so, st);
  }

  return ok;
}

/* check whether a common declaration can be simply included, that is
 * it is declared with the same names, orders and types in all instances.
 */
bool check_common_inclusion(entity common)
{
  bool ok = true;
  list /* of entity */ lv, lref;
  entity ref;
  pips_assert("entity is a common", entity_area_p(common));
  lv = area_layout(type_area(entity_type(common)));

  if (!lv) return true; /* empty common! */

  /* take the first function as the reference for the check. */
  ref = ram_function(storage_ram(entity_storage(ENTITY(CAR(lv)))));
  lref = common_members_of_module(common, ref, false);

  /* SAME name, type, offset */
  while (lv && ok)
    {
      entity v = ENTITY(CAR(lv));
      if (ram_function(storage_ram(entity_storage(v)))!=ref)
        ok = comparable_entity_in_list_p(common, v, lref);
      POP(lv);
    }

  gen_free_list(lref);
  return ok;
}
