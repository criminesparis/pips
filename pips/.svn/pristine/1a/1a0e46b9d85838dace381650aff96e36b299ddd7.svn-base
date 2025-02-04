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

/* Functions using simultaneously pipsdbm, which is based on strings,
   and ri-util, which contains basic methods for the objects of the
   internal representation.
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
#include "workspace-util.h"

/* Based on entity_user_name, but preserves scoping information when
   needed to avoid ambiguity between two or more variables with the
   same name.

   A variable or function name can be used for an external or static
   entity in the compilation unit, it can be used as function
   parameter, and then declared within the function at any scope
   level.

   This function cannot directly be used in an interprocedural setting
   as it is only related to one module.

   It is assumed that no new string is allocated, but a pointer to an
   existing string is returned.

   The current implementation is extremely ineffective, especially for
   a very unlikely, although mystifying, problem.

   FI: this function does not seem to be used in Libs or Passes. Its
implementation is based on module_entities(), which is not in ri-util...
*/
const char* entity_module_unambiguous_user_name(entity e, entity m)
{
  const char* uan = entity_user_name(e);

  /* No problem in Fortran */
  if(c_module_p(m)) {
    list conflicts = module_entities(m);

    FOREACH(ENTITY, v, conflicts){
	if(v!=e) {
	  const char* vn = entity_user_name(v);
	  if(same_string_p(uan,vn)) {
	    uan = entity_local_name(e);
	    break;
	  }
	}
      }
    gen_free_list(conflicts);
  }

  return (uan);
}

const char* entity_unambiguous_user_name(entity e)
{
  entity m = get_current_module_entity();

  return entity_module_unambiguous_user_name(e, m);
}

/* In interprocedural context, returns the shortest non-ambiguous name
   for a variable. If it is local to the current module, use the user
   name. If not return entity_name(), which is not fully satisfying
   for C variables because it includes scope information.

   Note also that this function assumes the existence of a current module.

   FI: why is this function in preprocessor and not in ri-util?
*/
static const char* entity_more_or_less_minimal_name(entity e, bool strict_p)
{
  entity m = get_current_module_entity();
  const char* mln = module_local_name(m);
  const char* emn = string_undefined;
  string cun = string_undefined; // compilation unit name
  entity cu = entity_undefined; // compilation unit
  list cudl = list_undefined; // compilation unit declaration list
  list mdl = code_declarations(value_code(entity_initial(m)));

  if(c_module_p(m) && !compilation_unit_p(mln)) {
    /* in pipsmake library...*/
    string compilation_unit_of_module(const char*);
    cun = compilation_unit_of_module(mln);
    cu = FindEntity(TOP_LEVEL_MODULE_NAME, cun);
    cudl = code_declarations(value_code(entity_initial(cu)));
    free(cun);
  }

  pips_assert("some current entity", !entity_undefined_p(m));

  /* gen_in_list_p() would/should be sufficient... */
  if (strcmp(mln, entity_module_name(e)) == 0
      || gen_in_list_p(e, mdl)) {
    /* The variable is declared in the current module */
    //return global_name_to_user_name(entity_name(e));
    if(strict_p)
      emn = entity_unambiguous_user_name(e);
    else
      emn = entity_user_name(e);
  }
  else if (!list_undefined_p(cudl) && gen_in_list_p(e, cudl)) {
    /* The variable is declared in the compilation unit of the current
       module */
    //return global_name_to_user_name(entity_name(e));
    if(strict_p)
      emn = entity_unambiguous_user_name(e);
    else
      emn = entity_user_name(e);
  }
  else if (entity_field_p(e)) {
    /* The variable is a union or struct field. No need to
       disambiguate. */
    if(strict_p)
      emn = entity_unambiguous_user_name(e);
    else
      emn = entity_user_name(e);
  }
  else if (entity_formal_p(e)) {
    /* Formal parameters should always be unambiguous? */
    if(strict_p)
      emn = entity_unambiguous_user_name(e);
    else
      emn = entity_user_name(e);
  }
  else if (strstr(entity_module_name(e), DUMMY_PARAMETER_PREFIX)) {
    /* The variable is a dummy parameter entity, used in a function
       declaration */
    if(strict_p)
      emn = entity_local_name(e);
    else {
      /* In analysis results, let's know when dummy parameters are
	 used... */
      //emn = strdup(entity_local_name(e));
      emn = strdup(entity_name(e));
    }
  }
  else if (strcmp(TOP_LEVEL_MODULE_NAME, entity_module_name(e)) == 0) {
    /* The variable is a ??? */
    if(strict_p)
      emn = entity_local_name(e);
    else
      emn = strdup(entity_local_name(e));
  }
  else if (strcmp(REGIONS_MODULE_NAME, entity_module_name(e)) == 0) {
    /* The variable is a PHI entity */
    if(strict_p)
      emn = entity_local_name(e);
    else
      emn = strdup(entity_local_name(e));
  }
  else if (strcmp(POINTS_TO_MODULE_NAME, entity_module_name(e)) == 0) {
    /* The variable is a stub entity for formal and global pointers */
    if(strict_p)
      emn = entity_local_name(e);
    else
      emn = strdup(entity_local_name(e));
  }
  else {
    /* must be used to prettyprint interprocedural information... */
    //entity om = local_name_to_top_level_entity(mln);
    //emn = entity_interprocedural_unambiguous_user_name(e, om);
    if(strict_p)
      emn = entity_name(e);
    else
      emn = strdup(entity_name(e));
  }

  return emn;
}

/* Do preserve scope informations

   This function does not allocate a new string, which implies to keep
   the scope information in the name of extraprocedural variables and
   functions.
 */
const char* entity_minimal_name(entity e)
{
  return entity_more_or_less_minimal_name(e, true);
}

/* Do not preserve scope information

   A new string is allocated.
 */
const char* entity_minimal_user_name(entity e)
{
  return entity_more_or_less_minimal_name(e, false);
}

void print_arguments(list args)
{
  print_homogeneous_arguments(args, entity_minimal_name);
}

/**
 * very simple conversion from string to expression
 * only handles entities and numeric values at the time being
 */
entity string_to_entity(const char * s,entity module)
{
    if(empty_string_p(s)) return entity_undefined;

    /* try float conversion */
    string endptr;
    const char *module_name=module_local_name(module);
    long int l = strtol(s,&endptr,10);
    if(!*endptr) {
        if(l>=0)
            return int_to_entity(l);
        else /* no negative integer entity in pips */
            return entity_undefined;
    }
    float f = strtof(s,&endptr);
    if(!*endptr) return float_to_entity(f);

    entity candidate = entity_undefined;
    /* first find all relevant entities */
    FOREACH(ENTITY,e,entity_declarations(module))
    {
        /* this an heuristic to find the one with a suiting scope
         * error prone*/
        if(same_string_p(entity_user_name(e),s) )
            if(entity_undefined_p(candidate) ||
                    strlen(entity_name(candidate)) > strlen(entity_name(e)))
                candidate=e;
    }
    /* try at the compilation unit level */
    if(entity_undefined_p(candidate))
        candidate=FindEntity(compilation_unit_of_module(module_name),s);
    /* try at top level */
    if(entity_undefined_p(candidate))
        candidate=FindEntity(TOP_LEVEL_MODULE_NAME,s);
    return candidate;
}

/* split a string using @p seed as separator
 * and call string_to_entity on each chunk */
list string_to_entities(const char * str, const char * seed, entity module) {
    list strings = strsplit(str,seed);
    list entities = NIL;
    FOREACH(STRING,s,strings) {
        entity e = string_to_entity(s,module);
        if(!entity_undefined_p(e)) {
            entities = CONS(ENTITY,
                    e,
                    entities);
        }
    }
    gen_map(free,strings);
    gen_free_list(strings);
    return gen_nreverse(entities);

}
