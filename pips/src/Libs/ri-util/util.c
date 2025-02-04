/*

  $Id: util.c 23412 2017-08-09 15:07:09Z irigoin $

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
/* Pot-pourri of utilities for the internal representation.
 * Some functions could be moved to non-generic files such as entity.c.
 */
#include <stdio.h>
#include <string.h>

#include "genC.h"
#include "linear.h"

#include "misc.h"
#include "ri.h"

#include "ri-util.h"

/* To deal with labels */

entity find_label_entity(const char* module_name, const char* label_local_name)
{
    string full = concatenate(module_name, MODULE_SEP_STRING,
			      LABEL_PREFIX, label_local_name, NULL);

    pips_debug(5, "searched entity: %s\n", full);
    void * found = gen_find_tabulated(full, entity_domain);
    return (entity) (gen_chunk_undefined_p(found) ? entity_undefined : found);
}

/* To find resources (this should be located in workspace-util as it
 * depends both on pipsdbm and ri-util.
 */

string module_codefilename(entity e)
{
    return(string_codefilename(entity_local_name(e)));
}

string module_par_codefilename(entity e)
{
    return(string_par_codefilename(entity_local_name(e)));
}

string module_fortranfilename(entity e)
{
    return(string_fortranfilename(entity_local_name(e)));
}

string module_par_fortranfilename(entity e)
{
    return(string_par_fortranfilename(entity_local_name(e)));
}

string module_pp_fortranfilename(entity e)
{
    return(string_pp_fortranfilename(entity_local_name(e)));
}

string module_predicat_fortranfilename(entity e)
{
    return(string_predicat_fortranfilename(entity_local_name(e)));
}

string module_entitiesfilename(entity e)
{
    return(string_entitiesfilename(entity_local_name(e)));
}


entity find_ith_parameter(entity e, int i)
{
  cons *pv = code_declarations(value_code(entity_initial(e)));

  if (! entity_module_p(e)) {
    pips_internal_error("entity %s is not a module",
			 entity_name(e));
  }
  while (pv != NIL) {
    entity v = ENTITY(CAR(pv));
    type tv = entity_type(v);
    storage sv = entity_storage(v);
    // FI: locations.c should be part of ri-util or a large entity library
    value val = entity_initial(v); // To check location entities

    // FI: the initial value of formal parameters may be value_undefined...
    // See Semantics-New/block01.c, formal parameter i of multiply
    if (type_variable_p(tv)
	&& storage_formal_p(sv)
	&& (value_undefined_p(val) || !value_reference_p(val))) {
      if (formal_offset(storage_formal(sv)) == i) {
        return(v);
      }
    }

    pv = CDR(pv);
  }

  return(entity_undefined);
}

/* returns true if v is the ith formal parameter of function f */
bool ith_parameter_p(entity f, entity v, int i)
{
  type tv = entity_type(v);
  storage sv = entity_storage(v);

  if (! entity_module_p(f)) {
    pips_internal_error("[ith_parameter_p] %s is not a module\n", entity_name(f));
  }

  if (type_variable_p(tv) && storage_formal_p(sv)) {
    formal fv = storage_formal(sv);
    return(formal_function(fv) == f && formal_offset(fv) == i);
  }

  return(false);
}

/* functions for references */

/* returns the ith index of an array reference */
expression reference_ith_index(reference ref, int i)
{
  int count = i;
  cons *pi = reference_indices(ref);

  while (pi != NIL && --count > 0)
    pi = CDR(pi);

  pips_assert("reference_ith_index", pi != NIL);

  return(EXPRESSION(CAR(pi)));
}

/* Test if a string can be a Fortran 77 comment: */
bool comment_string_p(const string comment)
{
  char c = *comment;
  /* If a line begins with a non-space character, claims it may be a
     Fortran comment. Assume empty line are comments. */
  return c != '\0' && c != ' ' && c != '\t';
}


/* Remove trailing line feed if any */
string string_remove_trailing_line_feed(string s)
{
  int sl = strlen(s);
  if(sl>0) {
    string ntl = s+sl-1;
    if(sl>0 && *ntl=='\n') {
      *ntl='\000';
    }
  }
  return s;
}

/* Remove trailing line feeds
 *
 * This function has been implemented three times. See below
 * string_strip_final_linefeeds() and string_fuse_final_linefeeds().
 */
string string_remove_trailing_line_feeds(string s)
{
  int sl = strlen(s);
  if(sl>0) {
    string ntl = s+sl-1;
    while(sl>0 && *ntl=='\n') {
      *ntl='\000';
      ntl--;
      sl--;
    }
  }
  return s;
}


/* Get rid of linefeed/newline at the end of a string.
 *
 * This is sometimes useful to cleanup comments messed up by the
 * lexical analyzer.
 *
 * Warning: the argument s is updated if it ends up with LF
 */
string string_strip_final_linefeeds(string s)
{
  int l = strlen(s)-1;

  while(l>=0 && *(s+l)=='\n') {
    *(s+l) = '\000';
    l--;
  }

  return s;
}

/* Get rid of extra linefeed/newline at the end of a string.
 *
 * This is sometimes useful to cleanup comments messed up by the
 * lexical analyzer.
 *
 * Warning: the argument s is updated if it ends up with LF
 */
string string_fuse_final_linefeeds(string s)
{
  int l = strlen(s)-1;

  while(l>=1 && *(s+l)=='\n' && *(s+l-1)=='\n') {
    *(s+l) = '\000';
    l--;
  }

  return s;
}

