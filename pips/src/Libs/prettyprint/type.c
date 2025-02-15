/*

  $Id: type.c 23180 2016-09-09 12:37:41Z irigoin $

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
#include "ri.h"
#include "misc.h"

#include "ri-util.h"
#include "text-util.h"

#include "prettyprint.h"

/* Provide a full ASCII description of type "t"
 *
 * FI: I am not sure about the language used.
 */
string type_to_full_string_definition(type t)
{
  debug_on("PRETTYPRINT_DEBUG_LEVEL");
  list pdl = NIL;
  string s = words_to_string(words_type(t, &pdl, false));
  gen_free_list(pdl);
  debug_off();
  return s;
}

// same as above, but without the leak...
string string_of_type(const type t)
{
  list pdl = NIL;
  list wl = words_type(t, &pdl, false);
  gen_free_list(pdl);
  string s = words_to_string(wl);
  FOREACH(STRING,s,wl) free(s);
  gen_free_list(wl);
  return s;
}

/* For naming homogeneity: expression_to_string(), reference_to_string()... but type_to_string() is already implemented in ri-util in a less useful form */
/* string type_to_string(cons type t) */
/* { */
/*   return string_of_type(t); */
/* } */

/* This function cannot be in ri-util because of string_of_type() */
bool same_type_name_p(const type t0, const type t1) {
  string s0 = string_of_type(t0),
    s1 =string_of_type(t1);
  bool same = same_string_p(s0,s1);
  free(s0); free(s1);
  return same;
}



/*
 * returns the string to declare a basic type.
 */
 string basic_to_string(basic b)
{
  /* Nga Nguyen, 19/09/2003: To not rewrite the same thing, I use the words_basic() function*/
  list pdl = NIL;
  return list_to_string(words_basic(b, &pdl));
  gen_free_list(pdl);
}

/* Very basic and crude debugging function */
void print_types(list tl)
{
  bool first_p = true;

  fprintf(stderr, "Type list: ");

  FOREACH(TYPE, t, tl) {
    fprintf(stderr, first_p? "%p" : ", %p", t);
    first_p = false;
  }

  fprintf(stderr, "\n");
}

/* For debugging */
void print_type(type t)
{
  debug_on("RI-UTIL_DEBUG_LEVEL");
  if(t==NULL)
    fprintf(stderr, "type is NULL.\n");
  else if(type_undefined_p(t))
    fprintf(stderr, "type is undefined.\n");
  else if(type_domain_number(t)!=type_domain)
    fprintf(stderr, "The argument is not a type.\n");
  else {
  // Might be better to pass true, or even more information, to see
  // what happens with the unknown type
  list pdl = NIL;
  list wl = words_type(t, &pdl, false);
  gen_free_list(pdl);
  dump_words(wl);
  }
  debug_off();
}

void print_qualifiers(list ql)
{
  list wl = words_qualifiers(ql);
  dump_words(wl);
  gen_full_free_list(wl);
}

void print_qualifier(qualifier q)
{
  list ql = CONS(QUALIFIER, q, NIL);
  print_qualifiers(ql);
  gen_free_list(ql);
}
