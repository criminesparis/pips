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

//#include <stdio.h>
//#include <string.h>

#include "genC.h"
#include "linear.h"

#include "misc.h"
// #include "properties.h"

#include "ri.h"
#include "effects.h"

#include "ri-util.h"
#include "prettyprint.h"
#include "effects-util.h"

#include "text-util.h"

#include "effects-simple.h"

#include "pips-libs.h"

#include "transformer.h"
#include "semantics.h"

// FI: these constants are not (yet) defined in ri-util-local.h
#define unsigned_char          11
#define unsigned_short_int     12
#define unsigned_int           14
#define unsigned_long_int      16
#define unsigned_long_long_int 18

/* Add some of the constraints linked to the type of a variable */
static void add_type_information(transformer tf)
{
  Psysteme ps = predicate_system(transformer_relation(tf));
  Pbase b = vect_copy(sc_base(ps)); // FI: the basis may evolve when
                                    // new constraints are added
  Pbase cb = BASE_NULLE;

  for(cb=b; !BASE_NULLE_P(cb); cb = vecteur_succ(cb)) {
    Variable v = vecteur_var(cb);
    //entity ev = (entity) v;
    if(v!=TCST && !local_old_value_entity_p(v)) { // FI: TCST check should be useless in a basis
      entity e = value_to_variable(v);
      type t = entity_basic_concrete_type(e);
      if(unsigned_type_p(t)) {
	basic tb = variable_basic(type_variable(t));
	int s = basic_int(tb);
	// FI: the lower bound, lb, could also be defined, e.g. for "char"
	long long int ub = -1/*, lb = 0*/;
	long long int period = 0;
	switch(s) {
	case unsigned_char:
	  ub = 256-1, period = 256;
	  break;
	case unsigned_short_int:
	  ub = 256*256-1, period = 256*256;
	  break;
	case unsigned_int:
	  // We go straight to the overflows!
	  // ub = 256L*256L*256L*256L-1;
	  ub = 0, period = 256L*256L*256L*256L;
	  break;
	case unsigned_long_int:
	  // We go straight to the overflows!
	  // ub = 256L*256L*256L*256L-1;
	  ub = 0, period = 256L*256L*256L*256L;
	  break;
	case unsigned_long_long_int:
	  // We go straight to the overflows!
	  //ub = 256*256*256*256*256*256*256*256-1;
	  //ub = 0; // FI: too dangerous
	  break;
	default:
	  ub=-1; // do nothing
	  break;
	}
	if(ub>=0) { 
	  /* We assume exists lambda s.t. e = ep + period*lambda */
	  entity ep = make_local_temporary_value_entity(t);
	  entity lambda = make_local_temporary_integer_value_entity();
	  tf = transformer_add_inequality_with_integer_constraint(tf, ep, 0, false);
	  if(ub>0) {
	    // Without this dangerous upperbound, we lose information
	    // but avoid giving wrong results.
	    // FI: The upperbound is dangerous because linear does not
	    // expect such large constants, especially my bounded normalization
	    // that should be itself bounded! See
	    // check_coefficient_reduction() and the stack allocation
	    // of arrays a, b and c!
	    tf = transformer_add_inequality_with_integer_constraint(tf, ep, ub, true);
	  }
	  Pvecteur eq =
	    vect_make(vect_new(e, VALUE_MONE),
		      ep, VALUE_ONE,
		      lambda, (Value) period, TCST, VALUE_ZERO, NULL);
	  tf = transformer_equality_add(tf, eq);
	  /* Compute the value of lambda */
	  Value pmin, pmax;
	  if(precondition_minmax_of_value(lambda, tf, (intptr_t*) &pmin, (intptr_t*) &pmax)) {
	    if(pmin==pmax) 
	      tf = transformer_add_equality_with_integer_constant(tf, lambda, pmin);
	  }
	  /* Now we must get rid of lambda and e and possibly e's old value */
	  list p =
	    CONS(ENTITY, e, CONS(ENTITY, lambda, NIL));
	  pips_assert("ep is in tf basis",
		      base_contains_variable_p(sc_base(ps), ep));
	  pips_assert("lambda is in tf basis",
		      base_contains_variable_p(sc_base(ps), lambda));
	  if(entity_is_argument_p(e, transformer_arguments(tf))) {
	    entity old_e = entity_to_old_value(e);
	    p = CONS(ENTITY, old_e, p);
	    pips_assert("old_e is in tf basis",
			base_contains_variable_p(sc_base(ps), ep));
	  }
	  /* Transformer projection removes variables from the
	     argument list as well as from the contraint system. */
	  list args = gen_copy_seq(transformer_arguments(tf));
	  tf = safe_transformer_projection(tf, p);
	  gen_free_list(transformer_arguments(tf));
	  transformer_arguments(tf) = args;
	  gen_free_list(p);
	  /* Now we must substitute ep by e */
	  tf = transformer_value_substitute(tf, ep, e);
	}
      }
    }
  }
  vect_rm(b);
  return;
}

void transformer_add_type_information(transformer tf)
{
  add_type_information(tf);
  return;
}

void transformer_add_variable_type_information(transformer tf, entity v)
{
  pips_assert("entity has values", entity_has_values_p(v));
  entity vv = entity_to_new_value(v);
  if(!value_belongs_to_transformer_space(vv, tf))
    add_value_to_transformer_space(vv, tf);
  transformer_add_type_information(tf);
  return;
}
