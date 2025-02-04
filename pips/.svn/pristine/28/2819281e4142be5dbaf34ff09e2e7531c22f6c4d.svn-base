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

/* Interface with points-to library */

#include <stdio.h>
#include <string.h>

#include "genC.h"
#include "linear.h"

#include "misc.h"
#include "properties.h"

#include "ri.h"
#include "effects.h"

#include "ri-util.h"
#include "prettyprint.h"
#include "effects-util.h"

#include "text-util.h"

#include "effects-simple.h"

#include "transformer.h"
//#include "semantics.h"

#include "effects-convex.h"

#include "pips-libs.h"
#ifdef HAVE_PIPS_points_to_LIBRARY
// for get_points_to_graph_from_statement & expression_to_points_to_sinks
#include "points-to.h" // 2 or more functions


/* Substitute PHI1 in effect reference if possible thanks to an
 * equation in the effect descriptor, which is assumed convex.
 *
 */
bool adapt_convex_effect_cell_to_backward_translation(effect eff)
{
  bool adapt_p = false; // By default, the conversion fails
  reference r = effect_any_reference(eff);
  list sl = reference_indices(r); // subscript list
  if(!ENDP(sl)) {
    expression se = EXPRESSION(CAR(sl));
    if(expression_reference_p(se)) {
      // By definition, it must be a reference to PHI1 variable
      reference sr = expression_reference(se);
      entity phi = reference_variable(sr);
      entity phi1 = make_phi_entity(1);
      if(phi==phi1) {
	/* Is phi defined as a 0 constant in the convex descriptor of eff?
	 *
	 * The standard way to do this is to call one of the minmax
	 * functions, but they are very slow. And here we know which
	 * equation to expect, phi==0.
	 */
	descriptor d = effect_descriptor(eff);
	Psysteme sc = descriptor_convex(d);
	Value val;
	if(sc_value_of_variable(sc, (Variable) phi, &val)) {
	  if(val==VALUE_ZERO) { // No VALUE_ZERO_P predicate in linear.h

	    /* Eliminate phi1 from the subscript list and from the predicate */
	    free_syntax(expression_syntax(se));
	    expression_syntax(se) =
	      make_syntax_call(make_call(int_to_entity(0), NIL));
	    region_exact_projection_along_variable(eff, phi);

	    // Substitute PHI_n by PHI_{n-1}
	    // They are supposed to appear in increasing rank order
	    list nsl = CDR(sl);
	    FOREACH(EXPRESSION, nse, nsl) {
	      syntax nss = expression_syntax(nse);
	      if(syntax_reference_p(nss)) {
		reference nsr = syntax_reference(nss);
		entity phin = reference_variable(nsr);
		int r = phi_entity_rank(phin);
		if(r!=0) {
		  entity phinm1 = make_phi_entity(r-1);
		  region_value_substitute(eff, phin, phinm1);
		  // Will be performed after translation
		  // reference_variable(nsr) = phinm1; Replace all phi
		  // variables by zero for matching the points-to
		  // information
		  free_syntax(expression_syntax(nse));
		  expression_syntax(nse) =
		    make_syntax_call(make_call(int_to_entity(0), NIL));
		}
	      }
	    }
	    adapt_p = true; // Could now mean that phi1 has been eliminated
	  }
	}
	else {
	  /* Phi1 must be preserved, but the corresponding subscript
	     set to zero to exploit points-to information for the
	     translation */
	    /* Eliminate phi1 from the subscript list */
	    free_syntax(expression_syntax(se));
	    expression_syntax(se) =
	      make_syntax_call(make_call(int_to_entity(0), NIL));
	    adapt_p = true;
	}
      }
    }
  }

  return adapt_p;
}

/* The same issue must arise in Fortran and be treated as a
 * case of region backward translation somewhere in
 * convex-effects.
 *
 * phi_n has to be offset by se, if se is an affine expression
 * or if its value is known.
 *
 * Else, phi_n has to be project out of the descriptor, which is
 * always valid if the exact or must approximation is reduced to may.
 *
 * In all cases, the subscript must be updated and 0 be
 * replaced by phi_n.
 *
 * Expression se is the nth subscript of the reference in eff. Effect
 * eff and expression se are updated by side effects.
 */
void adapt_phi_n_variable_in_convex_effect(effect eff, expression se, entity phi_n)
{
  // The easiest implementation
  //pips_internal_error("Phi update not implemented yet.\n");

  normalized n = NORMALIZE_EXPRESSION(se);

  if(normalized_linear_p(n)) {
    // Substitue phi_n by pni_n-v in the convex descriptor
    Pvecteur v = vect_dup(normalized_linear(n));
    v = vect_multiply(v, VALUE_MONE);
    //vect_add_elem(&v, (Variable) phi_n, VALUE_MONE);
    //Pcontrainte eq = contrainte_make(v);
    descriptor d = effect_descriptor(eff); // Assumed convex
    Psysteme sc = descriptor_convex(d);
    // descriptor_convex(d) = sc_variable_substitution_with_eq_ofl_ctrl(sc, eq, (Variable) phi_n, FWD_OFL_CTRL);
    descriptor_convex(d) = sc_substitute_dimension(sc, (Variable) phi_n, v);
  }
  // The expression may not be affine but still be a constant expression
  // else if(constant_expression_p()) {}
  else {
    // The second easiest implementation
    region_exact_projection_along_variable(eff, phi_n);
    free_approximation(effect_approximation(eff));
    effect_approximation(eff) = make_approximation_may();
  }
  free_syntax(expression_syntax(se));
  expression_syntax(se) =
    make_syntax_reference(make_reference(phi_n, NIL));
}

/* Replace back 0's used for the points-to translation by phi
 * variables (side effects).
 *
 * Rename the original phi variables in the predicate if the dimension
 * has increased.
 *
 * Add equations for the new phi variables.
 */
effect adapt_translation_as_convex_effect(effect eff, effect old_eff)
{
  reference r = effect_any_reference(eff);
  list sl = reference_indices(r);
  int n = 1;
  bool substituted_p = false;
  list pl = NIL;
  FOREACH(EXPRESSION, se, sl) {
    syntax ss = expression_syntax(se);
    // FI: I assume that fields are accessed as references
    if(syntax_call_p(ss)) {
      entity phi_n = make_phi_entity(n);
      call c = syntax_call(ss);
      entity f = call_function(c);
      entity zero = int_to_entity(0);
      bool unbounded_p = same_string_p(entity_local_name(f),
				       UNBOUNDED_DIMENSION_NAME);
      if(f==zero || unbounded_p) {
	free_syntax(expression_syntax(se));
	expression_syntax(se) =
	  make_syntax_reference(make_reference(phi_n, NIL));
	substituted_p = true;
      }
      if(!substituted_p) {
	// FI: this function should handle the zero and unbounded cases
	adapt_phi_n_variable_in_convex_effect(eff, se, phi_n);
      }
      if(unbounded_p) {
	/* The translation is not precise */
	pl = CONS(ENTITY, phi_n, pl);
      }
    }
    n++;
  }

  /* Adapt the phi variables in the predicate when the dimension of
   * the new effect is strictly larger
   */

  reference or = effect_any_reference(old_eff);
  list osl = reference_indices(or);
  int od = (int) gen_length(osl);
  int delta = (int) gen_length(sl) - od;
  // The new reference has always more subscrits than the old one
  // Except with constrant strings: "world" and "update2:_p_1[PHI1]"
  // Because in this case, "world" has not been subscripted...
  // The internal representation shuold be fixed
  // pips_assert("delta is positive", delta>=0);
  if(delta>0) {
    int i;
    descriptor d = effect_descriptor(eff); // Assumed convex
    Psysteme sc = descriptor_convex(d);
    for(i=1; i<=od; i++) {
      // Substitute phi_i by phi_{i+delta}
      entity phi_i = make_phi_entity(i);
      entity phi_i_plus_delta = make_phi_entity(i+delta);
      descriptor_convex(d) = sc_variable_rename(sc, phi_i, phi_i_plus_delta);
    }
    // Add equations phi_i == 0 if useful
    list cs = sl;
    for(i=1;i<=delta;i++) {
      expression s = EXPRESSION(CAR(cs));
      if(expression_reference_p(s)) {
	reference r = expression_reference(s);
	entity phi = reference_variable(r);
	if(phi_entity_rank(phi)==i) { // No need to do anything for fields
	  Pvecteur v = vect_make_1D(VALUE_ONE, (Variable) phi, VALUE_ZERO);
	  Pcontrainte c = contrainte_make(v);
	  sc = sc_equation_add(sc, c);
	}
	else if(entity_field_p(phi)) {
	  // Do nothing
	  ;
	}
	else {
	  normalized ns = NORMALIZE_EXPRESSION(s);
	  entity phi_i = make_phi_entity(i);
	  if(unbounded_expression_p(s)) {
	    ; // no information about phi_i
	  }
	  else if(normalized_linear_p(ns)) {
	    Pvecteur v = vect_dup(normalized_linear(ns));
	    vect_add_elem(&v, (Variable) phi_i, VALUE_MONE);
	    Pcontrainte c = contrainte_make(v);
	    sc = sc_equation_add(sc, c);
	  }
	  else {
	    // No information about phi
	    ;
	  }
	  expression_syntax(s) = make_syntax_reference(make_reference(phi_i,NIL));
	  free_normalized(expression_normalized(s));
	  // expression_normalized(s) = NORMALIZE_EXPRESSION(s);
	  expression_normalized(s) = normalized_undefined;
	}
      }
      POP(cs);
    }
  }

  /* Eliminate phi variables that are related to an imprecise translation
   * and set the approximation to MAY.
   */
  if(!ENDP(pl)) {
    approximation app = effect_approximation(eff);
    if(approximation_exact_p(app) || approximation_must_p(app)) {
      free_approximation(app);
      effect_approximation(eff) = make_approximation_may();
      region_exact_projection_along_variables(eff, pl);
    }
    
    gen_free_list(pl);
  }

  return eff;
}

/* If both "se", source entity, and "de", destination entity, are
 * defined, substitute the values of "se" by the values of "de" in
 * "backward_p" mode, when translating a callee transformer at a call
 * site of a caller.
 *
 * If the "se" entity cannot be substituted, its value must be
 * project.
 */
static effect substitute_scalar_stub_in_convex_array_region(effect eff, entity se, entity de, bool backward_p, list * ppl)
{
  if(entity_undefined_p(se))
    ;
  else if(entity_undefined_p(de))
    *ppl = CONS(ENTITY, se, *ppl);
  else if(entity_has_values_p(de)) {
    // Not in the caller's frame
    // entity nsv = entity_to_new_value(se);
    entity nsv = se;
    entity ndv = entity_to_new_value(de);
    if(backward_p) { // For transformers
      region_value_substitute(eff, nsv, ndv);
    }
    else { // For preconditions
      region_value_substitute(eff, ndv, nsv);
    }
  }
  else {
    // FI: could be some debugging stuff
    pips_user_warning("Stub \"%s\" cannot be substituted.\n",
		      entity_user_name(de));
    // FI: entity "de" must be projected
    *ppl = CONS(ENTITY, se, *ppl);
  }
  return eff;
}

static effect substitute_struct_stub_in_convex_array_region(effect eff, reference l, type lt, reference r, type rt __attribute__((unused)), bool backward_p, list *ppl)
{
  list fl = struct_type_to_fields(lt);
  FOREACH(ENTITY, f, fl) {
    type ft = entity_basic_concrete_type(f);
    if(analyzed_type_p(ft)) {
      reference r1 = add_subscript_to_reference(copy_reference(l), 
						entity_to_expression(f));
      reference r2 = add_subscript_to_reference(copy_reference(r), 
						entity_to_expression(f));
      entity l1 = constant_memory_access_path_to_location_entity(r1);
      entity l2 = constant_memory_access_path_to_location_entity(r2);

      if(!entity_undefined_p(l1)) {
	if(!entity_undefined_p(l2)) {
	  eff = substitute_scalar_stub_in_convex_array_region(eff, l1, l2, backward_p, ppl);
	}
      }
      else {
	// pips_internal_error("Not implemented yet.\n");
	// Do nothing, this field may simply be not used
	;
      }
      free_reference(r1);
      free_reference(r2); // another option would be to remove the last subscript
    }
    else if(type_struct_variable_p(ft)) {
      // This piece of code could be integrate in the previous
      // alternative to share most of its code
      reference l1 = add_subscript_to_reference(copy_reference(l), 
						entity_to_expression(f));
      reference r1 = add_subscript_to_reference(copy_reference(r), 
						entity_to_expression(f));
      // GO down recursively
      eff = substitute_struct_stub_in_convex_array_region(eff, l1, ft, r1, ft, backward_p, ppl);
    }
  }
  return eff;
}

/* Exploit the binding map to substitute calles's stubs by actual
 * arguments, which may be stubs of the callers,
 *
 * backward_p request a substitution from the callees' frame into the
 * caller's frame, which is useful for transformers. Flag backward_p is
 * set to false to compute ???
 */
effect substitute_stubs_in_convex_array_region(effect eff, bool backward_p, set binding)
{
  if(pt_to_list_undefined_p()) {
    // Return eff as is ?
    ;
  }
  else {
    if(!set_undefined_p(binding)) {
      list pl = NIL; // FI: I am not sure we can managed forward and
		     // backward projections with one variable
      SET_FOREACH(points_to, pt, binding) {
	approximation ap = points_to_approximation(pt);
	if(approximation_exact_p(ap) || approximation_must_p(ap)) {
	  cell s = points_to_source(pt); // callee
	  cell d = points_to_sink(pt); // caller
	  reference sr = cell_any_reference(s);
	  reference dr = cell_any_reference(d);
	  list srs = reference_indices(sr);
	  list drs = reference_indices(dr);
	  if(ENDP(srs) && ENDP(drs)) {
	    entity se = reference_variable(sr);
	    entity de = reference_variable(dr);
	    if(entity_has_values_p(de))
	      eff = substitute_scalar_stub_in_convex_array_region(eff, se, de, backward_p, &pl);
	    else {
	      type se_t = entity_basic_concrete_type(se);
	      type de_t = entity_basic_concrete_type(de);
	      if(type_struct_variable_p(se_t)) {
		eff = substitute_struct_stub_in_convex_array_region(eff, sr, se_t, dr, de_t, backward_p, &pl);
	      }
	      else
		pl = CONS(ENTITY, se, pl);
	    }
	  }
	  else if(ENDP(srs) && !ENDP(drs)) {
	    entity se = reference_variable(sr);
	    if(analyzed_reference_p(dr)) {
	      entity de = constant_memory_access_path_to_location_entity(dr);
	      eff = substitute_scalar_stub_in_convex_array_region(eff, se, de, backward_p, &pl);
	    }
	    else {
	      pl = CONS(ENTITY, se, pl);
	    }
	  }
	  else if(!ENDP(srs) && ENDP(drs)) {
	    entity de = reference_variable(dr);
	    if(entity_has_values_p(de)) {
	      entity se = constant_memory_access_path_to_location_entity(dr);
	      if(!entity_undefined_p(se))
		eff = substitute_scalar_stub_in_convex_array_region(eff, se, de, backward_p, &pl);
	      else
		pips_internal_error("Not implemented yet.\n");
	    }
	    else {
	      type de_t = entity_basic_concrete_type(de);
	      if(type_struct_variable_p(de_t)) {
		eff = substitute_struct_stub_in_convex_array_region(eff, sr, de_t, dr, de_t, backward_p, &pl);
	      }
	      else {
		// Do nothing
		// entity se = reference_variable(sr);
		// pl = CONS(ENTITY, se, pl);
		;
	      }
	    }
	  }
	  else { // !ENDP(srs) & !ENDP(drs)
	    if(analyzed_reference_p(dr)) {
	      entity se = constant_memory_access_path_to_location_entity(sr);
	      entity de = constant_memory_access_path_to_location_entity(dr);
	      eff = substitute_scalar_stub_in_convex_array_region(eff, se, de, backward_p, &pl);
	    }
	    else {
	      type st = points_to_reference_to_concrete_type(sr);
	      type cst = compute_basic_concrete_type(st);
	      if(type_struct_variable_p(cst))
		eff = substitute_struct_stub_in_convex_array_region(eff, sr, cst, dr, cst, backward_p, &pl);
	      else {
		// No useful information in this binding
		;
	      }
	    }
	  }
	}
      }
      if(!ENDP(pl)) {
	// Get rid on untranslatable entities
	// pips_internal_error("Not implemented yet.\n");
	//eff = safe_region_projection(eff, pl);
	; // do nothing and let another function perform the clean-up.
      }
    }
  }

  return eff;
}

#else // no HAVE_PIPS_points_to_LIBRARY
// typedef set points_to_graph

// FI: I do not believe we need to declare stubs because the function
// above is called from within semantics-generic/points_to.c, by a
// function that is guarded too

#if false
set user_call_to_points_to_interprocedural_binding_set(call c,
						       pt_map pt_caller)
{
  pips_internal_error("points-to library not available");
  return NIL;
}
#endif
#endif // HAVE_PIPS_points_to_LIBRARY
