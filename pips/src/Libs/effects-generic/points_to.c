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
//#include "properties.h"

#include "ri.h"
#include "effects.h"

#include "ri-util.h"
//#include "prettyprint.h"
#include "effects-util.h"
#include "resources.h"
#include "pipsdbm.h"

// For semantics_user_warning()
#include "transformer.h"
#include "semantics.h"

//#include "text-util.h"
#include "effects-generic.h"
//#include "effects-simple.h"
#include "effects-convex.h"

#include "pips-libs.h"
#ifdef HAVE_PIPS_points_to_LIBRARY

#include "points-to.h"

/*
 * Functions relying on points-to.h
 */

/* Special wrapping for the effects analyses
 *
 * FI: check if new cells are allocated to build the returned location
 * list ll...
 */
list effects_expression_to_points_to_sources(expression e)
{
  points_to_graph ptg = points_to_graph_undefined;
  if (!pt_to_list_undefined_p()) {
    statement curstat =  get_current_statement_from_statement_global_stack();
    ptg = get_points_to_graph_from_statement(curstat);
  }

  list ll = expression_to_points_to_sources(e, ptg);
  return ll;
}

/* Returns a list of cells */
list effects_expression_to_points_to_sinks(expression e)
{
  list ll = list_undefined;

  /* Points to are not as precise as proper effects because they are
   * based on cumulated effects. Let's try to get more precise
   * locations when an address of operator is used.
   */
  if(expression_call_p(e)) {
    call c = expression_call(e);
    entity f = call_function(c);
    if(ENTITY_ADDRESS_OF_P(f)) {
      expression a = EXPRESSION(CAR(call_arguments(c)));
      if(expression_reference_p(a)) {
	reference r = expression_reference(a);
	// memory_dereferencing_p
	bool exact_p;
	if(!effect_reference_dereferencing_p(r, &exact_p)) {
	  cell nc = make_cell_reference(copy_reference(r));
	  ll = CONS(CELL, nc, NIL);
	}
      }
      else {
	// This function is not as precise because it deals with
	// constant effects only
	ll = effects_expression_to_points_to_sources(a);
      }
    }
  }
#if false
  // FI: is handled at a higher level
  // if(!get_bool_property("CONSTANT_PATH_EFFECTS")) {
  if(!get_constant_paths_p()) {
    if(expression_reference_p(e)) {
      // Express the dereferencing with an additional subscript
      reference r = expression_reference(e);
      reference nr = copy_reference(r);
      reference_indices(nr) =
	gen_nconc(reference_indices(nr),
		  make_unbounded_subscripts(1));
      cell nc = make_cell_reference(copy_reference(r));
      ll = CONS(CELL, nc, NIL);
    }
    else {
      list pel = NIL;
      list el = generic_proper_effects_of_complex_address_expression(e, &pel, 0);
      gen_free_list(el); // It is not needed. Memory leak ?
    }
  }
#endif

  if(list_undefined_p(ll)) {
    if(pt_to_list_undefined_p()) {
      type t = points_to_expression_to_concrete_type(e);
      cell c = make_anywhere_points_to_cell(t);
      ll = CONS(CELL, c, NIL);
    }
    else {
      statement curstat =  get_current_statement_from_statement_global_stack();
      points_to_graph ptg = get_points_to_graph_from_statement(curstat);
      ll = expression_to_points_to_sinks(e, ptg);
    }
  }
  return ll;
}

/* Compute the mapping between the formal context of the callee and
 * the actual context of the caller.
 *
 * Formal arguments are not involved here, just the formal stubs
 * created by the points-to analysis.
 */
set safe_user_call_to_points_to_interprocedural_binding_set(entity callee,
							    list real_args)
{
  set binding = set_undefined;
  if(get_pointer_info_kind()==with_points_to) {
    statement s = effects_private_current_stmt_head();
    points_to_graph ptg = get_points_to_graph_from_statement(s);
    bool bottom_p = points_to_graph_bottom(ptg);

    if(bottom_p) {
      /* The callee does not return. The standard PIPS memory effects
	 due to the call still do exists as they may interfere with
	 parallelization. */
      ; // FI: temporary way out of the problem
    }
    else {
      call c = make_call(callee, real_args);
      binding = user_call_to_points_to_interprocedural_binding_set(c, ptg);
      call_arguments(c) = NIL;
      free_call(c);
    }
  }
  return binding;
}

void effect_backward_translation_error(entity callee, effect eff)
{
  /* The effect cannot be translated (probably) because the caller
     has not initialized the calling context properly. See for
     instance EffectsWithPointsTo/struct08.c: the main function
     does not initialize p, q, r or s before calling the
     initialization functions. */
  /* FI: not in the points-to context, look for a way to retrieve
     the statement number... */
  approximation a = effect_approximation(eff);
  // FI: this whole function
  // backward_translation_of_points_to_formal_context_effect()
  // should be in library effect_simple
  string effect_to_string(effect);
  if(approximation_exact_p(a) || approximation_must_p(a)) {
    // FI: the pass environment must be reset before the user error
    // is raised or PIPS is likely to core dump later
    // See resets in proper_effects_engine() unless there is a special
    // function, effects_pips_user_error(), but I did not find it
    semantics_user_warning("Exact effect \"%s\" of callee \"%s\" cannot be translated. "
		    "Check that the caller \"%s\" provides initialized "
		    "parameters.\n", effect_to_string(eff), 
		    entity_user_name(callee),
		    entity_user_name(get_current_module_entity()));
  }
  else {
    semantics_user_warning("May effect \"%s\" of callee \"%s\" cannot be translated. "
		      "Check that the caller \"%s\" provides initialized "
		      "parameters.\n", effect_to_string(eff), 
		      entity_user_name(callee),
		      entity_user_name(get_current_module_entity()));
  }
}

/* 
 * Return a list of actual effects corresponding to an effect on the
 * formal context "eff".
 *
 */
list backward_translation_of_points_to_formal_context_effect(entity callee,  list real_args __attribute__((unused)),  effect eff, set binding)
{
  list ael = NIL; // Actual effect list

  if (get_pointer_info_kind()!=with_points_to) {
    // This may occur at least with coarse_grain_parallelization()
    pips_user_warning("Inconsistency: points-to summary effects are used"
		      " to compute call site effects without points-to "
		      "information.\n");
    ael = effect_to_constant_path_effects_with_no_pointer_information(eff);
  }
  else if(!set_undefined_p(binding)) {
    ifdebug(8) print_points_to_set("binding", binding);
    effect n_eff ;
    if(descriptor_convex_p(effect_descriptor(eff))) {
      n_eff = copy_effect(eff);
      // Update the convex descriptor first
      n_eff = substitute_stubs_in_convex_array_region(n_eff, true, binding);
    }
    else{
      n_eff = copy_effect(eff);
    }
 
    cell n_eff_c = effect_cell(n_eff);
    points_to_graph bm_g = make_points_to_graph(false, binding);
    list n_eff_cells = points_to_source_to_translations(n_eff_c, bm_g, true);

    // pips_assert("The effect is translated", !ENDP(n_eff_cells));

    if(ENDP(n_eff_cells)) {
      /* Let's try again with PHI1 variable substituted by 0
       * <update1:_a_1[PHI1].var1-W-EXACT-{PHI1==0}> must be replaced
       * by equivalent convex effect update1:_a_1[0].var1-W-EXACT-{}
       *
       * Since points-to information does not use phi variables, all
       * have to be replaced by 0 to attempt the translation. For instance:
       *
       * <compute1:_a_1_3__1[PHI1][PHI2]-R-EXACT-{PHI1==0, 0<=PHI2,
       * PHI2<=99, compute1:_a_1[0][var1]==8}>
       *
       * Using
       *
       * compute1:_a_1_3__1[0][0]->update1:*HEAP*_l_12[0] (exact)
       *
       * where exact is doubtful when dealing with heap allocated locations.
       */
      if(adapt_convex_effect_cell_to_backward_translation(n_eff)) {
	n_eff_cells = points_to_source_to_translations(n_eff_c, bm_g, true);
      } 
      if(ENDP(n_eff_cells)) {
	effect_backward_translation_error(callee, eff);
	action a = copy_action(effect_action(eff));
	effect d = make_anywhere_effect(a);
	ael = CONS(EFFECT, d, NIL);
      }
    }

    points_to_graph_set(bm_g) = set_undefined;
    free_points_to_graph(bm_g);

    FOREACH(CELL, n_c, n_eff_cells) {
      if(!null_cell_p(n_c) && !nowhere_cell_p(n_c)) {
	action ac = copy_action(effect_action(eff));
	approximation ap = heap_cell_p(n_c) ?
	  make_approximation_may()
	  : copy_approximation(effect_approximation(eff));
	descriptor d = copy_descriptor(effect_descriptor(n_eff));
	effect nn_eff =  make_effect(n_c, ac, ap, d);
	if(descriptor_convex_p(d))
	  nn_eff = adapt_translation_as_convex_effect(nn_eff, eff);
	ael = CONS(EFFECT, nn_eff, ael);
      }
    }

    /* FI: if n_eff_cells is not empty, empty(ael) means that the
     * input code is wrong because a pointer has not been initialized
     * properly...
     *
     * But, the translation error may occur on an may effect that is
     * an overapproximation. So a user error is not 100 % sure and
     * ael may be empty.
     */
    approximation a = effect_approximation(eff);
    if(approximation_exact_p(a) || approximation_must_p(a))
      pips_assert("The effect is translated", !ENDP(ael));
  }
  else {
    /* Incompatibility between call site and callee */
    pips_user_error("Incompatibility between call site and callee.\n");
    gen_free_list(ael);
    ael = NIL;
  }

  return ael;
}

#else // no HAVE_PIPS_points_to_LIBRARY

/*
 * Local stubs for the functions relying on points-to.h
*/

// typedef set points_to_graph

set safe_user_call_to_points_to_interprocedural_binding_set(entity callee __attribue__((unused)),
							    list real_args __attribue__((unused)))
{
  set binding = set_undefined;
  return binding;
}

static list backward_translation_of_points_to_formal_context_effect(
  _UNUSED_ entity callee, _UNUSED_ list real_args, _UNUSED_ effect eff _UNUSED_ set binding)
{
  pips_internal_error("points-to library not available");
  return NIL;
}

#endif // HAVE_PIPS_points_to_LIBRARY

/* Returns a list of cells corresponding to the possibles values,
 * i.e. abstract or concrete locations, denoted by lhs expression e.
 *
 * This should work whether the points-to library is
 * available or not, but it is not yet the case.
 *
 * The prefix effects_ is used to have a local copy in the
 * effects-generic library.
 */
list effects_lhs_expression_to_sources(expression e)
{
  /* We expect here a test about points-to availability and a work
   * around if the points-to library is not linked.
   */
  return effects_expression_to_points_to_sources(e);
}

/* Returns a list of cells corresponding to the value,i.e. abstract or
 * concrete locations, denoted by lhs expression e.
 *
 * If "p" is a pointer, expression "p" has "p" as a source, and the
 * sources of "*p" as sinks.
 *
 * This should work whether the points-to library is
 * available or not, but it is not yet the case
 *
 * The prefix effects_ is used to have a local copy in the
 * effects-generic library.
 */
list effects_lhs_expression_to_sinks(expression e)
{
  /* We expect here a test about points-to availability and a work
   * around if the points-to library is not linked.
   */
  return effects_expression_to_points_to_sinks(e);
}

list cells_to_read_or_write_effects(list cl, bool write_p)
{
  // (*reference_to_effect_func)
  list wel = NIL;
  size_t n = gen_length(cl);
  size_t u = 0; // number of useless cells
  FOREACH(CELL, c, cl) {
    effect e = effect_undefined;
    if(nowhere_cell_p(c)) {
      if(n==1 || n==1+u) {
	// Would it be better to move on with a simple warning?
	pips_user_error("Dereferencing of an undefined pointer.\n");
      }
      else {
	; // ignore
      }
      u++;
    }
    else if(null_cell_p(c)) {
      if(n==1 || n==1+u)
	pips_user_error("Dereferencing of a null pointer.\n");
      else {
	; // ignore
      }
      u++;
    }
    else {
      action a = write_p? make_action_write_memory() : make_action_read_memory();
      //descriptor d = make_descriptor_none();
      if(cell_abstract_location_p(c)) {
	// This may always capture heap locations, although they may
	// sometimes be concrete
	// approximation ap = make_approximation_may();
	reference r = cell_any_reference(c);
	e = (*reference_to_effect_func)(r, a, false); // , ap, d);
      }
      else {
	reference r = cell_any_reference(c);
	e = (*reference_to_effect_func)(r, a, false); // , ap, d);
	if(n==1 || n==1+u) {
	//  approximation ap = make_approximation_exact();
	  //  e = make_effect(c, a, ap, d);
	  ;
	}
	else {
	  // FI: it could be exact with n>1 if alternatives are null
	  // and undefined
	  //approximation ap = make_approximation_may();
	  // e = make_effect(c, a, ap, d);
	  ;
	}
      }
      // Adjust type, which implies a may approximation
      type t = points_to_cell_to_concrete_type(c);
      int msn = type_depth(t);
      if(msn>0) {
	reference r = cell_any_reference(c);
	reference_indices(r) = gen_nconc(reference_indices(r), 
					 make_unbounded_subscripts(msn));
	if(approximation_exact_p(effect_approximation(e))) {
	  free_approximation(effect_approximation(e));
	  effect_approximation(e) = make_approximation_may();
	}
	entity re = reference_variable(r);
	if(entity_typed_anywhere_locations_p(re)) {
	  // FI: we hope that heap entities are not included here
	  pips_assert("Not a heap abstraction", !entity_heap_location_p(re));
	  type nt = points_to_reference_to_concrete_type(r);
	  entity nre = entity_typed_anywhere_locations(nt);
	  reference_variable(r) = nre;
	  gen_full_free_list(reference_indices(r));
	  reference_indices(r) = NIL;
	}
      }
    }
    if(!effect_undefined_p(e))
      wel = gen_nconc(wel, CONS(EFFECT, e, wel));
  }

  effects_to_proper_approximation(wel);
  add_precondition_information_to_effects(wel);

  return wel;
}

list cells_to_write_effects(list cl)
{
  return cells_to_read_or_write_effects(cl, true);
}

list cells_to_read_effects(list cl)
{
  return cells_to_read_or_write_effects(cl, false);
}
