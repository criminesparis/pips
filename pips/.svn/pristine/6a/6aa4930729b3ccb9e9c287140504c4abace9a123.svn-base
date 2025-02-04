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

#include "pips-libs.h"
#ifdef HAVE_PIPS_points_to_LIBRARY
// for get_points_to_graph_from_statement & expression_to_points_to_sinks
#include "points-to.h" // 2 or more functions
#else // no HAVE_PIPS_points_to_LIBRARY
// typedef set points_to_graph
points_to_graph get_points_to_graph_from_statement(
  _UNUSED_ statement st)
{
  pips_internal_error("points-to library not available");
  return NULL;
}

list expression_to_points_to_sinks(
  _UNUSED_ expression e,
  _UNUSED_ points_to_graph in)
{
  pips_internal_error("points-to library not available");
  return NIL;
}

list expression_to_points_to_sources(
  _UNUSED_ expression e,
  _UNUSED_ points_to_graph in)
{
  pips_internal_error("points-to library not available");
  return NIL;
}

set user_call_to_points_to_interprocedural_binding_set(call c,
						       pt_map pt_caller)
{
  pips_internal_error("points-to library not available");
  return NIL;
}
#endif // HAVE_PIPS_points_to_LIBRARY

#include "transformer.h"

/* Special wrapping for the semantics analyses
 *
 * FI: check if new cells are allocated to build the returned location
 * list ll...
 */
list semantics_expression_to_points_to_sources(expression e)
{
  points_to_graph ptg = points_to_graph_undefined;
  if (!pt_to_list_undefined_p()) {
    statement curstat =  get_current_statement_from_statement_global_stack();
    if(statement_undefined_p(curstat)) {
      // The points-to IN information should be used
      ;
    }
    else
      ptg = get_points_to_graph_from_statement(curstat);
  }

  list ll = expression_to_points_to_sources(e, ptg);
  return ll;
}

/* Returns a list of cells */
list semantics_expression_to_points_to_sinks(expression e)
{
  list ll = list_undefined;
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
  return ll;
}

/* If both "se", source entity, and "de", destination entity, are
 * defined, substitute the values of "se" by the values of "de" in
 * "backward_p" mode, when translating a callee transformer at a call
 * site of a caller.
 *
 * If the "se" entity cannot be substituted, its value must be
 * project.
 */
transformer substitute_scalar_stub_in_transformer(transformer tf, entity se, entity de, bool backward_p, list * ppl)
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
      tf = transformer_value_substitute(tf, nsv, ndv);
    }
    else { // For preconditions
      tf = transformer_value_substitute(tf, ndv, nsv);
    }
    // Careful, se has been substituted in the argument too
    if(entity_is_argument_p(de, transformer_arguments(tf))) {
      entity osv = global_new_value_to_global_old_value(nsv);
      entity odv = entity_to_old_value(de);
      if(backward_p) { // For transformers
	tf = transformer_value_substitute(tf, osv, odv);
      }
      else { // For preconditions
	tf = transformer_value_substitute(tf, odv, osv);
      }
    }
  }
  else {
    // FI: could be some debugging stuff
    pips_user_warning("Stub \"%s\" cannot be substituted.\n",
		      entity_user_name(de));
    // FI: entity "de" must be projected
    *ppl = CONS(ENTITY, se, *ppl);
  }
  return tf;
}

transformer substitute_struct_stub_in_transformer(transformer t, reference l, type lt, reference r, type rt __attribute__((unused)), bool backward_p, list *ppl)
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
	  t = substitute_scalar_stub_in_transformer(t, l1, l2, backward_p, ppl);
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
      if(array_type_p(ft)) {
	// FI: how do we guess the subscript values? we could try to
	// infer them from the values used in the transformer or we
	// can generate all possible subscripts...

	// FI: a special case, used for debugging only
	l1 = add_subscript_to_reference(l1, int_to_expression(1));
	r1 = add_subscript_to_reference(r1, int_to_expression(1));
      }

      // GO down recursively
      t = substitute_struct_stub_in_transformer(t, l1, ft, r1, ft, backward_p, ppl);
    }
  }
  return t;
}

/* The sources of the relevant points-to */
static bool relevant_translation_pair_p(points_to pt, list ll)
{
  bool relevant_p = false;
  cell d = points_to_sink(pt); // callee if backward_p
  reference dr = cell_any_reference(d);
  entity de = reference_variable(dr);
  relevant_p = gen_in_list_p((const void *) de, ll);

  return relevant_p;
}

/* Exploit the binding map to substitute calles's stubs by actual
 * arguments, which may be stubs of the callers,
 *
 * backward_p request a substitution from the callees' frame into the
 * caller's frame, which is useful for transformers. Flag backward_p is
 * set to false to compute summary preconditions.
 *
 * FI: this function is now only used for preconditions. It has been
 * rewritten for transformers to speed up the process when array
 * elements are involved. It is better to start from the needs, the
 * stubs used in the transformer, than from all possible stubs, but it
 * is much easier for a backward translation. With a forward
 * translation, regular variables may have to be translated into
 * stubs.
 *
 * FI: A quick improvement would to return when no translation is
 * needed... but you do not always know it when backward_p is set to
 * false.
 */
transformer substitute_stubs_in_transformer(transformer tf, call c, statement s, bool backward_p)
{
  entity m = get_current_module_entity();
  list ll = backward_p? transformer_to_analyzed_locations(tf)
    : transformer_to_potential_stub_translation(tf, m);
  if(ENDP(ll)) {
    // Return tf as is
    ;
  }
  else if(pt_to_list_undefined_p()) {
    // Return tf as is
  }
  else {
    points_to_graph ptg = get_points_to_graph_from_statement(s);
    bool bottom_p = points_to_graph_bottom(ptg);

    if(bottom_p) {
      // FI: should this lead to an empty transformer?
      pips_internal_error("Not implemented yet.\n");
    }
    else {
      set binding = user_call_to_points_to_interprocedural_binding_set(c, ptg);
      list pl = NIL; // FI: I am not sure we can managed forward and
		     // backward projections with one variable
      SET_FOREACH(points_to, pt, binding) {
	approximation ap = points_to_approximation(pt);
	if(relevant_translation_pair_p(pt, ll) 
	   && (approximation_exact_p(ap) || approximation_must_p(ap))) {
	  cell s = points_to_source(pt); // callee if backward_p
	  cell d = points_to_sink(pt); // caller if backward_p
	  reference sr = cell_any_reference(s);
	  reference dr = cell_any_reference(d);
	  // This test should be useless because this is guaranteed by
	  // the approximation, except if binding is corrupted.
	  if(atomic_points_to_reference_p(dr)) {
	    list srs = reference_indices(sr);
	    list drs = reference_indices(dr);
	    if(ENDP(srs) && ENDP(drs)) {
	      entity se = reference_variable(sr);
	      entity de = reference_variable(dr);
	      //type se_t = entity_basic_concrete_type(se);
	      //type de_t = entity_basic_concrete_type(de);
	      if(entity_has_values_p(de))
		tf = substitute_scalar_stub_in_transformer(tf, se, de, backward_p, &pl);
	      else {
		type se_t = entity_basic_concrete_type(se);
		type de_t = entity_basic_concrete_type(de);
		if(type_struct_variable_p(se_t)) {
		  tf = substitute_struct_stub_in_transformer(tf, sr, se_t, dr, de_t, backward_p, &pl);
		}
		else
		  pl = CONS(ENTITY, se, pl);
	      }
	    }
	    else if(ENDP(srs) && !ENDP(drs)) {
	      entity se = reference_variable(sr);
	      if(analyzed_reference_p(dr)) {
		entity de = constant_memory_access_path_to_location_entity(dr);
		tf = substitute_scalar_stub_in_transformer(tf, se, de, backward_p, &pl);
	      }
	      else {
		pl = CONS(ENTITY, se, pl);
	      }
	    }
	    else if(!ENDP(srs) && ENDP(drs)) {
	      entity de = reference_variable(dr);
	      if(entity_has_values_p(de)) {
		entity se = constant_memory_access_path_to_location_entity(sr);
		if(!entity_undefined_p(se))
		  tf = substitute_scalar_stub_in_transformer(tf, se, de, backward_p, &pl);
		else
		  pips_internal_error("Not implemented yet.\n");
	      }
	      else {
		type de_t = entity_basic_concrete_type(de);
		if(type_struct_variable_p(de_t)) {
		  tf = substitute_struct_stub_in_transformer(tf, sr, de_t, dr, de_t, backward_p, &pl);
		  // tf = substitute_struct_stub_reference_in_transformer(tf, sr, de, backward_p, &pl);
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
		tf = substitute_scalar_stub_in_transformer(tf, se, de, backward_p, &pl);
	      }
	      else {
		type st = reference_to_type(sr);
		type cst = compute_basic_concrete_type(st);
		if(type_struct_variable_p(cst))
		  tf = substitute_struct_stub_in_transformer(tf, sr, cst, dr, cst, backward_p, &pl);
		else {
		  // No useful information in this binding
		  ;
		}
	      }
	    }
	  }
	}
      }
      if(!ENDP(pl)) {
	// Get rid on untranslatable entities
	tf = safe_transformer_projection(tf, pl);
      }
    }
  }

  gen_free_list(ll);

  return tf;
}

static transformer substitute_stubs_in_transformer_with_translation_binding(transformer tf, pt_map binding_g, bool backward_p)
{
  pips_assert("Backward only", backward_p);
  list ll = transformer_to_analyzed_locations(tf);
  FOREACH(ENTITY, l, ll) {
    type lt = entity_basic_concrete_type(l);
    value val = entity_initial(l);
    entity v = l;
    list sl = NIL;
    if(value_reference_p(val)) {
      reference r = value_reference(val); // By definition of list ll
      v = reference_variable(r);
      sl = reference_indices(r);
    }
    list tcrl = reference_to_points_to_translations(v, sl, binding_g);
    FOREACH(CELL, tcr, tcrl) {
      reference tr = cell_any_reference(tcr);
      type trt = points_to_reference_to_concrete_type(tr);
      // FI: The type checking should be useless, but for constant
      // character strings which appear as a pointer to a char,
      // i.e. an integer, and is analyzed as such in the callee
      if(type_equal_p(lt, trt)
	 && generic_atomic_points_to_reference_p(tr, false)) {
	entity tl = constant_memory_access_path_to_location_entity(tr);
	if(!entity_undefined_p(tl)) {
	  entity nlv = external_entity_to_new_value(l);
	  entity ntlv = entity_to_new_value(tl);
	  tf = transformer_value_substitute(tf, nlv, ntlv);
	  if(entity_is_argument_p(ntlv, transformer_arguments(tf))) {
	    entity olv = external_entity_to_old_value(l);
	    entity otlv = entity_to_old_value(tl);
	    tf = transformer_value_substitute(tf, olv, otlv);
	  }
	}
      }
    }
    gen_free_list(tcrl);
  }
  gen_free_list(ll);
  return tf;
}

transformer new_substitute_stubs_in_transformer(transformer tf, call c, statement s, bool backward_p)
{
  if(pt_to_list_undefined_p()) {
    // Return tf as is
  }
  else {
    points_to_graph ptg = get_points_to_graph_from_statement(s);
    bool bottom_p = points_to_graph_bottom(ptg);

    if(bottom_p) {
      /* This leads to an empty transformer because the statement is
       * unreachable. Some kind of dereferencement error has occured
       * earlier in the execution
       */
      free_transformer(tf);
      tf = transformer_empty();
    }
    else {
      set binding = user_call_to_points_to_interprocedural_binding_set(c, ptg);
      pt_map binding_g = make_points_to_graph(false, binding);
      tf = substitute_stubs_in_transformer_with_translation_binding(tf, binding_g, backward_p);
      free_points_to_graph(binding_g);
    }
  }
  return tf;
}
