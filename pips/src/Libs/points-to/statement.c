/*

  $Id: statement.c 23412 2017-08-09 15:07:09Z irigoin $

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

/*
This file contains functions used to compute points-to sets at statement level.
*/

#include <stdlib.h>
#include <stdio.h>

#include "genC.h"
#include "linear.h"

#include "ri.h"
#include "ri-util.h"

#include "effects.h"
#include "effects-util.h"

#include "misc.h"
#include "properties.h"

#include "points-to.h"

/* FI: short term attempt at providing a deep copy to avoid sharing
 * between sets. If elements are shared, it quickly becomes impossible
 * to deep free any set.
 */
set full_copy_simple_pt_map(set m)
{
  set out = new_simple_pt_map();
  /*
  HASH_MAP(k, v, {
      points_to pt = (points_to) k;
      points_to npt = copy_points_to(pt);
	hash_put( out->table, (void *) npt, (void *) npt );
    }, m->table);
  */
  SET_FOREACH(points_to, pt, m) {
    points_to npt = copy_points_to(pt);
    set_add_element(out, out, (void *) npt);
  }
  return out;
}

pt_map full_copy_pt_map(pt_map in)
{
  // Dynamic type check
  int n = points_to_graph_domain_number(in);
  pips_assert("\"in\" is a points_to_graph", n==points_to_graph_domain);
  pt_map out = new_pt_map();
  set in_s = points_to_graph_set(in);
  set out_s = points_to_graph_set(out);
  SET_FOREACH(points_to, pt, in_s) {
    points_to npt = copy_points_to(pt);
    set_add_element(out_s, out_s, (void *) npt);
  }
  points_to_graph_bottom(out) = points_to_graph_bottom(in);
  return out;
}

/* The input points-to information of a statement is updated by the
 * analysis of the statement because of the on-demand approach. The
 * formal context with its stubs is built onloy when necessary. 
 */
static stack statement_points_to_context = stack_undefined;
static stack current_statement_points_to_context = stack_undefined;

void init_statement_points_to_context()
{
  pips_assert("statement_points_to_context is undefined",
	      stack_undefined_p(statement_points_to_context));
  statement_points_to_context = stack_make(points_to_graph_domain, 0, 0);
  current_statement_points_to_context = stack_make(statement_domain, 0, 0);
}

void push_statement_points_to_context(statement s, pt_map in)
{
  stack_push((void *) in, statement_points_to_context);
  stack_push((void *) s, current_statement_points_to_context);
}

void add_arc_to_statement_points_to_context(points_to pt)
{
  pt_map in = stack_head(statement_points_to_context);
  add_arc_to_pt_map(pt, in);
  //update_points_to_graph_with_arc(pt, in);
  pips_assert("in is consistent", consistent_pt_map_p(in));
}

void update_statement_points_to_context_with_arc(points_to pt)
{
  pt_map in = stack_head(statement_points_to_context);
  //add_arc_to_pt_map(pt, in);
  update_points_to_graph_with_arc(pt, in);
  pips_assert("in is consistent", consistent_pt_map_p(in));
}

int points_to_context_statement_line_number()
{
  //statement s = stack_head(current_statement_points_to_context);
  statement s = get_current_statement_from_statement_global_stack();
  return statement_number(s);
}

pt_map points_to_context_statement_in()
{
  pt_map in = (pt_map) stack_head(statement_points_to_context);
  return in;
}

pt_map pop_statement_points_to_context(void)
{
  (void) stack_pop(current_statement_points_to_context);
  return (pt_map) stack_pop(statement_points_to_context);
}

void reset_statement_points_to_context()
{
  stack_free(&statement_points_to_context);
  statement_points_to_context = stack_undefined;
}

bool statement_points_to_context_defined_p()
{
  return statement_points_to_context != stack_undefined;
}

/* See points_to_statement()
 *
 *
 */
pt_map statement_to_points_to(statement s, pt_map pt_in)
{
  pips_assert("pt_in is consistent", consistent_pt_map_p(pt_in));
  push_statement_on_statement_global_stack(s);
  upgrade_approximations_in_points_to_set(pt_in);
  pt_map pt_out = new_pt_map();
  pt_out = full_copy_pt_map(pt_in);
  instruction i = statement_instruction(s);

  if(points_to_graph_bottom(pt_in)) {
    // The information about dead code must be propagated downwards
    pt_out = instruction_to_points_to(i, pt_out);
    pips_assert("The resulting points-to graph is bottom",
		points_to_graph_bottom(pt_out));
  }
  else {

    init_heap_model(s);
    // FI: it would be nice to stack the current statement in order to
    // provide more helpful error messages
    push_statement_points_to_context(s, pt_in);

    if(declaration_statement_p(s)) {
      /* Process the declarations */
      pt_out = declaration_statement_to_points_to(s, pt_out);
      pips_assert("pt_out is consistent", consistent_pt_map_p(pt_out));
      /* Go down recursively, although it is currently useless since a
	 declaration statement is a call to CONTINUE */
      pt_out = instruction_to_points_to(i, pt_out);
    }
    else {
      pt_out = instruction_to_points_to(i, pt_out);
    }

    pips_assert("pt_out is consistent", consistent_pt_map_p(pt_out));

    /* Get the current version of pt_in, updated by the analysis of s. */
    pt_in = pop_statement_points_to_context();

    pips_assert("pt_in is consistent", consistent_pt_map_p(pt_in));

    reset_heap_model();
  }

  /* Either pt_in or pt_out should be stored in the hash_table 
   *
   * But it might be smarter (or not) to require or not the storage.
   */
  // FI: currently, this is going to be redundant most of the time
  pt_map pt_merged;
  if(bound_pt_to_list_p(s)) {
    points_to_list ptl_prev = load_pt_to_list(s);
    list ptl_prev_l = gen_full_copy_list(points_to_list_list(ptl_prev));
    pt_map pt_prev = new_pt_map();
    pt_prev = graph_assign_list(pt_prev, ptl_prev_l);
    gen_free_list(ptl_prev_l);
    pt_merged = merge_points_to_graphs(pt_in, pt_prev);
  }
  else
    pt_merged = pt_in;
  fi_points_to_storage(pt_merged, s, true);

  /* Eliminate local information if you exit a block */
  if(statement_sequence_p(s)) {
    statement ms = get_current_module_statement();
    entity m = get_current_module_entity();
    bool main_p = ms==s && entity_main_module_p(m);
    bool body_p = ms==s;
    list dl = statement_declarations(s);
    /* The statement context is know unknown: it has been popped
       above. No precise error message in
       points_to_set_block_projection() */
    push_statement_points_to_context(s, pt_in);
    points_to_graph_set(pt_out) =
      points_to_set_block_projection(points_to_graph_set(pt_out), dl, main_p, body_p);
    pt_in = pop_statement_points_to_context();
  }

  /* Because arc removals do not update the approximations of the
     remaining arcs, let's upgrade approximations before the
     information is passed. Useful for arithmetic02. */
  upgrade_approximations_in_points_to_set(pt_out);

  /* Really dangerous here: if pt_map "in" is empty, then pt_map "out"
   * must be empty to...
   *
   * FI: we have a problem to denote unreachable statement. To
   * associate an empty set to them woud be a way to avoid problems
   * when merging points-to along different control paths. But you
   * might also wish to start with an empty set... And anyway, you can
   * find declarations in dead code...
   */
  // FI: a temporary fix to the problem, to run experiments...
  //if(empty_pt_map_p(pt_in) && !declaration_statement_p(s)
  //   && s!=get_current_module_statement())
  //  clear_pt_map(pt_out); // FI: memory leak?

  pips_assert("pt_out is consistent on exit", consistent_pt_map_p(pt_out));

  pop_statement_global_stack();

  return pt_out;
}

/* See points_to_init()
 *
 * pt_in is modified by side-effects and returned
 */
pt_map declaration_statement_to_points_to(statement s, pt_map pt_in)
{
  pt_map pt_out = pt_in;
  //set pt_out = set_generic_make(set_private, points_to_equal_p, points_to_rank);
  list l = NIL;
  //bool type_sensitive_p = !get_bool_property("ALIASING_ACROSS_TYPES");

  list l_decls = statement_declarations(s);

  pips_debug(1, "declaration statement \n");
  
  FOREACH(ENTITY, e, l_decls) {
    type et = entity_basic_concrete_type(e);
    if(pointer_type_p(et)
       || array_of_pointers_type_p(et)
       || struct_type_p(et)
       || array_of_struct_type_p(et)) {
      if( !storage_rom_p(entity_storage(e)) ) {
	// FI: could be simplified with variable_initial_expression()
	value v_init = entity_initial(e);
	/* generate points-to due to the initialisation */
	if(value_expression_p(v_init)){
	  expression exp_init = value_expression(v_init);
	  expression lhs = entity_to_expression(e);
	  type it = compute_basic_concrete_type(expression_to_type(exp_init));
	  // See C standard for type compatibility + PIPS idiosyncrasies
	  // This should be extended to cope with the C type hierarchy
	  // accept side effects
	  pt_out = expression_to_points_to(exp_init, pt_out, true);
	  //if(array_pointer_type_equal_p(et, it)
	  //if(concrete_type_equal_p(et, it)
	  if(type_structurally_equal_p(et, it)
	     || array_pointer_type_equal_p(et, it)
	     || type_void_star_p(et) || type_void_star_p(it)
	     || integer_type_p(it)
	     || (char_star_type_p(et) && string_type_p(it))
	     || overloaded_type_p(it)) // PIPS own compatibility...
	    pt_out = assignment_to_points_to(lhs,
					     exp_init,
					     pt_out);
	  else {
	    pips_user_warning("Type mismatch for initialization of \"%s\" at line %d.\n",
			      entity_user_name(e),
			      points_to_context_statement_line_number());
	    clear_pt_map(pt_out);
	    points_to_graph_bottom(pt_out) = true;
	  }
	  /* AM/FI: abnormal sharing (lhs); the reference may be
	     reused in the cel... */
	  /* free_expression(lhs); */
	}
	else {
	  l = variable_to_pointer_locations(e);
	  // C Standard: if e is a static pointer, it is implicly
	  // initialized to NULL
	  if(pointer_type_p(et) && variable_static_p(e)) {
	    cell source = CELL(CAR(l));
	    cell sink = make_null_cell(); 
	    points_to pt = make_points_to(source, sink,
					  make_approximation_exact(),
					  make_descriptor_none());
	    add_arc_to_pt_map(pt, pt_out);
	    // The declared variable is local
	    // add_arc_to_points_to_context(copy_points_to(pt));
	  }
	  else {
	    FOREACH(CELL, source, l) {
	      cell sink = cell_to_nowhere_sink(source); 
	      points_to pt = make_points_to(source, sink,
					    make_approximation_exact(),
					    make_descriptor_none());
	      add_arc_to_pt_map(pt, pt_out);
	      // The declared variable is local
	      // add_arc_to_points_to_context(copy_points_to(pt));
	    }
	  }
	}
      }
    }
    else {
      /* The initialization expression may use pointers, directly or
	 indirectly via struct and arrays. */
      expression ie = variable_initial_expression(e);
      if(!expression_undefined_p(ie)) {
	pt_out = expression_to_points_to(ie, pt_out, true);
	free_expression(ie);
      }
    }
    /* Take care of expressions in array sizing (see array12.c) */
    if(array_type_p(et)) {
      variable ev = type_variable(et);
      list dl = variable_dimensions(ev);
      FOREACH(DIMENSION, d, dl) {
	expression l = dimension_lower(d);
	expression u = dimension_upper(d);
	pt_out = expression_to_points_to(l, pt_out, true);
	pt_out = expression_to_points_to(u, pt_out, true);
      }
    }
  }
  
  return pt_out;
}

/* See points_to_statement()
 *
 * pt_in is modified by side-effects and returned
 */
pt_map instruction_to_points_to(instruction i, pt_map pt_in)
{
  pt_map pt_out = pt_in;
  tag it = instruction_tag(i);
  switch(it) {
  case is_instruction_sequence: {
    sequence seq = instruction_sequence(i);
    pt_out = sequence_to_points_to(seq, pt_in);
    break;
  }
  case is_instruction_test: {
    test t = instruction_test(i);
    pt_out = test_to_points_to(t, pt_in);
    break;
  }
  case is_instruction_loop: {
    loop l = instruction_loop(i);
    pt_out = loop_to_points_to(l, pt_in);
    break;
  }
  case is_instruction_whileloop: {
    whileloop wl = instruction_whileloop(i);
    pt_out = whileloop_to_points_to(wl, pt_in);
    break;
  }
  case is_instruction_goto: {
    pips_internal_error("Go to instructions should have been removed "
			"before the analysis is started\n");
    break;
  }
  case is_instruction_call: {
    call c = instruction_call(i);
    if(points_to_graph_bottom(pt_in))
      pt_out = pt_in;
    else
      pt_out = call_to_points_to(c, pt_out, NIL, true);
    break;
  }
  case is_instruction_unstructured: {
    unstructured u = instruction_unstructured(i);
    pt_out = unstructured_to_points_to(u, pt_in);
    break;
  }
  case is_instruction_multitest: {
    pips_internal_error("Not implemented\n");
    break;
  }
  case is_instruction_forloop: {
    forloop fl = instruction_forloop(i);
    pt_out = forloop_to_points_to(fl, pt_in);
    break;
  }
  case is_instruction_expression: {
    expression e = instruction_expression(i);
    if(points_to_graph_bottom(pt_in))
      pt_out = pt_in;
    else
      pt_out = expression_to_points_to(e, pt_in, true);
    break;
  }
  default:
    pips_internal_error("Unexpected instruction tag %d\n", it);
  }
  return pt_out;
}

pt_map sequence_to_points_to(sequence seq, pt_map pt_in)
{
  pt_map pt_out = pt_in;
  //bool store = true; // FI: management and use of store_p? Could be useful? How is it used?
  // pt_out = points_to_sequence(seq, pt_in, store);
  FOREACH(statement, st, sequence_statements(seq)) {
    pt_out = statement_to_points_to(st, pt_out);
  }

  return pt_out;
}


/* expand the domain of pt_f according to the domain of pt_t */
static void expand_points_to_domain(points_to_graph pt_t, points_to_graph pt_f)
{
  set s_t = points_to_graph_set(pt_t);
  set s_f = points_to_graph_set(pt_f);
  SET_FOREACH(points_to, a_t, s_t) {
    cell c_t = points_to_source(a_t);
    bool found_p = false;
    SET_FOREACH(points_to, a_f, s_f) {
      cell c_f = points_to_source(a_f);
      if(points_to_cell_equal_p(c_t, c_f)) {
	found_p = true;
	break;
      }
    }
    if(!found_p) {
      reference r_t = cell_any_reference(c_t);
      entity v_t = reference_variable(r_t);
      if(formal_parameter_p(v_t) || entity_stub_sink_p(v_t)) {
	expression e_t = reference_to_expression(r_t);
	pt_f = pointer_assignment_to_points_to(e_t, e_t, pt_f);
	if(points_to_graph_bottom(pt_f))
	  pips_internal_error("Unexpected information loss.");
      }
    }
  }
}

/* Make sure that pt_t and pt_f have the same definition domain except
   if one of them is bottom */
void  equalize_points_to_domains(points_to_graph pt_t, points_to_graph pt_f)
{
  if(!points_to_graph_bottom(pt_t)) {
    if(!points_to_graph_bottom(pt_f)) {
      expand_points_to_domain(pt_t, pt_f);
      expand_points_to_domain(pt_f, pt_t);
    }
  }
}

/* Computing the points-to information after a test.
 *
 * All the relationships are of type MAY, even if the same arc is
 * defined, e.g. "if(c) p = &i; else p=&i;".
 *
 * Might be refined later by using preconditions.
 */
pt_map test_to_points_to(test t, pt_map pt_in)
{
  pt_map pt_out = pt_map_undefined;

  //bool store = true;
  // pt_out = points_to_test(t, pt_in, store);
  // Translation of points_to_test
  statement ts = test_true(t);
  statement fs = test_false(t);
  expression c = test_condition(t);
  pt_map pt_t =  pt_map_undefined;
  pt_map pt_f = pt_map_undefined;

  /* Make sure the condition is exploited, either because of side
   * effects or simply because of dereferencements.
   *
   * This cannot be done here because of side-effects.
   *
   * FI: because the conditions must be evaluated for true and false?
   */
  //pt_in = expression_to_points_to(c, pt_in);
  //list el = expression_to_proper_constant_path_effects(c);
  //if(!effects_write_p(el))
  // pt_in = expression_to_points_to(c, pt_in, true);
  //gen_free_list(el);

  // The side effects won't be taken into account when the condition
  // is evaluated
  pt_in = expression_to_points_to(c, pt_in, true);

  pt_map pt_in_t = full_copy_pt_map(pt_in);
  pt_map pt_in_f = full_copy_pt_map(pt_in);
  
  /* condition's side effect and information are taked into account, e.g.:
   *
   * "if(p=q)" or "if(*p++)" or "if(p)" which implies p->NULL in the
   * else branch. FI: to be checked with test cases */
  if(!points_to_graph_bottom(pt_in_t)) // FI: we are in dead code
    pt_in_t = condition_to_points_to(c, pt_in_t, true);
  pt_t = statement_to_points_to(ts, pt_in_t);

  if(!points_to_graph_bottom(pt_in_f)) // FI: we are in dead code
    pt_in_f = condition_to_points_to(c, pt_in_f, false);
  pt_f = statement_to_points_to(fs, pt_in_f);

  pips_assert("pt_t is consistent", points_to_graph_consistent_p(pt_t));
  pips_assert("pt_f is consistent", points_to_graph_consistent_p(pt_f));

  /* We must use a common definition domain for both relations in
     order to obatin a really consistent points-to relation after the
     merge. This is similar to what is done in semantics for scalar
     preconditions. */
  equalize_points_to_domains(pt_t, pt_f);
  
  pt_out = merge_points_to_graphs(pt_t, pt_f);

  pips_assert("pt_out is consistent", points_to_graph_consistent_p(pt_out));

  // FI: we should take care of pt_t and pt_f to avoid memory leaks
  // In that specific case, clear_pt_map() and free_pt_map() should be ok

  pips_assert("pt_out is consistent", points_to_graph_consistent_p(pt_out));

  set_clear(points_to_graph_set(pt_t));
  set_clear(points_to_graph_set(pt_f));
  free_pt_map(pt_t), free_pt_map(pt_f);

  pips_assert("pt_out is consistent", points_to_graph_consistent_p(pt_out));

  return pt_out;
}

/* FI: I assume that pointers and pointer arithmetic cannot appear in
 * a do loop, "do p=q, r, 1" is possible with "p", "q" and "r"
 * pointing towards the same array... Let's hope the do loop
 * conversion does not catch such cases.
 */
pt_map loop_to_points_to(loop l, pt_map pt_in)
{
  pt_map pt_out = pt_in;
  statement b = loop_body(l);
  //bool store = false;
  //pt_out = points_to_loop(l, pt_in, store);

  /* loop range expressions may require some points-to information 
   * See for instance Pointers/Mensi.sub/array_init02.c
   *
   * Side effects might have to be taken into account... But side
   * effects should also prevent PIPS from transforming a for loop
   * into a do loop.
   */
  range r = loop_range(l);
  expression init = range_lower(r);
  expression bound = range_upper(r);
  expression inc = range_increment(r);
  pt_in = expression_to_points_to(init, pt_in, false);
  pt_in = expression_to_points_to(bound, pt_in, false);
  pt_in = expression_to_points_to(inc, pt_in, false);

  pt_out = any_loop_to_points_to(b,
				 expression_undefined,
				 expression_undefined,
				 expression_undefined,
				 pt_in);

  return pt_out;
}

pt_map whileloop_to_points_to(whileloop wl, pt_map pt_in)
{
  pt_map pt_out = pt_in;
  statement b = whileloop_body(wl);
  expression c = whileloop_condition(wl);
    
  //bool store = false;
  if (evaluation_before_p(whileloop_evaluation(wl))) {
    //pt_out = points_to_whileloop(wl, pt_in, store);
    //pt_out = expression_to_points_to(c, pt_out, false);
    pt_out = expression_to_points_to(c, pt_out, true);
    pt_out = any_loop_to_points_to(b,
				   expression_undefined,
				   c,
				   expression_undefined,
				   pt_in);
  }
  else {
    // pt_out = points_to_do_whileloop(wl, pt_in, store);
    /* Execute the first iteration */
    pt_out = statement_to_points_to(b, pt_out);
    pt_out = any_loop_to_points_to(b,
				   expression_undefined,
				   c,
				   expression_undefined,
				   pt_out);
  }

  //statement ws = whileloop_body(wl);
  //list dl = statement_declarations(ws);
  // FI: to be improved
  //if(declaration_statement_p(ws) && !ENDP(dl))
  //  pt_out = points_to_set_block_projection(pt_out, dl);

      pips_assert("", consistent_points_to_graph_p(pt_out));

  return pt_out;
}

/* Perform the same k-limiting scheme for all kinds of loops 
 *
 * The do while loop must use an external special treatment for the
 * first iteration.
 *
 * Derived from points_to_forloop() and from Amira's work.
 *
 * pt_in is modified by side effects.
 */
//pt_map old_any_loop_to_points_to(statement b,
pt_map any_loop_to_points_to(statement b,
			     expression init, // can be undefined
			     expression c, // can be undefined
			     expression inc, // ca be undefined
			     pt_map pt_in)
{
  pt_map pt_out = pt_in;

  if(points_to_graph_bottom(pt_in)) {
    (void) statement_to_points_to(b, pt_in);
  }
  else {
    int i = 0;
    // FI: k is linked to the cycles in points-to graph, and should not
    // be linked to the number of convergence iterations. I assume here
    // that the minimal number of iterations is greater than the
    // k-limiting factor
    int k = get_int_property("POINTS_TO_PATH_LIMIT")
      + get_int_property("POINTS_TO_SUBSCRIPT_LIMIT")
      + get_int_property("POINTS_TO_OUT_DEGREE_LIMIT")
      +10; // Safety margin: might be set to max of both properties + 1 or 2...

    /* First, enter or skip the loop: initialization + condition check */
    if(!expression_undefined_p(init))
      pt_out = expression_to_points_to(init, pt_out, true);
    pt_map pt_out_skip = full_copy_pt_map(pt_out);
    if(!expression_undefined_p(c)) {
      pt_out = expression_to_points_to(c, pt_out, true);
      pt_out = condition_to_points_to(c, pt_out, true);
      pt_out_skip = condition_to_points_to(c, pt_out_skip, false);
    }

    /* Comput pt_out as loop invariant: pt_out holds at the beginning of
     * the loop body.
     *
     * pt_out(i) = f(pt_out(i-1)) U pt_out(i-1)
     *
     * prev = pt_out(i-1)
     *
     * Note: the pt_out variable is also used to carry the loop exit
     * points-to set.
     */
    pt_map prev = new_pt_map();
    // FI: it should be a while loop to reach convergence
    // FI: I keep it a for loop for safety
    bool fix_point_p = false;
    for(i = 0; i<k+2 ; i++) {
      /* prev receives the current points-to information, pt_out */
      clear_pt_map(prev);
      prev = assign_pt_map(prev, pt_out);
      clear_pt_map(pt_out);

      /* Depending on the kind of loops, execute the body and then
	 possibly the incrementation and the condition */
      // FI: here, storage_p would be useful to avoid unnecessary
      // storage and update for each substatement at each iteration k
      pt_out = statement_to_points_to(b, prev);
      if(!expression_undefined_p(inc))
	pt_out = expression_to_points_to(inc, pt_out, true);
      // FI: should be condition_to_points_to() for conditions such as
      // while(p!=q);
      // The condition is not always defined (do loops)
      if(!expression_undefined_p(c)) {
	pt_out = condition_to_points_to(c, pt_out, true);
	upgrade_approximations_in_points_to_set(pt_out);
      }

      /* Merge the previous resut and the current result. */
      // FI: move to pt_map
      pt_out = merge_points_to_graphs(prev, pt_out);

      pt_out = normalize_points_to_graph(pt_out);
      pt_out = remove_unreachable_stub_vertices_in_points_to_graph(pt_out);

      // pips_assert("", consistent_points_to_graph_p(pt_out));

      /* Check convergence */
      if(set_equal_p(points_to_graph_set(prev), points_to_graph_set(pt_out))) {
	fix_point_p = true;
	/* Add the last iteration to obtain the pt_out holding when
	   exiting the loop */
	pt_out = statement_to_points_to(b, prev);

      pips_assert("", consistent_points_to_graph_p(pt_out));
	if(!expression_undefined_p(inc))
	  pt_out = expression_to_points_to(inc, pt_out, true);

      pips_assert("", consistent_points_to_graph_p(pt_out));
	if(!expression_undefined_p(c))
	  pt_out = condition_to_points_to(c, pt_out, false);

      pips_assert("", consistent_points_to_graph_p(pt_out));
	break;
      }
      else {
	ifdebug(1) {
	  pips_debug(1, "\n\nAt iteration i=%d:\n\n", i);
	  print_points_to_set("Loop points-to set prev:\n",
			      points_to_graph_set(prev));
	  print_points_to_set("Loop points-to set pt_out:\n",
			      points_to_graph_set(pt_out));
	}
      }
    }

    if(!fix_point_p) {
      print_points_to_set("Loop points-to set prev:\n", points_to_graph_set(prev));
      print_points_to_set("Loop points-to set pt_out:\n", points_to_graph_set(pt_out));
      pips_internal_error("Loop convergence not reached in %d iterations.\n", i);
    }

    /* FI: I suppose that p[i] is replaced by p[*] and that MAY/MUST
       information is changed accordingly. */
    points_to_graph_set(pt_out) = points_to_independent_store(points_to_graph_set(pt_out));

    // pips_assert("", consistent_points_to_graph_p(pt_out));

    pt_out = merge_points_to_graphs(pt_out, pt_out_skip);
  }

  // pips_assert("", consistent_points_to_graph_p(pt_out));

  return pt_out;
}

/* Perform the same k-limiting scheme for all kinds of loops 
 *
 * The do while loop must use an external special treatment for the
 * first iteration.
 *
 * Derived from the initial any_loop_to_points_to(): the iteration
 * scheme is slighlty different but we end up with the same final
 * iteration with all unioned states. Seems problematic at least in
 * the presence of calls to free() because iter() is never normalized
 * and always introduces new vertices and arcs in "pt_out". See
 * list05.c.
 *
 * pt_in is modified by side effects.
 */
pt_map new_any_loop_to_points_to(statement b,
			     expression init, // can be undefined
			     expression c, // can be undefined
			     expression inc, // ca be undefined
			     pt_map pt_in)
{
  // return old_any_loop_to_points_to(b, init, c, inc, pt_in);
  pt_map pt_out = pt_in;

  if(points_to_graph_bottom(pt_in)) {
    (void) statement_to_points_to(b, pt_in);
  }
  else {
    int i = 0;
    // FI: k is linked to the cycles in points-to graph, and should not
    // be linked to the number of convergence iterations. I assume here
    // that the minimal number of iterations is greater than the
    // k-limiting factor
    int k = get_int_property("POINTS_TO_PATH_LIMIT")
      + get_int_property("POINTS_TO_SUBSCRIPT_LIMIT")
      + get_int_property("POINTS_TO_OUT_DEGREE_LIMIT")
      +10; // Safety margin: might be set to max of both properties + 1 or 2...

    /* First, enter or skip the loop: initialization + condition check */
    if(!expression_undefined_p(init))
      pt_out = expression_to_points_to(init, pt_out, true);
    pt_map pt_out_skip = full_copy_pt_map(pt_out);
    if(!expression_undefined_p(c)) {
      pt_out = condition_to_points_to(c, pt_out, true);
      pt_out_skip = condition_to_points_to(c, pt_out_skip, false);
    }

    /* Compute pt_out as loop invariant: pt_out holds at the beginning of
     * the loop body.
     *
     * pt_out(i) = pt_out(i-1) U pt_iter(i)
     *
     * pt_iter(i) = f(pt_iter(i-1))
     *
     * pt_prev == pt_iter(i-1), pt_out_prev == pt_out(i-1)
     *
     * Note: the pt_out variable is also used to carry the loop exit
     * points-to set.
     */
    pt_map pt_out_prev = new_pt_map();
    pt_map prev = new_pt_map();
    pt_map pt_iter = new_pt_map();
    pt_iter = assign_pt_map(pt_iter, pt_out);

    // FI: it should be a while loop to reach convergence
    // FI: I keep it a for loop for safety
    bool fix_point_p = false;
    for(i = 0; i<k+2 ; i++) {
      /* prev receives the current points-to information, pt_iter */
      clear_pt_map(prev);
      prev = assign_pt_map(prev, pt_iter);
      clear_pt_map(pt_iter);

      /* Depending on the kind of loop, execute the body and then
	 possibly the incrementation and the condition */
      // FI: here, storage_p would be useful to avoid unnecessary
      // storage and update for each substatement at each iteration k
      pt_iter = statement_to_points_to(b, prev);
      if(!expression_undefined_p(inc))
	pt_iter = expression_to_points_to(inc, pt_iter, true);
      // FI: should be condition_to_points_to() for conditions such as
      // while(p!=q);
      // The condition is not always defined (do loops)
      if(!expression_undefined_p(c))
	pt_iter = condition_to_points_to(c, pt_iter, true);

      /* Merge the previous resut and the current result. */
      // FI: move to pt_map
      pt_out_prev = assign_pt_map(pt_out_prev, pt_out);
      pt_out = merge_points_to_graphs(pt_out, pt_iter);

      pt_out = normalize_points_to_graph(pt_out);

      /* Check convergence */
      if(set_equal_p(points_to_graph_set(pt_out_prev),
		     points_to_graph_set(pt_out))) {
	fix_point_p = true;
	/* Add the last iteration to obtain the pt_out holding when
	   exiting the loop */
	pt_out = statement_to_points_to(b, pt_out_prev);
	if(!expression_undefined_p(inc))
	  pt_out = expression_to_points_to(inc, pt_out, true);
	if(!expression_undefined_p(c))
	  pt_out = condition_to_points_to(c, pt_out, false);
	break;
      }
      else {
	//ifdebug(1) {
	if(true) {
	  pips_debug(1, "\n\nAt iteration i=%d:\n\n", i);
	  print_points_to_set("Loop points-to set pt_out_prev:\n",
			      points_to_graph_set(pt_out_prev));
	  print_points_to_set("Loop points-to set pt_out:\n",
			      points_to_graph_set(pt_out));
	}
      }
    }

    if(!fix_point_p) {
      print_points_to_set("Loop points-to set pt_out:\n", points_to_graph_set(pt_out));
      print_points_to_set("Loop points-to set pt_out_prev:\n", points_to_graph_set(pt_out_prev));
      pips_internal_error("Loop convergence not reached after %d iterations.\n", k+2);
    }

    /* FI: I suppose that p[i] is replaced by p[*] and that MAY/MUST
       information is changed accordingly. */
    points_to_graph_set(pt_out) =
      points_to_independent_store(points_to_graph_set(pt_out));

    pt_out = merge_points_to_graphs(pt_out, pt_out_skip);
  }

  return pt_out;
}

pt_map k_limit_points_to(pt_map pt_out, int k)
{
  //bool type_sensitive_p = !get_bool_property("ALIASING_ACROSS_TYPES");
  //entity anywhere = entity_undefined;
  set pt_out_s = points_to_graph_set(pt_out);

  SET_FOREACH(points_to, pt, pt_out_s){
    cell sc = points_to_source(pt);
    reference sr = cell_any_reference(sc);
    list sl = reference_indices(sr);

    cell kc = points_to_sink(pt);
    reference kr = cell_any_reference(kc);
    list kl = reference_indices(kr);

    if((int)gen_length(sl)>k){
      bool to_be_freed = false;
      type sc_type = cell_to_type(sc, &to_be_freed);
      sc = make_anywhere_cell(sc_type);
      if(to_be_freed) free_type(sc_type);
    }

    if((int)gen_length(kl)>k){
      bool to_be_freed = false;
      type kc_type = cell_to_type(kc, &to_be_freed);
      kc = make_anywhere_cell(kc_type);
      if(to_be_freed) free_type(kc_type);
    }

    points_to npt = make_points_to(sc, kc,
				   copy_approximation(points_to_approximation(pt)),
				   make_descriptor_none());
    if(!points_to_equal_p(npt,pt)){
      // FC: why assigning pt_out to itself?
      pt_out = remove_arc_from_pt_map_(pt, pt_out);
      pt_out = remove_arc_from_pt_map_(npt, pt_out);
    }
    else {
      // FI: memory leak
      // free_points_to(npt);
    }
  }
  return pt_out;
}


pt_map unstructured_to_points_to(unstructured u, pt_map pt_in)
{
  pt_map pt_out = pt_in;

  pt_out = new_points_to_unstructured(u, pt_in, true);

  return pt_out;
}

pt_map multitest_to_points_to(multitest mt, pt_map pt_in)
{
  pt_map pt_out = pt_in;
  pips_internal_error("Not implemented yet for multitest %p\n", mt);
  return pt_out;
}

pt_map forloop_to_points_to(forloop fl, pt_map pt_in)
{
  pt_map pt_out = pt_in;
  statement b = forloop_body(fl);
  expression init = forloop_initialization(fl);
  expression c = forloop_condition(fl);
  expression inc = forloop_increment(fl);

  pt_out = any_loop_to_points_to(b, init, c, inc, pt_in);
  return pt_out;
}
