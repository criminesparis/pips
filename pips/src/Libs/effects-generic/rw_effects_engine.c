/*

  $Id: rw_effects_engine.c 23495 2018-10-24 09:19:47Z coelho $

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
/* package generic effects :  Be'atrice Creusillet 5/97
 *
 * File: rw_effects_engine.c
 * ~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * This File contains the generic functions necessary for the computation of
 * all types of read and write effects and cumulated references.
 */
#include <stdio.h>
#include <string.h>

#include "genC.h"

#include "linear.h"

#include "misc.h"

#include "text.h"
#include "ri.h"
#include "effects.h"

#include "ri-util.h"
#include "prettyprint.h"
#include "effects-util.h"
#include "text-util.h"

#include "properties.h"

#include "pipsdbm.h"

#include "effects-generic.h"

#include "pointer_values.h"

/************************************************ TO CONTRACT PROPER EFFECTS */

static bool contract_p = true;

void set_contracted_rw_effects(bool b)
{
    contract_p = b;
}


/*********************************************** INTERPROCEDURAL COMPUTATION */

bool summary_rw_effects_engine(const char* module_name)
{
  list l_glob = NIL, l_loc = NIL,l_loc2 = NIL, l_dec=NIL;
  statement module_stat;

  set_current_module_entity(module_name_to_entity(module_name));
  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, module_name, true) );
  module_stat = get_current_module_statement();
  make_effects_private_current_context_stack();
  make_statement_global_stack(); // for calls to semantics libray

  // functions that can be pointed by effects_computation_init_func:
  // effects_computation_no_init
  // init_convex_in_out_regions
  // init_convex_rw_regions
  (*effects_computation_init_func)(module_name);

  debug_on("SUMMARY_EFFECTS_DEBUG_LEVEL");

  set_rw_effects((*db_get_rw_effects_func)(module_name));

  if(empty_statement_p(module_stat)) {
    if(get_bool_property("MAXIMAL_EFFECTS_FOR_UNKNOWN_FUNCTIONS")) {
      l_loc = make_anywhere_read_write_memory_effects();
    }
    else if(get_bool_property("MAXIMAL_PARAMETER_EFFECTS_FOR_UNKNOWN_FUNCTIONS")) {
      // Generate all possible paths from the parameters
      // with read and write actions
      // I guess this does not work with varargs...
      // This may not be sufficient when there are pointers
      // In this case, we should use points_to
      // dummy targets to generate effects from them
      // but only for paths from formal arguments with pointer basic
      // BC.
      //entity m = get_current_module_entity();
      //type m_utype = ultimate_type(entity_type(m));
      list l_formals = module_formal_parameters(get_current_module_entity());
      // Types of formal parameters, not the formal parameters themselves
      //list l_formals = functional_parameters(type_functional(m_utype));

      FOREACH(ENTITY, formal, l_formals)
      {
        type formal_t = entity_basic_concrete_type(formal);
        list l_tmp = NIL;

        if (!ENDP(variable_dimensions(type_variable(formal_t))))
        {
          // functions that can be pointed by reference_to_effect_func:
          // reference_to_simple_effect
          // reference_to_convex_region
          // reference_to_reference_effect
          effect eff = (*reference_to_effect_func)
            (make_reference(formal,NIL), make_action_write_memory(), true);
          l_tmp =  generic_effect_generate_all_accessible_paths_effects
            (eff, formal_t, 'x');
          // free the dummy effect
          // functions that can be pointed by effect_free_func:
          // free_effect
          // region_free
          (*effect_free_func)(eff);
        }
        l_loc = gen_nconc(l_tmp, l_loc);
      }
    }
  }

  // l_loc may still be equal to NIL even if module_stat is an empty statement
  // and if the previously tested properties are true, because
  // the module may have no formal argument at all. BC.
  if(ENDP(l_loc) && !empty_statement_p(module_stat)) {
    l_loc = load_rw_effects_list(module_stat);
    ifdebug(2){
      pips_debug(2, "local regions, before translation to global scope:\n");
      (*effects_prettyprint_func)(l_loc);
    }
  }

  l_dec = summary_effects_from_declaration(module_name);
  ifdebug(8) {
    int nb_param;
    pips_debug(8, "Summary effects from declarations:\n");
    (*effects_prettyprint_func)(l_dec);
    nb_param = gen_length(functional_parameters(type_functional(ultimate_type(entity_type(get_current_module_entity())))));
    pips_debug(8, "number of declared formal parameters:%d\n", nb_param);

  }

  l_loc2 = gen_append(l_loc,l_dec);

  // MAP(EFFECT, e, fprintf(stderr, "=%s=", entity_name(reference_variable(effect_any_reference(e)))) ,l_loc2);
  // functions that can be pointed by effects_local_to_global_translation_op:
  // effects_dynamic_elim
  // regions_dynamic_elim
  l_glob = (*effects_local_to_global_translation_op)(l_loc2);

  ifdebug(4)
  {
    /* Check that summary effects are not corrupted */
    if(!check_sdfi_effects_p(get_current_module_entity(), l_glob))
      pips_internal_error("SDFI effects for \"%s\" are corrupted ",
          entity_name(get_current_module_entity()));
  }

  /* Different effects may have been reduced to the same one */
  /* FI: I'm not to sure the parameter true is generic */
  l_glob = proper_effects_combine(l_glob, true);

  ifdebug(2){
    pips_debug(2, "local regions, after translation to global scope:\n");
    (*effects_prettyprint_func)(l_loc2);
    pips_debug(2, "global regions, after translation to global scope:\n");
    (*effects_prettyprint_func)(l_glob);
  }

  ifdebug(4)
  {
    /* Check that summary effects are not corrupted */
    if(!check_sdfi_effects_p(get_current_module_entity(), l_glob))
      pips_internal_error("SDFI effects for \"%s\" are corrupted",
          entity_name(get_current_module_entity()));
  }

  (*db_put_summary_rw_effects_func)(module_name, l_glob);

  free_effects_private_current_context_stack();
  free_statement_global_stack(); // for calls to semantics libray

  reset_current_module_entity();
  reset_current_module_statement();
  reset_rw_effects();

  debug_off();
  // functions that can be pointed by effects_computation_reset_func:
  // effects_computation_no_reset
  // reset_convex_in_out_regions
  // reset_convex_rw_regions
  (*effects_computation_reset_func)(module_name);

  return(true);
}

/*********************************************** INTRAPROCEDURAL COMPUTATION */

static void rw_effects_of_unstructured(unstructured unst)
{
  statement current_stat = effects_private_current_stmt_head();
  list blocs = NIL ;
  list le = NIL ;
  control ct;

  pips_debug(2, "begin\n");

  ct = unstructured_control(unst);

  if(control_predecessors(ct) == NIL && control_successors(ct) == NIL)
  {
    /* there is only one statement in u; no need for a fixed point */
    pips_debug(3, "unique node\n");
    le = effects_dup(load_rw_effects_list(control_statement(ct)));
  }
  else
  {
    transformer t_unst = (*load_transformer_func)(current_stat);
    list l_node;

    CONTROL_MAP(c,
        {
            l_node = effects_dup(load_rw_effects_list(control_statement(c)));
            // functions that can be pointed by effects_test_union_op:
            // EffectsMayUnion
            // RegionsMayUnion
            // ReferenceTestUnion
            le = (*effects_test_union_op) (l_node, le, effects_same_action_p) ;
        },
        ct, blocs) ;
    // functions that can be pointed by effects_transformer_composition_op:
    // effects_composition_with_transformer_nop
    // effects_undefined_composition_with_transformer
    // convex_regions_transformer_compose
    // simple_effects_composition_with_effect_transformer
    le = (*effects_transformer_composition_op)(le, t_unst);
    effects_to_may_effects(le);
    gen_free_list(blocs) ;
  }

  // functions that can be pointed by effects_descriptor_normalize_func:
  // simple_effects_descriptor_normalize
  // convex_effects_descriptor_normalize
  (*effects_descriptor_normalize_func)(le);

  ifdebug(2){
    pips_debug(2, "R/W effects: \n");
    (*effects_prettyprint_func)(le);
  }
  store_rw_effects_list(current_stat, le);

  pips_debug(2, "end\n");
}

/*
 * From BC's PhD:
 *
 *   R[while(C)S] = R[C] U ( R[S] o E[C] ) U ( R[while(C)S] o T[S] o E[C] )
 *
 * However we do not have the lpf available to solve the recursive equation...
 * Ok, let's try something else, with a few transformations:
 *
 *   R[while(C)S]  = Rc[while(C)S] u Rs[while(C)S] ;
 *
 *   Rc[while(C)S] = R[C] u R[C] o T[S] o E[C] u ...
 *                 = U_i=0^inf R[C] o (T[S] o E[C])^i
 *                 = R[C] O U_i=0^inf (T[S] o E[C])^i
 *                 = R[C] O T*[while(C)S] ;
 *
 *   Rs[while(C)S] = R[S] o E[C] u R[S] o E[C] o T[S] o E[C] u ...
 *                 = U_i=0^inf R[S] o E[C] o (T[S] o E[C])^i
 *                 = R[S] o E[C] O U_i=0^inf (T[S] o E[C])^i
 *                 = R[S] o E[C] O T*[while(C)S] ;
 *
 * Thus
 *
 *   R[while(C)S]  = (R[C] u R[S] o E[C]) O T*[while(C)S] ;
 *
 *
 * I assume that someone (FI) is to provide:
 *
 *   T*[while(C)S] = U_i=0^inf (T[S] o E[C])^i ;
 *
 * Note that T* can be computed as a fixpoint from the recursice equation:
 *
 *   T*[while(C)S] = T*[while(C)S] o T[S] o E[C] u Id
 *
 * That is the resolution of the fixpoint for R is expressed as a fixpoint
 * on transformers only, and a direct computation on R.
 *
 * Also we know that the output state is the one which makes C false.
 *
 *   T[while(C)S] = E[.not.C] O T*[while(C)S] ;
 *
 * note that T[] Sigma -> Sigma,
 * but T*[] Sigma -> P(Sigma)
 * that is it describes exactly intermediate stores reached by the while.
 *
 * FC, 04/06/1998
 */
static void rw_effects_of_while(whileloop w)
{
  statement current_stat = effects_private_current_stmt_head();
  list l_prop, l_body, l_cond_first, l_res;
  statement b = whileloop_body(w);
  transformer trans;

  /* we should check if the loop is executed at least once :
   * we could keep exact effects on scalars at least.
   */

  l_prop = effects_dup(load_proper_rw_effects_list(current_stat)); /* R[C] */
  if (contract_p)
    l_prop = proper_to_summary_effects(l_prop);

  /* The condition is executed at least once : let's keep exact effects if we can */
  l_cond_first = effects_dup(l_prop);

  l_body = effects_dup(load_rw_effects_list(b)); /* R[S] */
  /* I use the famous over-approximation of E[C]: Id */
  trans = (*load_transformer_func)(current_stat); /* T*[while(C)S] */

  // functions that can be pointed by effects_union_op:
  // ProperEffectsMustUnion
  // RegionsMustUnion
  // ReferenceUnion
  // EffectsMustUnion
  l_body = (*effects_union_op)(l_body, l_prop, effects_same_action_p);
  // functions that can be pointed by effects_transformer_composition_op:
  // effects_composition_with_transformer_nop
  // effects_undefined_composition_with_transformer
  // convex_regions_transformer_compose
  // simple_effects_composition_with_effect_transformer
  l_body = (*effects_transformer_composition_op)(l_body, trans);

  /* We don't know whether the loop is executed at least once or not. */
  effects_to_may_effects(l_body);

  /* We add the effects of the first condition evaluation */
  // functions that can be pointed by effects_union_op:
  // ProperEffectsMustUnion
  // RegionsMustUnion
  // ReferenceUnion
  // EffectsMustUnion
  l_res = (*effects_union_op)(l_cond_first, l_body, effects_same_action_p);

  // functions that can be pointed by effects_descriptor_normalize_func:
  // simple_effects_descriptor_normalize
  // convex_effects_descriptor_normalize
  (*effects_descriptor_normalize_func)(l_res);

  store_rw_effects_list(current_stat, l_res);
}

static void rw_effects_of_forloop(forloop w)
{
  statement current_stat = effects_private_current_stmt_head();
  statement b = forloop_body(w);
  transformer trans;

  list l_body = NIL, l_res = NIL, li = NIL, lc = NIL, linc = NIL, l_init = NIL, l_cond_inc = NIL;

  /* we should check if the loop is executed at least once :
   * we could keep exact effects on scalars at least.
   */

  /* proper_effects first : we must recompute them
   * there are must effects for the intialization and the first evaluation
   * of the condition.
   * the next evaluations of the condition and the incrementation must be
   * composed by the transformer.
   */

  /* effects of initialization */
  li = generic_proper_effects_of_expression(forloop_initialization(w));

  /* effects of condition expression */
  lc = generic_proper_effects_of_expression(forloop_condition(w));

  /* effects of incrementation expression  */
  linc = generic_proper_effects_of_expression(forloop_increment(w));
  if (contract_p)
  {
    li = proper_to_summary_effects(li);
    lc = proper_to_summary_effects(lc);
    linc = proper_to_summary_effects(linc);
  }
  l_init = gen_nconc(li, lc);
  // functions that can be pointed by effects_union_op:
  // ProperEffectsMustUnion
  // RegionsMustUnion
  // ReferenceUnion
  // EffectsMustUnion
  l_cond_inc = (*effects_union_op)(effects_dup(lc), linc, effects_same_action_p);

  if (get_constant_paths_p())
  {
    list l_tmp = l_init;
    l_init = pointer_effects_to_constant_path_effects(l_init);
    effects_free(l_tmp);
    l_tmp = l_cond_inc;
    l_cond_inc = pointer_effects_to_constant_path_effects(l_cond_inc);
    effects_free(l_tmp);
  }

  l_body = effects_dup(load_rw_effects_list(b)); /* R[S] */
  /* I use the famous over-approximation of E[C]: Id */
  trans = (*load_transformer_func)(current_stat); /* T*[while(C)S] */

  // functions that can be pointed by effects_union_op:
  // ProperEffectsMustUnion
  // RegionsMustUnion
  // ReferenceUnion
  // EffectsMustUnion
  l_body = (*effects_union_op)(l_body, l_cond_inc, effects_same_action_p);
  // functions that can be pointed by effects_transformer_composition_op:
  // effects_composition_with_transformer_nop
  // effects_undefined_composition_with_transformer
  // convex_regions_transformer_compose
  // simple_effects_composition_with_effect_transformer
  l_res = (*effects_transformer_composition_op)(l_body, trans);

  /* We don't know whether the loop is executed at least once or not. */
  effects_to_may_effects(l_res);

  /* We finally add the effects of the initialization phase */
  // functions that can be pointed by effects_union_op:
  // ProperEffectsMustUnion
  // RegionsMustUnion
  // ReferenceUnion
  // EffectsMustUnion
  l_res = (*effects_union_op)(l_init, l_res, effects_same_action_p);

  // functions that can be pointed by effects_descriptor_normalize_func:
  // simple_effects_descriptor_normalize
  // convex_effects_descriptor_normalize
  (*effects_descriptor_normalize_func)(l_res);

  store_rw_effects_list(current_stat, l_res);
}

static void rw_effects_of_loop(loop l)
{
  statement current_stat = effects_private_current_stmt_head();
  list l_prop, l_body, l_loop = NIL;
  statement b = loop_body(l);
  entity i = loop_index(l);
  range r = loop_range(l);
  transformer loop_trans;

  pips_debug(2, "begin\n");

  /* proper effects of loop */
  l_prop = effects_dup(load_proper_rw_effects_list(current_stat));
  if (contract_p)
    l_prop = proper_to_summary_effects(l_prop);

  /* rw effects of loop body */
  l_body = load_rw_effects_list(b);

  ifdebug(4){
    pips_debug(4, "rw effects of loop body:\n");
    (*effects_prettyprint_func)(l_body);
  }
  /* Loop body must not have a write effect on the loop index */
  FOREACH(EFFECT, ef, l_body) {
    if(effect_entity(ef)==i && action_write_p(effect_action(ef)))
      pips_user_error("Index %s of loop %s defined in loop body. "
          "Fortran 77 standard violation, see Section 11.10.5.\n",
          entity_local_name(i),
          label_local_name(loop_label(l)));
  }

  /* SG: effects on locals are masked if the loop is parallel */
  if(loop_parallel_p(l)) {
    list tmp = effects_dup_without_variables(l_body, loop_locals(l));
    l_body = effects_dup_without_variables(tmp, statement_declarations(b));
    gen_free_list(tmp);
  }
  else
    l_body = effects_dup(l_body);

  /* COMPUTATION OF INVARIANT RW EFFECTS */

  /* We get the loop transformer, which gives the loop invariant */
  /* We must remove the loop index from the list of modified variables */
  loop_trans = (*load_transformer_func)(current_stat);

  ifdebug(8)
  {
    pips_debug(8, "loop transformer : \n");
    // dump_transformer(loop_trans);
  }

  loop_trans = transformer_remove_variable_and_dup(loop_trans, i);

  ifdebug(8)
  {
    pips_debug(8, "loop transformer after removing loop index %s : \n",
        entity_name(i));
    // dump_transformer(loop_trans);
  }


  /* And we compute the invariant RW effects. */
  // functions that can be pointed by effects_transformer_composition_op:
  // effects_composition_with_transformer_nop
  // effects_undefined_composition_with_transformer
  // convex_regions_transformer_compose
  // simple_effects_composition_with_effect_transformer
  l_body = (*effects_transformer_composition_op)(l_body, loop_trans);
  update_invariant_rw_effects_list(b, effects_dup(l_body));

  ifdebug(4){
    pips_debug(4, "invariant rw effects of loop body:\n");
    (*effects_prettyprint_func)(l_body);
  }

  /* COMPUTATION OF RW EFFECTS OF LOOP FROM INVARIANT RW EFFECTS */
  if (!ENDP(l_body))
  {
    l_loop = l_body;
    /* We eliminate the loop index */
    // functions that can be pointed by effects_union_over_range_op:
    // effects_union_over_range_nop
    // simple_effects_union_over_range
    // convex_regions_union_over_range
    l_loop = (*effects_union_over_range_op)(l_loop, i, r,
        descriptor_undefined);
  }

  ifdebug(4){
    pips_debug(4, "rw effects of loop before adding proper effects:\n");
    (*effects_prettyprint_func)(l_loop);
  }

  /* We finally add the loop proper effects */
  // functions that can be pointed by effects_union_op:
  // ProperEffectsMustUnion
  // RegionsMustUnion
  // ReferenceUnion
  // EffectsMustUnion
  l_loop = (*effects_union_op)(l_loop, l_prop, effects_same_action_p);

  ifdebug(4){
    pips_debug(4, "rw effects of loop after adding proper effects:\n");
    (*effects_prettyprint_func)(l_loop);
  }
  // functions that can be pointed by effects_descriptor_normalize_func:
  // simple_effects_descriptor_normalize
  // convex_effects_descriptor_normalize
  (*effects_descriptor_normalize_func)(l_loop);

  ifdebug(2){
    pips_debug(2, "R/W effects: \n");
    (*effects_prettyprint_func)(l_loop);
  }
  store_rw_effects_list(current_stat, l_loop);
  pips_debug(2, "end\n");
}

static void rw_effects_of_call(call c)
{
  statement current_stat = effects_private_current_stmt_head();
  transformer context = (*load_context_func)(current_stat);
  list le = NIL;

  pips_debug(2, "begin call to %s\n", entity_name(call_function(c)));

  if (!(*empty_context_test)(context))
  {
    list sel = load_proper_rw_effects_list(current_stat);
    le = effects_dup(sel);
    ifdebug(2){
      pips_debug(2, "proper effects before summarization: \n");
      (*effects_prettyprint_func)(le);
    }
    if (contract_p)
      le = proper_to_summary_effects(le);
  }
  else
    pips_debug(2, "empty context\n");

  // functions that can be pointed by effects_descriptor_normalize_func:
  // simple_effects_descriptor_normalize
  // convex_effects_descriptor_normalize
  (*effects_descriptor_normalize_func)(le);

  ifdebug(2){
    pips_debug(2, "R/W effects: \n");
    (*effects_prettyprint_func)(le);
  }
  store_rw_effects_list(current_stat, le);

  pips_debug(2, "end\n");
}

/* For the time being, just a duplicate of rw_effects_of_call() */
static void rw_effects_of_application(application a __attribute__ ((__unused__)))
{
  statement current_stat = effects_private_current_stmt_head();
  transformer context = (*load_context_func)(current_stat);
  list le = NIL;

  pips_debug(2, "begin application\n");

  if (!(*empty_context_test)(context))
  {
    list sel = load_proper_rw_effects_list(current_stat);
    le = effects_dup(sel);
    ifdebug(2){
      pips_debug(2, "proper effects before summarization: \n");
      (*effects_prettyprint_func)(le);
    }
    if (contract_p)
      le = proper_to_summary_effects(le);
  }
  else
    pips_debug(2, "empty context\n");

  // functions that can be pointed by effects_descriptor_normalize_func:
  // simple_effects_descriptor_normalize
  // convex_effects_descriptor_normalize
  (*effects_descriptor_normalize_func)(le);

  ifdebug(2){
    pips_debug(2, "R/W effects: \n");
    (*effects_prettyprint_func)(le);
  }
  store_rw_effects_list(current_stat, le);

  pips_debug(2, "end\n");
}

/* Just to handle one kind of instruction, expressions which are not
   calls.  As we do not distinguish between Fortran and C, this
   function is called for Fortran module although it does not have any
   effect.
 */
static void rw_effects_of_expression_instruction(instruction i)
{
  //list l_proper = NIL;
  statement current_stat = effects_private_current_stmt_head();
  //instruction inst = statement_instruction(current_stat);

  /* Is the call an instruction, or a sub-expression? */
  if (instruction_expression_p(i)) {
    expression ie = instruction_expression(i);
    syntax is = expression_syntax(ie);
    call c = call_undefined;

    if(syntax_cast_p(is)) {
      expression ce = cast_expression(syntax_cast(is));
      syntax sc = expression_syntax(ce);

      if(syntax_call_p(sc)) {
	c = syntax_call(sc);
	rw_effects_of_call(c);
      }
      else if(syntax_reference_p(sc)) {
	/* FI: I guess you do not end up here if the cast appears in
	   the lhs, assuming this is till compatible with the
	   standard. */
	/* reference r = syntax_reference(sc); */
	// FI: Copied from below
	store_rw_effects_list(current_stat, NIL);
      }
      else {
	pips_internal_error("Cast case not implemented");
      }
    }
    else if(syntax_call_p(is)) {
      /* This may happen when a loop is desugared into an unstructured. */
      c = syntax_call(is);
      rw_effects_of_call(c);
    }
    else if(syntax_application_p(is)) {
      application a = syntax_application(is);
      //expression fe = application_function(a);

      pips_user_warning("Cumulated effects of call site using function "
			"pointers in data structures are ignored for the time being\n");
      rw_effects_of_application(a);
    }
    else if (syntax_reference_p(is)) {
      // someone typed "i;" in the code... it is allowed.
      // let us ignore this dead code for today
      // shoud generate a read effect on the reference?
      // can it be safely ignored?
      store_rw_effects_list(current_stat, NIL);
    }
    else {
      pips_internal_error("Instruction expression case not implemented");
    }

    pips_debug(2, "Effects for expression instruction in statement%03zd\n",
	       statement_ordering(current_stat));

  }
}

static void rw_effects_of_test(test t)
{
  statement current_stat = effects_private_current_stmt_head();
  list le, lt, lf, lc, lr;
  statement true_s = test_true(t);
  statement false_s = test_false(t);

  pips_debug(2, "begin\n");

  /* FI: when regions are computed the test condition should be
   * evaluated wrt the current precondition to see if it evaluates
   * to true or false. This would preserve must effects.
   *
   * dead_test_filter() could be used, but it returns an enum
   * defined in transformations-local.h
   */

  if (stmt_strongly_feasible_p_func &&
      !(*stmt_strongly_feasible_p_func)(true_s)) {
    /* the true branch is dead */
    le = effects_dup(load_rw_effects_list(false_s));
  }
  else if (stmt_strongly_feasible_p_func &&
           !(*stmt_strongly_feasible_p_func)(false_s)) {
    /* the false branch is dead */
    le = effects_dup(load_rw_effects_list(true_s));
  }
  else {
    /* effects of the true branch */
    lt = effects_dup(load_rw_effects_list(test_true(t)));
    /* effects of the false branch */
    lf = effects_dup(load_rw_effects_list(test_false(t)));
    /* effects of the combination of both 
     *
     * The region intersection in the corresponding equation, at the
     * bottom of page 297 in Beatrice Creusillet's PhD, is not used to
     * compute MUST regions.
     *
     * Also, the impact of the test condition is assumed taken into
     * account at a lower level, via the preconditions.
     */
    // functions that can be pointed by effects_test_union_op:
    // EffectsMayUnion
    // RegionsMayUnion
    // ReferenceTestUnion
    le = (*effects_test_union_op)(lt, lf, effects_same_action_p);
  }

  /* proper_effects of the condition */
  lc = effects_dup(load_proper_rw_effects_list(current_stat));
  if (contract_p)
    lc = proper_to_summary_effects(lc);
  /* effect of the test */
  // functions that can be pointed by effects_union_op:
  // ProperEffectsMustUnion
  // RegionsMustUnion
  // ReferenceUnion
  // EffectsMustUnion
  lr = (*effects_union_op)(le, lc, effects_same_action_p);

  // functions that can be pointed by effects_descriptor_normalize_func:
  // simple_effects_descriptor_normalize
  // convex_effects_descriptor_normalize
  (*effects_descriptor_normalize_func)(lr);

  ifdebug(2){
    pips_debug(2, "R/W effects: \n");
    (*effects_prettyprint_func)(lr);
  }

  store_rw_effects_list(current_stat, lr);
  pips_debug(2, "end\n");
}

static void save_useful_variables_effects(entity ent, list l_eff) {
  list l_save = NIL;
  effects eff = effects_undefined;

  FOREACH(EFFECT, ef, l_eff) {
    if (same_entity_p(ent, reference_variable(effect_any_reference(ef)))) {
      // copy_effect is need because of the save and free by pipsdbm
      l_save = CONS(EFFECT, copy_effect(ef), l_save);
    }
  }
  ifdebug(2) {
    pips_debug(2, "add useful_variables_effects/regions for entity %s :\n", entity_name(ent));
    (*effects_prettyprint_func)(l_save);
  }
  eff = make_effects(l_save);

  store_useful_variables_effects((entity) ent, (effects) eff);
}


/**
   computes the cumulated effects of the declaration from the list of
   effects that occur after the declaration

   @param[out] lrw_before_decl is the list of effects in the store before the declaration;
   it is a modified version of lrw_after_first_decl.
   @param[inout] lrw_after_first_decl is the list of effects in the store after the declaration;
       lrw_after_first_decl can be freed after this function.
   @param[in] decl is the declared variable

   possible usage: l = rw_effects_of_declaration(l, decl)

   This is used at least in rw_effects_of_sequence to compute the
   cumulated effect of a sequence. The statements are walked backward
   from the last one to the first one. Each time a declaration is hit,
   the declared variables are also analyzed backwards to project past
   effects that cannot be moved up because the variables is no longer
   in the environment.

   For reasons I (FI) still do not understand, the effect of
   initialization expressions are (re(re?)?) computed here. At least
   when this code is used for the computation of the cumulated
   effects, I'd rather use the statement effects, whether they are
   declarations or not and only filter them, igonring initialization
   expressions if any.

   This function has been outlined from
   rw_effects_of_declaration(). The names of the local variables
   should probably be updated according to its signature and
   semantics.
 */
static list rw_effects_of_declaration(list lrw_after_first_decl, entity decl)
{
  list lrw_before_decls = NIL; /* the returned list */
  storage decl_s = entity_storage(decl);

  ifdebug(8) {
    type ct = entity_basic_concrete_type(decl);
    pips_debug(8, "dealing with entity : %s with type %s\n",
        entity_local_name(decl), string_of_type(ct));
  }

  if (storage_ram_p(decl_s)
      /* static variable declaration has no effect, even in case of initialization. */
      && !static_area_p(ram_section(storage_ram(decl_s)))
      && type_variable_p(entity_type(decl)))
  {
    value v_init = entity_initial(decl);
    expression exp_init = expression_undefined;
    if(value_expression_p(v_init))
      exp_init = value_expression(v_init);

    // add the effects due to the initialization part
    if(/*false &&*/ !expression_undefined_p(exp_init))
    {
      pips_debug(8, "initial value: %s\n", expression_to_string(exp_init));
      list l_exp_init = generic_proper_effects_of_expression(exp_init);
      if (contract_p)
        l_exp_init = proper_to_summary_effects(l_exp_init);
      // functions that can be pointed by effects_union_op:
      // ProperEffectsMustUnion
      // RegionsMustUnion
      // ReferenceUnion
      // EffectsMustUnion
      lrw_after_first_decl = (*effects_union_op)(l_exp_init,
          lrw_after_first_decl, effects_same_action_p);
    }

    save_useful_variables_effects(decl, lrw_after_first_decl);

    // filter l_rw_after_decls with the declaration
    lrw_before_decls = filter_effects_with_declaration(lrw_after_first_decl, decl);

  } /* if (storage_ram(decl_s) && !static_area_p(ram_section(storage_ram(decl_s)))) */
  else
  {
    lrw_before_decls = lrw_after_first_decl;
  }
  return lrw_before_decls;
}

/**
   computes the cumulated effects of the declarations from the list of
   effects after the declaration and make sure that all effects are
   constant (FI: with respect to dereferencements I guess) to be sure
   that can be unioned properly.

   @param[out] lrw_after_decls is the list of effects in the store after the declarations;
   it is modified.
   @param[in] l_decl is the ordered list of declarations.

   usage: l = rw_effects_of_declarations(l, l_decl)
 */
static list rw_effects_of_declarations(list lrw_after_decls, list l_decl)
{
  list lrw_before_decls = NIL; /* the returned list */
  list lrw_after_first_decl = NIL; /* effects after first declaration */

  if (!ENDP(l_decl))
    {
      // treat last declarations first: n recursive calls instead of a
      // gen_reverse()...
      if (!ENDP(CDR(l_decl)))
	lrw_after_first_decl = rw_effects_of_declarations(lrw_after_decls, CDR(l_decl));
      else
	lrw_after_first_decl = lrw_after_decls;
      // then handle top declaration
      entity decl = ENTITY(CAR(l_decl));
      lrw_before_decls = rw_effects_of_declaration(lrw_after_first_decl, decl);

    } /* if (!ENDP(CDR(l_decl))) */
  else
     lrw_before_decls = lrw_after_decls;
      // we should also do some kind of unioning...

  if (get_constant_paths_p()) {
      list l_tmp = lrw_before_decls;
      lrw_before_decls = pointer_effects_to_constant_path_effects(lrw_before_decls);
      effects_free(l_tmp);
    }

  return lrw_before_decls;
}

/* Compute backwards the cumulated effects of the non-empty statement
 * list "sl" as it is necessary to translate convex effects into
 * the initial state.
 *
 * To do so, call recursively r_rw_effects_of_sequence() on the CDR of
 * "sl" and translate them in the current state thanks to "t1", the
 * transformer of the first statement, "s1", add the effects of the
 * first statement "s1" which are already available in that same
 * state, and remove effects related to variables declared in the
 * first statement, "s1".
 *
 * rw_effects(sl) = projection(rw_effects(CDR(sl)) o transformer(s1)
 *                                 U effects(s1),
 *                                 declarations(s1))
 * 
 * The implementation is slightly different from the equations above
 * if the first statement is a C declaration statement. The effect of
 * the first statement are neglected at first and the effects of the
 * initialization expressions are added later:
 *
 * rw_effects(sl) = if(declaration_p(s1)) then
 *                        projection(rw_effects(CDR(sl)) o transformer(s1),
 *                                   declarations(s1))
 *                        U effects(initializations(s1))
 *                      else
 *                        rw_effects(CDR(l_inst)) o transformer(s1)
 *                        U effects(s1)
 *
 * In both cases, a special process is used when "sl" is a singleton list:
 *
 * rw_effects(sl) = if(constant_p) then 
 *                    constant_effects(projection(effects(s1), declaration(s1)))
 *                  else
 *                    projection(effects(s1), declaration(s1))
 *
 * This equation is altered with the implemented scheme because
 * "effects(s1)" is not used when "s1" is a declaration.
 *
 * The precondition of "s1", called "context" is also used and should
 * appear in the equations above.
 *
 * Note that the recursion performed here is independent of the global
 * gen_multi_recurse(). The contexts have to be maintained explicitely.
 */
static list r_rw_effects_of_sequence(list sl)
{
  statement s1 = STATEMENT(CAR(sl));
  list remaining_block = CDR(sl);

  list s1_lrw; /* rw effects of first statement */
  list rb_lrw; /* rw effects of remaining block */
  list l_rw = NIL; /* resulting rw effects */
  list l_decl = NIL; /* declarations if first_statement is a declaration statement */

  /* Precondition of s1. Could be called p1... */
  // for effects, context=transformer_undefined
  transformer context = (*load_context_func)(s1);
  effects_private_current_context_push(context);
  /* This is used to retrieve the points-to information */
  effects_private_current_stmt_push(s1);
  /* To obtain precise warning and error messages */
  push_statement_on_statement_global_stack(s1);

  if (c_module_p(get_current_module_entity()) &&
      (declaration_statement_p(s1) )) {
    // if it's a declaration statement, effects will be added on the fly
    // as declarations are handled.
    pips_debug(5, "first statement is a declaration statement\n");
    l_decl = statement_declarations(s1);
    s1_lrw = NIL;
    //s1_lrw = load_rw_effects_list(s1);
  }
  else
    s1_lrw = load_rw_effects_list(s1);

  /* Is it the last instruction of the block? */
  if (!ENDP(remaining_block)) {
    rb_lrw = r_rw_effects_of_sequence(remaining_block);

    ifdebug(3) {
      pips_debug(3, "R/W effects of first statement: \n");
      (*effects_prettyprint_func)(s1_lrw);
      pips_debug(3, "R/W effects of remaining sequence: \n");
      (*effects_prettyprint_func)(rb_lrw);
      /*
      transformer t1 = (*load_transformer_func)(s1);
      if (!transformer_undefined_p(t1)) {
        pips_debug(3, "transformer of first statement:\n");
        fprint_transformer(stderr, t1, (get_variable_name_t) entity_local_name);
        //print_transformer(t1);
      }
      if (!transformer_undefined_p(context)) {
        pips_debug(3, "Precondition of first statement:\n");
        fprint_transformer(stderr, context, (get_variable_name_t) entity_local_name);
        //print_transformer(t1);
      }
      */
    }
    if (rb_lrw !=NIL) {
      /* FI: I do not understand this update; do we store each
       *     partial accumulation of effects at each statement? */
      /* NL: It's not an update of the resource but of the store effects */
      rb_lrw = generic_effects_store_update(rb_lrw, s1, true);
    }
    else {
      ifdebug(3){
        pips_debug(3, "Warning - no effect on remaining block\n");
      }
    }
    ifdebug(5){
      pips_debug(5, "R/W effects of remaining sequence "
          "after store update: \n");
      (*effects_prettyprint_func)(rb_lrw);
    }

    /* then take care of declarations if any: project effects
     * based on declared variables and add effects of
     * initialization expressions and translate non constant
     * effects into constant effects if necessary. */
    effects_private_current_stmt_push(s1);
    rb_lrw = rw_effects_of_declarations(rb_lrw, l_decl);
    effects_private_current_stmt_pop();

    ifdebug(5){
      pips_debug(5, "R/W effects of remaining sequence "
          "after taking declarations into account: \n");
      (*effects_prettyprint_func)(rb_lrw);
    }

    /* RW(block) = RW(rest_of_block) U RW(s1) */
    // functions that can be pointed by effects_union_op:
    // ProperEffectsMustUnion
    // RegionsMustUnion
    // ReferenceUnion
    // EffectsMustUnion
    l_rw = (*effects_union_op)(rb_lrw, effects_dup(s1_lrw), effects_same_action_p);

    ifdebug(5){
      pips_debug(5, "R/W effects of remaining sequence "
          "after union: \n");
      (*effects_prettyprint_func)(l_rw);
    }
  }
  else {
    /* We are on the last statement of the block and end the recursion */
    /* If l_decl is not empty, then s1_lrw is empty, and
     * vice-versa. See prologue. */
    l_rw = rw_effects_of_declarations(effects_dup(s1_lrw), l_decl);
    /* This should be useless because cumulated effects are applied
     * to constant proper effects most of the time... Maybe it is
     * useful for cumulated pointer effects? */
    if (get_constant_paths_p()) {
      list l_tmp = l_rw;
      l_rw = pointer_effects_to_constant_path_effects(l_rw);
      effects_free(l_tmp);
    }
  }

  effects_private_current_context_pop();
  effects_private_current_stmt_pop();
  pop_statement_global_stack();

  return(l_rw);
}

/* The real work is performed by r_rw_effects_of_sequence(), the
 * recursive backward walk of the sequence.
 *
 * Here, anywhere effects are dealt with, the effects are normalized
 * and store in the cumulate effects mapping.
 *
 * Empty sequences are also dealt with directly here.
 */
static void rw_effects_of_sequence(sequence seq)
{
  statement current_stat = effects_private_current_stmt_head();
  list le = NIL;
  list l_inst = sequence_statements(seq);

  pips_debug(2, "begin\n");

  if (ENDP(l_inst))
  {
    if (get_bool_property("WARN_ABOUT_EMPTY_SEQUENCES"))
      pips_user_warning("empty sequence\n");
  }
  else
  {
    list l_tmp = r_rw_effects_of_sequence(l_inst);
    le = clean_anywhere_effects(l_tmp);
    gen_full_free_list(l_tmp);
  }

  ifdebug(2){
    pips_debug(2, "R/W effects: \n");
    (*effects_prettyprint_func)(le);
  }

  // functions that can be pointed by effects_descriptor_normalize_func:
  // simple_effects_descriptor_normalize
  // convex_effects_descriptor_normalize
  (*effects_descriptor_normalize_func)(le);

  ifdebug(2){
    pips_debug(2, "R/W effects after normalization: \n");
    (*effects_prettyprint_func)(le);
  }

  store_rw_effects_list(current_stat, le);
  pips_debug(2, "end\n");
}

static bool rw_effects_stmt_filter(statement s)
{
  pips_debug(1, "Entering statement with ordering: %03zd and number: %03zd\n", statement_ordering(s), statement_number(s));
  ifdebug(4) {
    print_statement(s);
  }
  effects_private_current_stmt_push(s);
  effects_private_current_context_push((*load_context_func)(s));
  return(true);
}

static void rw_effects_of_statement(statement s)
{
    store_invariant_rw_effects_list(s, NIL);
    effects_private_current_stmt_pop();
    effects_private_current_context_pop();
    pips_debug(1, "End statement %03zd :\n", statement_ordering(s));
}

static bool r_effects_of_return_exit_abort_statment(statement s, list lem) {
  if (statement_call_p(s)) {
    if (return_statement_p(s)
        || exit_statement_p(s)
        || abort_statement_p(s)) {
      list le = load_rw_effects_list(s);
      FOREACH(EFFECT, e, lem) {
        if (io_effect_p(e)) {
          if (effect_read_p(e)) {
            le = gen_nconc(le, CONS(EFFECT, e, NIL));
          }
        }
      }
      update_rw_effects_list(s, le);
    }
    return false;
  }
  return true;
}


void rw_effects_of_module_statement(statement module_stat)
{
  make_effects_private_current_stmt_stack();
  make_effects_private_current_context_stack();
  make_statement_global_stack(); // for calls to semantics libray
  pips_debug(1,"begin\n");

  gen_multi_recurse(module_stat,
      statement_domain, rw_effects_stmt_filter, rw_effects_of_statement,
      sequence_domain, gen_true, rw_effects_of_sequence,
      test_domain, gen_true, rw_effects_of_test,
      call_domain, gen_true, rw_effects_of_call,
      loop_domain, gen_true, rw_effects_of_loop,
      whileloop_domain, gen_true, rw_effects_of_while,
      forloop_domain, gen_true, rw_effects_of_forloop,
      unstructured_domain, gen_true, rw_effects_of_unstructured,
      instruction_domain, gen_true, rw_effects_of_expression_instruction,
      expression_domain, gen_false, gen_null, /* NOT THESE CALLS */
      NULL);

  if (entity_main_module_p(get_current_module_entity())) {
    list le = load_rw_effects_list(module_stat);

    gen_context_recurse(module_stat, le,
        statement_domain, r_effects_of_return_exit_abort_statment, gen_null2);
  }

  pips_debug(1,"end\n");
  free_effects_private_current_stmt_stack();
  free_effects_private_current_context_stack();
  free_statement_global_stack(); // for calls to semantics library
}

bool rw_effects_engine(const char * module_name)
{
  /* Get the code of the module. */
  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, module_name, true));
  statement ms = get_current_module_statement();

  set_current_module_entity(module_name_to_entity(module_name));

  // functions that can be pointed by effects_computation_init_func:
  // effects_computation_no_init
  // init_convex_in_out_regions
  // init_convex_rw_regions
  (*effects_computation_init_func)(module_name);

  /* We also need the proper effects of the module */
  set_proper_rw_effects((*db_get_proper_rw_effects_func)(module_name));

  /* Compute the rw effects or references of the module. */
  init_rw_effects();
  init_invariant_rw_effects();
  init_useful_variables_effects();

  if (get_pointer_info_kind() == with_points_to)
    set_pt_to_list( (statement_points_to)
        db_get_memory_resource(DBR_POINTS_TO, module_name, true) );
  else if (get_pointer_info_kind() == with_pointer_values)
    set_pv( db_get_simple_pv(module_name));


  debug_on("EFFECTS_DEBUG_LEVEL");
  pips_debug(1, "begin\n");

  rw_effects_of_module_statement(ms);

  pips_debug(1, "end\n");
  debug_off();

  if (get_pointer_info_kind() == with_points_to)
    reset_pt_to_list();
  else if (get_pointer_info_kind() == with_pointer_values)
    reset_pv();

  (*db_put_rw_effects_func)
        (module_name, get_rw_effects());
  (*db_put_invariant_rw_effects_func)
        (module_name, get_invariant_rw_effects());
  (*db_put_useful_variables_effects_func)
        (module_name, get_useful_variables_effects());

  reset_current_module_entity();
  reset_current_module_statement();
  reset_proper_rw_effects();
  reset_rw_effects();
  reset_invariant_rw_effects();
  reset_useful_variables_effects();

  // functions that can be pointed by effects_computation_reset_func:
  // effects_computation_no_reset
  // reset_convex_in_out_regions
  // reset_convex_rw_regions
  (*effects_computation_reset_func)(module_name);
  return(true);
}


