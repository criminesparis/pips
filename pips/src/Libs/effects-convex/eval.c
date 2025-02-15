/*

  $Id: eval.c 23065 2016-03-02 09:05:50Z coelho $

  Copyright 1989-2016 MINES ParisTech
  Copyright 2009-2010 HPC Project

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
#include <string.h>
#include <stdlib.h>

#include "genC.h"
#include "linear.h"
#include "ri.h"
#include "effects.h"
#include "ri-util.h"
#include "prettyprint.h"
#include "effects-util.h"
#include "misc.h"
#include "text-util.h"
#include "newgen_set.h"
#include "points_to_private.h"
#include "pointer_values.h"

#include "effects-generic.h"
#include "effects-convex.h"

/*
  @param r1 and r2 are two path references
  @param strict_p is true if the path length of r1 must be strictly inferior
         to the path length of r2
  @param exact_p is a pointer towards a boolean, which is set to false
         is the result is an over-approximation, true if it's an exact answer.
  @return true if r1 path may be a predecessor of r2 path

  (we consider that p[1] is a predecessor of p[*], with *exact_p = false.)

  Note FI: the notion of predecessor is similar to having a prefix
  subscript list. You might want an inclusion between the memory cells
  accessed by the two references, but it is not the case since p[1] is
  a predecessor of p[*]. And, the descriptors are used... with no
  explanations. I guess you want to be able to say something with
  p[i], 0<=i<=2, since p[0], p[1], p[2] and p[*] may be used.

 */
bool convex_cell_reference_preceding_p(reference r1, descriptor d1,
    reference r2, descriptor d2,
    transformer current_precondition,
    bool strict_p,
    bool * exact_p)
{
  bool res = true;
  entity e1 = reference_variable(r1);
  list ind1 = reference_indices(r1);
  size_t r1_path_length = gen_length(ind1);
  entity e2 = reference_variable(r2);
  list ind2 = reference_indices(r2);
  size_t r2_path_length = gen_length(ind2);

  pips_debug(8, "input references r1 : %s, r2: %s \n",
      reference_to_string(r1),
      reference_to_string(r2));

  *exact_p = true;
  if (same_entity_p(e1, e2)
      && ((r1_path_length < r2_path_length)
          || (!strict_p && r1_path_length == r2_path_length)))
  {
    /* same entity and the path length of r1 is shorter than the
     * path length of r2.
     *
     * we now have to check that each common index matches
     */
    pips_debug(8,"same entities, and r1 path is shorter than r2 path\n");
    while (res && !ENDP(ind1))
    {
      expression exp1 = EXPRESSION(CAR(ind1));
      expression exp2 = EXPRESSION(CAR(ind2));

      if(!expression_equal_p(exp1, exp2))
      {
        res = false;
        *exact_p = true;
      }

      POP(ind1);
      POP(ind2);
    }
    if (res)
    {
      /* only matching reference indices have been found (phi
       * variables or struct field entities).
       *
       * we must now check the descriptors.
       */
      region reg1 = make_effect(make_cell(is_cell_reference, r1),
          make_action_write_memory(),
          make_approximation_exact(), d1);
      region reg2 = make_effect(make_cell(is_cell_reference, r2),
          make_action_write_memory(),
          make_approximation_exact(), d2);

      pips_debug_effect(6, "reg1 = \n", reg1);
      pips_debug_effect(6, "reg2 = \n", reg1);

      list li = region_intersection(reg1, reg2);
      if (ENDP(li))
      {
        res = false;
        *exact_p = true;
      }
      else
      {

        pips_debug_effect(8, "reg2 before eliminating phi variables: \n ", reg2);

        effect reg2_dup = copy_effect(reg2);
        list l_reg2 = CONS(EFFECT,reg2_dup,NIL);
        list l_phi = phi_entities_list(r1_path_length+1,r2_path_length);
        project_regions_along_variables(l_reg2, l_phi);
        gen_free_list(l_reg2);
        gen_free_list(l_phi);
        pips_debug_effect(8, "reg2_dup after elimination: \n ", reg2_dup);

        effect reg1_dup = copy_effect(reg1);
        if (!transformer_undefined_p(current_precondition))
        {
          Psysteme sc_context = predicate_system(transformer_relation(current_precondition));
          region_sc_append(reg1_dup, sc_context, false);
        }

        pips_debug_effect(8, "reg1_dup after adding preconditions: \n ", reg1_dup);
        pips_debug_effect(8, "reg1 after adding preconditions: \n ", reg1);

        list ld = region_sup_difference(reg1_dup, reg2_dup);
        if (ENDP(ld))
        {
          res = true;
          *exact_p = true;
        }
        else
        {
          res = true;
          *exact_p = false;
        }
        gen_full_free_list(ld);
      }
      gen_full_free_list(li);

      cell_reference(effect_cell(reg1)) = reference_undefined;
      effect_descriptor(reg1) = descriptor_undefined;
      free_effect(reg1);

      cell_reference(effect_cell(reg2)) = reference_undefined;
      effect_descriptor(reg2) = descriptor_undefined;
      free_effect(reg2);
    }
  }
  else
  {
    res = false;
    *exact_p = true;
  }

  pips_debug(8, "end : r1 is %s a predecessor of r2 (%s exact)\n", res ? "":"not", *exact_p ? "":"not");
  return res;
}


bool convex_cell_preceding_p(cell c1, descriptor d1,
			     cell c2, descriptor d2,
			     transformer current_precondition,
		             bool strict_p,
			     bool * exact_p)
{
  reference r1 = cell_any_reference(c1);
  reference r2 = cell_any_reference(c2);

  return convex_cell_reference_preceding_p(r1, d1, r2, d2, current_precondition,
					   strict_p, exact_p);
}


void simple_reference_to_convex_reference_conversion(reference ref, reference * output_ref, descriptor * output_desc)
{

  effect reg = make_effect(make_cell_reference(make_reference(reference_variable(ref), NIL)),
      make_action_write_memory(),
      make_approximation_exact(),
      make_descriptor_convex(sc_new()));

  FOREACH(EXPRESSION, exp, reference_indices(ref))
  {
    if((expression_reference_p(exp)
        && entity_field_p(reference_variable(expression_reference(exp)))))
    {
      entity e = reference_variable(expression_reference(exp));
      effect_add_field_dimension(reg, e);
    }
    else
      convex_region_add_expression_dimension(reg, exp);
  }
  *output_ref = effect_any_reference(reg);
  *output_desc = effect_descriptor(reg);

  pips_debug_effect(6, "reg = \n", reg);

  cell_reference(effect_cell(reg)) = reference_undefined;
  effect_descriptor(reg) = descriptor_undefined;
  free_effect(reg);
}

void simple_cell_to_convex_cell_conversion(cell input_cell, cell * output_cell, descriptor * output_desc)
{

  reference input_ref = cell_any_reference(input_cell);
  reference output_ref = reference_undefined;

  simple_reference_to_convex_reference_conversion(input_ref, &output_ref, output_desc);
  *output_cell = make_cell_reference(output_ref);
}




/*
  @param c is a the convex cell for which we look an equivalent constant path
  @param ptl is the list of points-to in which we search for constant paths
  @param  exact_p is a pointer towards a boolean. It is set to true if
         the result is exact, and to false if it is an approximation,
	 either because the matching points-to sources found in ptl are
	 over-approximations of the preceding path of input_ref or because
	 the matching points-to have MAY approximation tag.
  @return a list of constant path effects. It is a list because at a given
          program point the cell may correspond to several constant paths.


  original comment:
  goal: see if cell c can be shortened by replacing its indirections
  by their values when they are defined in ptl. For instance, p[0][0]
  and (p,q,EXACT) is reduced to q[0]. And if (q,i,EXACT) is also
  available, the reference is reduced to i. The reduced cell is less likely
  to be invalidated by a write effect. The function is called "eval"
  because its goal is to build an as constant as possible reference or
  gap.

  I currently assume that points-to sinks are constant paths because
  in the last example we should also have (p[0], i, EXACT) in the
  points-to list. (BC)

  This function is called by effects to see if a convex memory access path
  can be transformed into a constant one.
*/
list eval_convex_cell_with_points_to(cell c, descriptor d, list ptl, bool *exact_p, transformer current_precondition)
{

  return generic_eval_cell_with_points_to(c, d, ptl, exact_p, current_precondition,
					  convex_cell_reference_preceding_p,
					  convex_cell_reference_with_address_of_cell_reference_translation,
					  simple_reference_to_convex_reference_conversion);
}


list convex_effect_to_constant_path_effects_with_points_to(effect eff)
{
  list le = NIL;
  bool exact_p;
  reference ref = effect_any_reference(eff);

  if (effect_reference_dereferencing_p(ref, &exact_p))
  {
    pips_debug(8, "dereferencing case \n");
    bool exact_p = false;
    transformer context;
    if (effects_private_current_context_empty_p())
      context = transformer_undefined;
    else {
      context = effects_private_current_context_head();
    }

    list l_eval = eval_convex_cell_with_points_to(effect_cell(eff), effect_descriptor(eff),
        points_to_list_list(load_pt_to_list(effects_private_current_stmt_head())),
        &exact_p, context);
    if (ENDP(l_eval))
    {
      pips_debug(8, "no equivalent constant path found -> anywhere effect\n");
      /* We have not found any equivalent constant path : it may point anywhere */
      /* We should maybe contract these effects later. Is it done by the callers ? */
      le = CONS(EFFECT, make_anywhere_effect(copy_action(effect_action(eff))), le);
    }
    else
    {
      /* change the resulting effects action to the current effect action */
      if (effect_read_p(eff))
        effects_to_read_effects(l_eval);
      le = gen_nconc(l_eval,le);
    }
  }
  else
    le = CONS(EFFECT, copy_effect(eff), le);
  return le;
}


list convex_effect_find_aliased_paths_with_pointer_values(effect eff, statement s)
{
  bool exact_p;
  list l_pv = cell_relations_list( load_pv(s));
  pv_context ctxt = make_simple_pv_context();
  list l_aliased = generic_effect_find_aliases_with_simple_pointer_values(eff, l_pv, &exact_p, transformer_undefined,
      convex_cell_preceding_p,
      convex_cell_with_address_of_cell_translation,
      convex_cell_with_value_of_cell_translation,
      convex_cells_intersection_p,
      convex_cells_inclusion_p,
      simple_cell_to_convex_cell_conversion);

  reset_pv_context(&ctxt);
  return l_aliased;
}




list convex_effect_to_constant_path_effects_with_pointer_values(effect __attribute__ ((unused)) eff)
{
  list le = NIL;
  bool exact_p;
  reference ref = effect_any_reference(eff);

  if (effect_reference_dereferencing_p(ref, &exact_p))
  {
    pips_debug(8, "dereferencing case \n");
    bool exact_p = false;
    list l_aliased = convex_effect_find_aliased_paths_with_pointer_values(eff, effects_private_current_stmt_head());
    pips_debug_effects(8, "aliased effects\n", l_aliased);

    FOREACH(EFFECT, eff_alias, l_aliased)
    {
      entity ent_alias = effect_entity(eff_alias);
      if (undefined_pointer_value_entity_p(ent_alias)
          || null_pointer_value_entity_p(ent_alias))
      {
        // currently interpret them as anywhere effects since these values
        // are not yet well integrated in abstract locations lattice
        // and in effects computations
        // to be FIXED later.
        le = CONS(EFFECT, make_anywhere_effect(copy_action(effect_action(eff_alias))), le);
        free_effect(eff_alias);
      }
      else if (entity_abstract_location_p(effect_entity(eff_alias))
          || !effect_reference_dereferencing_p(effect_any_reference(eff_alias), &exact_p)) {
        le = CONS(EFFECT, eff_alias, le);
        /* it should be a union here.
         * However, we expect the caller
         * to perform the contraction afterwards. */
      }
      else
        free_effect(eff_alias);
    }
    gen_free_list(l_aliased);
  }
  else {
    // functions that can be pointed by effect_dup_func:
    // simple_effect_dup
    // region_dup
    // copy_effect
    le = CONS(EFFECT, (*effect_dup_func)(eff), le);
  }

  return le;
}
