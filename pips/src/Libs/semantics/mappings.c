/*

  $Id: mappings.c 23412 2017-08-09 15:07:09Z irigoin $

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
 /* Variable value mappings package
  *
  * Establish mappings between analyzed scalar variable entities and
  * variable value entities for a given module (see transformer/value.c).
  *
  * Handle static aliasing in Fortran, i.e. equivalences too.
  *
  * Cannot handle more than one module at a time: no recursivity on
  * modules or chaos will occur.
  *
  * See package value.c for more information on functions more or less
  * independent of the internal representation.
  *
  * Francois Irigoin, 20 April 1990
  *
  */

#include <stdio.h>

#include "genC.h"
#include "linear.h"
#include "ri.h"
#include "effects.h"
#include "ri-util.h"
#include "workspace-util.h"
#include "prettyprint.h"
#include "effects-util.h"
#include "constants.h"

#include "misc.h"

#include "arithmetique.h"
#include "vecteur.h"
#include "contrainte.h"

/* To convert non constant effects into constant effects */
#include "effects-simple.h"
#include "effects-generic.h"

#include "transformer.h"

#include "semantics.h"
#include "preprocessor.h"
#include "properties.h"

/* FORTRAN 77 EQUIVALENCE */

static Pcontrainte equivalence_equalities = CONTRAINTE_UNDEFINED;

static void reset_equivalence_equalities()
{
    if(equivalence_equalities != CONTRAINTE_UNDEFINED) {
	equivalence_equalities = contraintes_free(equivalence_equalities);
    }
}

transformer tf_equivalence_equalities_add(transformer tf)
{
    /* I need here a contraintes_dup() that is not yet available
       in Linear and I cannot change Linear just before the DRET meeting;
       I've got to modify transformer_equalities_add() and to give it
       a behavior different from transformer_equality_add() */
    tf = transformer_equalities_add(tf, equivalence_equalities);
    return tf;
}

static void add_equivalence_equality(entity e, entity eq)
{
    /* assumes e and eq are different */
    Pvecteur v = vect_new((Variable) e, 1);
    Pcontrainte c;

    vect_add_elem(&v, (Variable) eq, -1);
    c = contrainte_make(v);
    /* Strange: there is no macro to chain a contrainte on a list of
       contrainte */
    c->succ = equivalence_equalities;
    equivalence_equalities = c;
}

void add_equivalenced_values(entity e, entity eq, bool readonly)
{
  /* e and eq are assumed to be different scalar variables of the same
     analyzed type */
  /* eq will be seen as e, as far as values are concerned,
     but for printing */
  /* new equalities e#new == eq#new and e#old == eq#old
     have to be added to the preconditions just before they
     are stored; since eq should never be written no eq#old
     should appear; thus the first equation is enough */

  /* By definition, all variables are conflicting
     with themselves but this is assumed filtered out above. */

  pips_assert("e is not eq", e!=eq);

  add_synonym_values(e, eq, readonly);
  /* add the equivalence equations */
  add_equivalence_equality(e, eq);

}

/* ???? */

/* void add_interprocedural_value_entities
 */
static void add_interprocedural_value_entities(entity e)
{
    pips_debug(8,"for %s\n", entity_name(e));
    if(!entity_has_values_p(e)) {
	entity a = entity_undefined;
	if((a=value_alias(e))==entity_undefined){
	    add_new_value(e);
	    add_old_value(e);
	    add_intermediate_value(e);
	    add_or_kill_equivalenced_variables(e, false);
	}
	else {
	    add_new_alias_value(e,a);
	    add_old_alias_value(e,a);
	    add_intermediate_alias_value(e,a);
	}
    }
}

static void add_interprocedural_new_value_entity(entity e)
{
    pips_debug(8,"add_interprocedural_new_value_entities" "for %s\n",
	       entity_name(e));
    if(!entity_has_values_p(e)) {
	entity a = entity_undefined;
	if((a=value_alias(e))==entity_undefined){
	    add_new_value(e);
	    /* CA: information on aliasing variables erased*/
	    add_or_kill_equivalenced_variables(e,true);
	}
	else {
	    add_new_alias_value(e,a);
	}
    }
}

static void add_intraprocedural_value_entities_unconditionally(entity e)
{
  pips_debug(8, "for %s\n", entity_name(e));
  add_new_value(e);
  add_local_old_value(e);
  add_local_intermediate_value(e);
  add_or_kill_equivalenced_variables(e, false);
}

/* Use to be static, but may be called from ri_to_transformer. */
/* void add_intraprocedural_value_entities(entity e)
 */
void add_intraprocedural_value_entities(entity e)
{
  type ut = entity_basic_concrete_type(e);

  pips_debug(8, "for %s\n", entity_name(e));
  if(!entity_has_values_p(e) && type_variable_p(ut) ) {
    add_intraprocedural_value_entities_unconditionally(e);
  }
}

/* Look for variables equivalenced with e. e already has values associated
 * although it may not be a canonical representative of its equivalence
 * class...
 *
 * Forget dynamic aliasing between formal parameters.
 *
 * Handle intraprocedural aliasing only.
 *
 * Do not handle interprocedural aliasing: this does not seem to be the right place
 * because too many synonyms, not visible from the current procedure, are
 * introduced (global_shared = area_layout(type_area(t));
 * */

void add_or_kill_equivalenced_variables(entity e, bool readonly)
{
  storage s = entity_storage(e);
  entity re = e; /* potential canonical representative for all variables equivalenced with e */

  pips_debug(8,	"Begin for %s %s\n", entity_name(e),
	     readonly? "readonly" : "read/write");

  pips_assert("e has values", entity_has_values_p(e));

  if(storage_ram_p(s)) {
    list local_shared = ram_shared(storage_ram(s));
    bool array_equivalenced = false;
    entity sec = ram_section(storage_ram(s));
    type t = entity_type(sec);
    list ce = list_undefined;

    pips_assert("t is an area", type_area_p(t));

    /* Is e intraprocedurally equivalenced/aliased with an array or a
     * non-analyzable variable which would make e and all its aliased
     * variables unanalyzable?  */
    for(ce=local_shared; !ENDP(ce); POP(ce)) {
      entity eq = ENTITY(CAR(ce));

      /* Since the equivalence is reflexive, no need to process e==eq again. */
      if(e==eq) continue;
      /* Since the equivalence is symetrical, eq may have been processed
         already. */
      if(entity_has_values_p(eq)) continue;

      /* this approximate test by Pierre Jouvelot should be
	 replaced by an exact test but it does not really matter;
	 an exact test could only be useful in presence of arrays;
	 and in presence of arrays we do nothing here */
      if(entities_may_conflict_p(e, eq) && !analyzable_scalar_entity_p(eq)) {
	pips_user_warning("Values for variable %s are not analyzed because "
			  "%s is aliased with scalar variable %s with non "
			  "analyzed type %s or with array variable\n",
			  entity_name(e), entity_name(e), entity_name(eq),
			  type_to_string(entity_type(eq)));
	array_equivalenced = true;
	break;
      }

      if(entities_may_conflict_p(e, eq) && analyzable_scalar_entity_p(eq)) {
	if(!type_equal_p(entity_type(e),entity_type(eq))) {
	  pips_user_warning("Values for variable %s of type %s are not analyzed because "
			    "%s is aliased with scalar variable %s with different "
			    "type %s\n",
			    entity_name(e), type_to_string(entity_type(e)),
			    entity_name(e), entity_name(eq),
			    type_to_string(entity_type(eq)));
	  array_equivalenced = true;
	  break;
	}
      }
      if(entities_may_conflict_p(e, eq) && strcmp(entity_name(eq), entity_name(re))<0) {
	re = eq;
      }
    }

    /* if it's not, go ahead: it exists at least one eq such that e and eq
       are different, are scalars and have the same analyzable type. All
       eq conflicting with e meets these conditions. */
    if(!array_equivalenced) {

      /* Declare values for the canonical representative re */
      if(e!=re) {
	pips_debug(8, "Canonical representative is %s\n", entity_local_name(re));
	/* Give values to re which should have none and remove values of
	   e. Assume that e and re are local variables. */
	pips_assert("re has no values", !entity_has_values_p(re));
	remove_entity_values(e, readonly);
	add_new_value(re);
	if(!readonly) {
	  add_old_value(re);
	  add_intermediate_value(re);
	}
      }

      /* If it is intra-procedurally equivalenced, set the synonyms as
       * read-only variables
       */
      for(ce=local_shared; !ENDP(ce); POP(ce)) {
	entity eq = ENTITY(CAR(ce));

	if(re==eq) continue;
	if(entities_may_conflict_p(re, eq)) {
	  /* if eq is an integer scalar variable it does not
	     only have a destructive effect */
	  add_equivalenced_values(re, eq, readonly);
	}
      }
    }
    else {
      /* Variable e is equivalenced with an array or a non-integer
       * variable and cannot be analyzed; it must be removed from
       * the hash tables.
       */
      remove_entity_values(e, readonly);
    }
  }
  else if(storage_return_p(s)) {
    /* semantics analysis should be performed on this kind of variable
       but it has probably been eliminated earlier; no equivalence
       possible anyway! */
    // FI: the warning message is not useful. See formal parameters
    // pips_user_warning("storage return\n");
    ;
  }
  else if(storage_formal_p(s))
    /* to be dealt with later if we assume non-standard dynamic
       aliasing between formal parameters */
    ;
  else
    pips_internal_error("unproper storage = %d (%s), for entity %s", storage_tag(s), storage_to_string(s), entity_name(e));

  pips_debug(8,	"End for %s\n", entity_name(e));
}

static void allocate_module_value_mappings(entity m)
{
    /* this routine tries to estimate the sizes of the hash tables,
       although the hashtable package has enlarging capability;
       its usefulness is limited... but keep at least hash table
       allocations! */

  /* FI: not a good estimate for C codes with local delcarations */
    list module_intra_effects = load_module_intraprocedural_effects(m);
    int old_value_number = 0;
    int intermediate_value_number = 0;
    int new_value_number = 0;

    /* count interprocedural effects on scalar integer variables
       before allocating hash tables; too many entries might be
       expected because the same variable could appear many times,
       at least twice, once in a read effect and once in a write 
       effect; entries for arrays equivalenced with scalar variables
       are ignored; some slack is added before allocating the hash
       tables; module_inter_effects are (should be) included into
       module_intra_effects */
    FOREACH(EFFECT, ef,	module_intra_effects)
    {
	entity e = reference_variable(effect_any_reference(ef));
	action a = effect_action(ef);
	// The estimation is poor when abstract effects occur
	if(integer_scalar_entity_p(e))
	    new_value_number++;
	if(action_write_p(a))
	    old_value_number++;
    }

    /* add 50 % slack for underestimation (some more slack will be added
       by the hash package */
    new_value_number *= 3; new_value_number /= 2;
    old_value_number *= 3; old_value_number /= 2;
    /* the hash package does not like very small sizes */
    new_value_number = MAX(10,new_value_number);
    old_value_number = MAX(10,old_value_number);
    /* overapproximate intermediate value number */
    intermediate_value_number = old_value_number;

    pips_debug(8, "old_value_number = %d\n", old_value_number);
    pips_debug(8, "new_value_number = %d\n", new_value_number);

    /* allocate hash tables */
    allocate_value_mappings(new_value_number, old_value_number,
			    intermediate_value_number);
}

/* It is assumed that al is an abstract location that is written and
   which may conflict with effects in effect list el. If there is a
   conflict, than the variable associated to this effect is
   written.

   It should be generalized to non-interprocedural cases.
*/
void add_implicit_interprocedural_write_effects(entity al, list el)
{
  type alt = entity_type(al);

  if(type_unknown_p(alt)
     || type_area_p(alt) // FI: Let's agree about typing issues!
     || get_bool_property("ALIASING_ACROSS_TYPES")
     || overloaded_type_p(alt)) {
    FOREACH(EFFECT, ef, el) {
      reference r = effect_any_reference(ef);
      entity v = reference_variable(r);

      if(!entity_abstract_location_p(v)
	 && entities_may_conflict_p(al, v)
	 && analyzable_scalar_entity_p(v)) {
	add_interprocedural_value_entities(v);
      }
    }
  }
  else {
    FOREACH(EFFECT, ef, el) {
      reference r = effect_any_reference(ef);
      entity v = reference_variable(r);
      type vt = ultimate_type(entity_type(v));

      if(!entity_abstract_location_p(v)
	 && entities_may_conflict_p(al, v)
	 && type_equal_p(alt, vt)) {
	if(dummy_parameter_entity_p(v))
	  pips_internal_error("Effects cannot be related to dummy parameters.");
	add_interprocedural_value_entities(v);
      }
    }
  }
}

static bool entity_for_value_mapping_p(entity e)
{
  return entity_not_constant_or_intrinsic_p(e) 
    && !typedef_entity_p(e)
    && !entity_field_p(e);
}

// Declared because they are called recursively but static
static void add_intraprocedural_field_entities(reference r, list fl);
static void add_interprocedural_field_entities(reference r, list fl);

/* Check which fields combined with r would lead to analyzed values
 * and recurse for fields which are struct themselves.
 *
 * A similar function would be useful to handle struct assignments in
 * semantics or points-to or effect analysis.
 */
static void add_inter_or_intraprocedural_field_entities(reference r, list fl, bool intra_p)
{
  FOREACH(ENTITY, f, fl) {
    type t = entity_basic_concrete_type(f);
    if(analyzed_type_p(t)) {
      reference fr = simple_reference_add_field_dimension(copy_reference(r), f);
      entity l = make_location_entity(fr); // Do not free fr as it should be the initial value
      if(!entity_has_values_p(l)) {
	if(intra_p)
	  add_intraprocedural_value_entities(l);
	else
	  add_interprocedural_value_entities(l);
      }
    }
    else if(struct_type_p(t)) {
      reference fr = simple_reference_add_field_dimension(copy_reference(r), f);
      list nfl = struct_type_to_fields(t);
      if(intra_p)
	add_intraprocedural_field_entities(fr, nfl);
      else
	add_interprocedural_field_entities(fr, nfl);
      free_reference(fr);
    }
  }
}

static void add_intraprocedural_field_entities(reference r, list fl)
{
  add_inter_or_intraprocedural_field_entities(r, fl, true);
}

static void add_interprocedural_field_entities(reference r, list fl)
{
  add_inter_or_intraprocedural_field_entities(r, fl, false);
}
static void add_reference_values(reference r, bool write_p, bool global_p)
{
  entity e = make_location_entity(r);
  if(global_p) {
    if(write_p)
      add_interprocedural_value_entities(e);
    else
      add_interprocedural_new_value_entity(e);
  }
  else {
    if(write_p)
      add_intraprocedural_value_entities(e);
    else
      add_intraprocedural_value_entities(e);
  }
}

/* If effect e meets all conditions to represent a location whose
 * value could and should be analyzed, create the related values.
 */
static void create_values_for_simple_effect(effect e, entity m)
{
  if(store_effect_p(e)) {
    reference r = effect_any_reference(e);
    if(generic_atomic_points_to_reference_p(r, false)) {
      entity v = reference_variable(r);
      if(entity_variable_p(v)
	 && !place_holder_variable_p(v)
	 && !effects_package_entity_p(v)
	 && !entity_abstract_location_p(v)) {
	storage vs = entity_storage(v);
	if(storage_ram_p(vs)
	   || storage_formal_p(vs)
	   /* || storage_return_p(vs)*/) {
	  // atomic_points_to_reference_p(r)
	  // scalar_reference_p(r))
	  type t = points_to_reference_to_concrete_type(r);
	  if(analyzed_type_p(t)) { // implies scalar_type_p(t)
	    // FI: the effect may be local to the module or visible outside;
	    // the effect may be a read or a write
	    bool write_p = action_write_p(effect_action(e));
	    bool global_p = global_variable_p(v)
	      || variable_is_a_module_formal_parameter_p(v, m)
	      || formal_context_variable_p(v);
	    add_reference_values(r, write_p, global_p);
	  }
	}
      }
    }
  }
  return;
}

/* Declare value entities necessary to analyze locations defined by
 * proper effects.
 *
 */

static bool add_values_for_simple_effects_of_statement(statement s)
{
  // #include "effects-generic.h"
  extern effects load_proper_rw_effects(statement);
  effects fx = load_proper_rw_effects(s);
  entity m = get_current_module_entity();

  if(!get_bool_property("CONSTANT_PATH_EFFECTS")) {
    list el = effects_effects(fx);
    FOREACH(EFFECT, e, el) {
      list cel = list_undefined;
      if(pt_to_list_undefined_p()) {
	// FI: use of a generic effect function
	effect (*effect_dup_func_save)(effect eff) = effect_dup_func;
	effect (*reference_to_effect_func_save)(reference, action, bool) = reference_to_effect_func;
	effect_dup_func = copy_effect;
	reference_to_effect_func = reference_to_reference_effect;
	cel = effect_to_constant_path_effects_with_no_pointer_information(e);
	effect_dup_func = effect_dup_func_save;
	reference_to_effect_func = reference_to_effect_func_save;
      }
      else {
	// FI: hopefully, the context is not used for simple effects...
	transformer context = transformer_undefined;
	cel = effect_to_constant_path_effects_with_points_to(e, s, context);
      }
      FOREACH(EFFECT, ce, cel)
	if(effect_write_p(e) && store_effect_p(e) && store_independent_effect_p(e))
	  create_values_for_simple_effect(ce, m);
      FOREACH(EFFECT, ce, cel)
	if(!effect_write_p(e) && store_effect_p(e) && store_independent_effect_p(e))
	  create_values_for_simple_effect(ce, m);
      gen_full_free_list(cel);
    }
  }
  else {
    list el = effects_effects(fx);
    FOREACH(EFFECT, e, el) {
      if(effect_write_p(e) && store_effect_p(e) && store_independent_effect_p(e))
	create_values_for_simple_effect(e, m);
    }
    FOREACH(EFFECT, e, el) {
      if(!effect_write_p(e) && store_effect_p(e) && store_independent_effect_p(e))
	create_values_for_simple_effect(e, m);
    }
  }

  return true;
}

static void values_for_current_module_intraprocedural_simple_effects(void)
{
  statement s = get_current_module_statement();
  if(!get_bool_property("CONSTANT_PATH_EFFECTS")) {
    pips_user_warning("Property \"CONSTANT_PATH_EFFECTS\" is set to its "
		      "experimental value, false.");
  }
  gen_recurse(s, statement_domain,
	      add_values_for_simple_effects_of_statement,
	      gen_null);
  return;
}

/* void module_to_value_mappings(entity m): build hash tables between
 * variables and values (old, new and intermediate), and between values
 * and names for module m, as well as equivalence equalities
 *
 * NW:
 * before calling "module_to_value_mappings"
 * to set up the hash table to translate value into value names
 * for module with name (string) module_name
 * do:
 *
 * set_current_module_entity( local_name_to_top_level_entity(module_name) );
 *
 * (the following call is only necessary if a variable of type entity
 * such as "module" is not already set)
 * module = get_current_module_entity();
 *
 * set_current_module_statement( (statement)
 * 			      db_get_memory_resource(DBR_CODE,
 * 						     module_name,
 * 						     true) );
 * set_cumulated_rw_effects((statement_effects)
 * 			 db_get_memory_resource(DBR_CUMULATED_EFFECTS,
 * 						module_name,
 * 						true));
 *
 * (that's it, but we musn't forget to reset everything
 * after the call to "module_to_value_mappings", as below)
 *
 * reset_current_module_statement();
 * reset_cumulated_rw_effects();
 * reset_current_module_entity();
 * free_value_mappings();
 */
void module_to_value_mappings(entity m)
{
  list module_inter_effects;
  list module_intra_effects;

  pips_debug(8,"begin for module %s\n", module_local_name(m));

  pips_assert("m is a module", entity_module_p(m));

  // hook cleanup in free_value_mappings
  reset_hooks_register(error_reset_value_mappings);
  /* free_value_mappings(); */

  allocate_module_value_mappings(m);

  /* reset local intermediate value counter for
     make_local_intermediate_value_entity and
     make_local_old_value_entity */
  reset_value_counters();
  reset_equivalence_equalities();
  reset_temporary_value_counter();
  set_analyzed_types();

  /* module_inter_effects = code_effects(value_code(entity_initial(m))); */
  module_inter_effects = load_summary_effects(m);

  /* look for interprocedural write effects on scalar analyzable variables
     and generate proper entries into hash tables */
  FOREACH(EFFECT, ef, module_inter_effects) {
    if(store_effect_p(ef)) {
      reference r = effect_any_reference(ef);
      entity e = reference_variable(r);
      action a = effect_action(ef);
      if(analyzable_scalar_entity_p(e) // check type
	 && !effects_package_entity_p(e)
	 && (
	     action_write_p(a)
	     ||
	     /* In C, write effects on scalar formal parameter are
		masked by the value passing mode but the copy may
		nevertheless be written inside the function. */
	     (c_module_p(m) && entity_formal_p(e))
	     ||
	     /* To keep the summary transformer consistent
		although the return value has no old value */
	     (c_module_p(m) && storage_return_p(entity_storage(e))
	      ))
	 )
	add_interprocedural_value_entities(e);
      else if(entity_abstract_location_p(e) && action_write_p(a)) {
	add_implicit_interprocedural_write_effects(e, module_inter_effects);
      }
      else if(constant_path_analyzed_p() && analyzed_reference_p(r)) {
	type t = points_to_reference_to_concrete_type(r);
	if(analyzed_type_p(t)) {
	  entity le = make_location_entity(r);
	  add_interprocedural_value_entities(le);
	}
	free_type(t);
      }
    }
  }

  /* look for interprocedural read effects on scalar analyzable variables
     and generate proper entries into hash tables */
  FOREACH(EFFECT, ef, module_inter_effects) {
    if(store_effect_p(ef)) {
      entity e = reference_variable(effect_any_reference(ef));
      action a = effect_action(ef);
      if(analyzable_scalar_entity_p(e) && action_read_p(a)) {
        if(c_module_p(m) && 
	   ( storage_return_p(entity_storage(e))
	     /* static variables have an old value too */
	     ||  entity_static_variable_p(e) 
	     )
	   )
	  add_interprocedural_value_entities(e);
	else
	  add_interprocedural_new_value_entity(e);
      }
    }
  }

  module_intra_effects = load_module_intraprocedural_effects(m);

  /* look for intraprocedural write effects on scalar analyzable variables
     and generate proper entries into hash tables */
  FOREACH(EFFECT, ef, module_intra_effects) {
    if(store_effect_p(ef)) {
      entity e = reference_variable(effect_any_reference(ef));
      action a = effect_action(ef);
      if(analyzable_scalar_entity_p(e) && action_write_p(a)) {
	if(storage_return_p(entity_storage(e))) {
	  add_interprocedural_value_entities(e);
	}
	else {
	  if(!entity_anywhere_locations_p(e)
	     && !entity_typed_anywhere_locations_p(e)
	     && !entity_heap_location_p(e))
	    add_intraprocedural_value_entities(e);
	}
      }
      else if(constant_path_analyzed_p() && action_write_p(a)) {
	reference rlhs = cell_any_reference(effect_cell(ef));

	if (analyzed_reference_p(rlhs)) {
	  entity le = make_location_entity(rlhs);
	  add_intraprocedural_value_entities(le);
	}
      }
    }
  }

  /* look for intraprocedural read effects on scalar analyzable variables
     and generate proper entry into value name hash table if it has
     not been entered before; interprocedural read effects are implicitly
     dealed with since they are included;
     most entities are likely to have been encountered before; however
     in parameters and uninitialized variables have to be dealt with */
  FOREACH(EFFECT, ef, module_intra_effects) {
    if(store_effect_p(ef)) {
      entity e = reference_variable(effect_any_reference(ef));
      if(analyzable_scalar_entity_p(e) && !entity_has_values_p(e)) {
	/* FI: although it may only be read within this procedure, e
	 * might be written in another one thru a COMMON; this write
	 * is not visible from OUT, but only from a caller of out;
	 * because we have only a local intraprocedural or a global
	 * interprocedural view of aliasing, we have to create useless
	 * values:-(
	 *
	 * add_new_value(e);
	 *
	 * Note: this makes the control structure of this procedure
	 * obsolete!
	 */
	/* This call is useless because it only is effective if
	 * entity_has_values_p() is true:
	 * add_intraprocedural_value_entities(e);
	 */
	  if(!entity_anywhere_locations_p(e)
	     && !entity_typed_anywhere_locations_p(e)
	     && !entity_heap_location_p(e))
	    add_intraprocedural_value_entities_unconditionally(e);
	/* A stronger call to the same subroutine is included in
	 * the previous call:
	 * add_or_kill_equivalenced_variables(e, true);
	 */
      }
    }
  }

  /* scan declarations to make sure that private variables are
   * taken into account; assume a read and write effects on these
   * variables, although they may not even be used.
   *
   * Only intraprocedural variables can be privatized (1 Aug. 92)
   */
  list dl = current_module_declarations();
  FOREACH(ENTITY, e, dl) {
    if(analyzable_scalar_entity_p(e) && !entity_has_values_p(e)
       && !location_entity_p(e) && !entity_heap_location_p(e)) {
      if(storage_return_p(entity_storage(e))) {
	/* This should be useless if return variables are taken
	   into account by effect analysis. No problem with
	   Fortran because the return variable really is assigned
	   a value. Not obvious in C because the assignment is
	   implicit in the return statement. In C the return
	   variable is more like a value: it cannot be re-assigned. */
	add_interprocedural_value_entities(e);
      }
      else {
	add_intraprocedural_value_entities(e);
      }
    }
    else if(entity_variable_p(e) && !entity_abstract_location_p(e)) {
      storage es = entity_storage(e);
      // FI: do not process named or derived types
      //if(storage_ram_p(es) || storage_return_p(es)) {
      /* FI: Only return variables are forgotten by effects
       *
       * FI: no, this is wrong in C; local variables are dropped
       * from effect when their declaration statements are
       * processed. They cannot be found in the effects of the
       * module statement.
       */
      if(storage_ram_p(es) || storage_return_p(es)) {
	type t = entity_basic_concrete_type(e);
	if(constant_path_analyzed_p() && struct_type_p(t)) {
	  /* We need references to all fields, direct or indirect when
	   * a field is itself a struct
	   */
	  reference r = make_reference(e, NIL);
	  list fl = struct_type_to_fields(t);
	  add_intraprocedural_field_entities(r, fl);
	  free_reference(r);
	}
      }
    }
  }

  /* scan other referenced variables to make sure everyone has an
   * entry in the symbol table
   */
  set re = get_referenced_entities_filtered(get_current_module_statement(), (bool (*)(void *))gen_true, entity_for_value_mapping_p);
  SET_FOREACH(entity, e, re) {
    if(analyzable_scalar_entity_p(e) && !entity_has_values_p(e)) {
      pips_assert("should not go there ?", !storage_return_p(entity_storage(e)));
      add_interprocedural_value_entities(e);
    }
  }

  // FI: to analyze array elements with constant subscripts, we would
  // need to get a list of all constant atomic references with types
  // that are analyzed.

  // FI: for points-to analysis, we need to know all formal virtual
  // entities that have been created by the points-to pass. It is not
  // clear the information may be retrieved from the module statement
  // cumulated effect, especially if scopes are used by the
  // programmer, or the module summary cumulated effects.
  if(constant_path_analyzed_p()) {
    SET_FOREACH(entity, e, re) {
      // FI: place holder variables are supposed to have been removed
      // from internal representation by C parser?
      if(entity_variable_p(e) && !place_holder_variable_p(e)) {
	storage es = entity_storage(e);
	if(storage_ram_p(es)/* || storage_return_p(es)*/) {
	  type t = entity_basic_concrete_type(e);
	  if(struct_type_p(t)) {
	    /* We need references to all fields, direct or indirect when
	     * a field is itself a struct
	     */
	    reference r = make_reference(e, NIL);
	    list fl = struct_type_to_fields(t);
	    add_interprocedural_field_entities(r, fl);
	    free_reference(r);
	  }
	}
      }
    }
  }
  set_free(re);

  /* Beware of struct return values which may generate additional
   * locations and location values
   */
  if(constant_path_analyzed_p()) {
    const char * module_name = entity_local_name(m);
    callees c = (callees) db_get_memory_resource(DBR_CALLEES,
						 module_name,
						 true);
    list lc = callees_callees(c);
    FOREACH(STRING, callee_name, lc) {
      entity f = module_name_to_entity(callee_name);
      type ft = entity_basic_concrete_type(f);
      type rt = compute_basic_concrete_type(functional_result(type_functional(ft)));
      if(struct_type_p(rt)) {
	entity rv = function_to_return_value(f);
	reference rvr = make_reference(rv, NIL);
	list fl = struct_type_to_fields(rt);
	add_intraprocedural_field_entities(rvr, fl);
	free_reference(rvr);
      }
    }
  }

  /* To be sure to retrieve all relevant locations, including array elements */
  if(constant_path_analyzed_p()) {
    values_for_current_module_intraprocedural_simple_effects();
  }

  /* for debug, print hash tables */
  ifdebug(8) {
    pips_debug(8, "hash tables for module %s\n", module_local_name(m));
    print_value_mappings();
    test_mapping_entry_consistency();
  }

  pips_debug(1, "Number of analyzed variables for module %s: %d\n",
	     module_local_name(m),
	     aproximate_number_of_analyzed_variables());
  pips_debug(1, "Number of analyzed values for module %s: %d\n",
	     module_local_name(m),
	     number_of_analyzed_values());

  pips_debug(8,"end for module %s\n", module_local_name(m));
}

/* transform a vector based on variable entities into a vector based
 * on new value entities when possible; does nothing most of the time;
 * does a little in the presence of equivalenced variables
 *
 * Ugly because it has a hidden side effect on v to handle Fortran
 * equivalences and because its implementation is dependent on type
 * Pvecteur.
 *
 * Assume that the value mappings are available (as implied by the
 * function's name!), which may not be true when dealing with call
 * sites.
 */
bool value_mappings_compatible_vector_p(Pvecteur iv)
{
  Pvecteur v = iv;
  for(;!VECTEUR_NUL_P(v); v = v->succ) {
    if(vecteur_var(v) != TCST) {
      entity e = (entity) vecteur_var(v);

      /* The variable may denote a constant with compatible type */
      if(entity_constant_p(e) && !analyzed_constant_p(e)) {
	return false;
      }

      /* or a temporary variable */
      else if(local_temporary_value_entity_p(e)) {
	;
      }

      /* Or a variable value */
      else if(entity_has_values_p(e)) {
	entity new_v = entity_to_new_value(e);

	if(new_v != entity_undefined)
	  vecteur_var(v) = (Variable) new_v;
	else
	  return false;
      }

      /* Or a phi variable, when transformers are computed by the
	 region analysis */
      else if(variable_phi_p(e)) {
	;
      }

      /* Or the vector cannot be used in the semantics analysis */
      else {
	return false;
      }
    }
  }
  return true;
}

list variables_to_values(list list_mod)
{
  list list_val = NIL;

  FOREACH(ENTITY, e, list_mod) {
    if(entity_has_values_p(e)) {
      entity v_old = entity_to_old_value(e);
      entity v_new = entity_to_new_value(e);

      list_val = CONS(ENTITY, v_old, list_val);
      list_val = CONS(ENTITY, v_new, list_val);
    }
  }
  return list_val;
}

list variable_to_values(entity e)
{
  list list_val = NIL;

  if(entity_has_values_p(e)) {
    entity v_old = entity_to_old_value(e);
    entity v_new = entity_to_new_value(e);

    list_val = CONS(ENTITY, v_old, list_val);
    list_val = CONS(ENTITY, v_new, list_val);
  }

  return list_val;
}

/* Build the list of values to be projected when the declaration list
 * list_mod is no longer valid because a block is closed/left.
 *
 * Values for static variables are preserved. Values for heap
 * variables also, in case their values are computed in the future...
 *
 * This may not be the best algorithm when locations are used because
 * the list of locations may be much longer, especially for arrays,
 * than the list of values appearing in the transformer.
 */
list dynamic_variables_to_values(list list_mod)
{
  list list_val = NIL;

  FOREACH(ENTITY, e, list_mod) {
    if(entity_has_values_p(e)
       && (variable_dynamic_p(e) || variable_stack_p(e))) {
      entity v_old = entity_to_old_value(e);
      entity v_new = entity_to_new_value(e);

      list_val = CONS(ENTITY, v_old, list_val);
      list_val = CONS(ENTITY, v_new, list_val);
    }
  }
  return list_val;
}

list variables_to_old_values(list list_mod)
{
  list list_val = NIL;

  MAP(ENTITY, e, {
    entity v_old = entity_to_old_value(e);

    list_val = CONS(ENTITY, v_old, list_val);
  }, list_mod);
  return list_val;
}

/* replace variables by new values which is necessary for equivalenced
   variables */
void variables_to_new_values(Pvecteur v)
{
  Pvecteur elem = VECTEUR_UNDEFINED;

  for(elem = v; !VECTEUR_NUL_P(elem); elem = vecteur_succ(elem)) {
    entity var = (entity) vecteur_var(elem);

    if(vecteur_var(elem)!=TCST) {
      entity v_new = entity_to_new_value(var);

      if(v_new!=var) {
	(void) vect_variable_rename(v, (Variable) var,
				    (Variable) v_new);
      }
    }
  }
}

/* Renaming of variables in v according to transformations occuring
 * later. If a variable is modified by post, its old value must
 * be used in v
 */

void
upwards_vect_rename(Pvecteur v, transformer post)
{
    /* FI: it would probably ne more efficient to
     * scan va and vb than the argument list...
     */
    list modified_values = transformer_arguments(post);

    FOREACH(ENTITY, v_new, modified_values) {
	entity v_init = new_value_to_old_value(v_new);

	(void) vect_variable_rename(v, (Variable) v_new,
				    (Variable) v_init);
    }
}
