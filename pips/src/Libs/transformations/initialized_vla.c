/*

  $Id: initialized_vla.c 23495 2018-10-24 09:19:47Z coelho $

  Copyright 1989-2014 MINES ParisTech

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

// do not compile unless required
#include "phases.h"
#if defined(BUILDER_CHECK_INITIALIZE_VLA_WITH_EFFECTS) ||     \
  defined(BUILDER_CHECK_INITIALIZE_VLA_WITH_PRECONDITIONS) || \
  defined(BUILDER_CHECK_INITIALIZE_VLA_WITH_REGIONS) ||       \
  defined(BUILDER_INITIALIZE_VLA_WITH_EFFECTS) ||             \
  defined(BUILDER_INITIALIZE_VLA_WITH_PRECONDITIONS) ||       \
  defined(BUILDER_INITIALIZE_VLA_WITH_REGIONS)

#ifdef HAVE_CONFIG_H
    #include "pips_config.h"
#endif


/**
 * Pass: CHECK_INITIALIZE_VLA_WITH_PRECONDITIONS
 * Debug mode: INITIALIZE_VLA_DEBUG_LEVEL
 * Properties used:
 *   - ERROR_ON_UNINITIALIZE_VLA
 *   (- SEMANTICS_ANALYZE_CONSTANT_PATH)
 * Resource needed:
 *   - preconditions
 *
 * Pass: CHECK_INITIALIZE_VLA_WITH_EFFECTS (not implemented yet)
 * Debug mode: INITIALIZE_VLA_DEBUG_LEVEL
 * Properties used:
 *   - ERROR_ON_UNINITIALIZE_VLA
 *   (- SEMANTICS_ANALYZE_CONSTANT_PATH)
 * Resource needed:
 *   - CUMULATED_EFFECTS/OUT_EFFECTS
 *
 * Pass: CHECK_INITIALIZE_VLA_WITH_REGIONS (not implemented yet)
 * Debug mode: INITIALIZE_VLA_DEBUG_LEVEL
 * Properties used:
 *   - ERROR_ON_UNINITIALIZE_VLA
 *   (- SEMANTICS_ANALYZE_CONSTANT_PATH)
 * Resource needed:
 *   - REGIONS/OUT_REGIONS
 *
 *
 * Pass: INITIALIZE_VLA_WITH_PRECONDITIONS
 * Debug mode: INITIALIZE_VLA_DEBUG_LEVEL
 * Properties used:
 *   - INITIALIZE_VLA_VALUE
 *   (- SEMANTICS_ANALYZE_CONSTANT_PATH)
 * Resource needed:
 *   - preconditions
 *
 * Pass: INITIALIZE_VLA_WITH_EFFECTS (not implemented yet)
 * Debug mode: INITIALIZE_VLA_DEBUG_LEVEL
 * Properties used:
 *   - INITIALIZE_VLA_VALUE
 *   (- SEMANTICS_ANALYZE_CONSTANT_PATH)
 * Resource needed:
 *   - CUMULATED_EFFECTS/OUT_EFFECTS
 *
 * Pass: INITIALIZE_VLA_WITH_REGIONS (not implemented yet)
 * Debug mode: INITIALIZE_VLA_DEBUG_LEVEL
 * Properties used:
 *   - INITIALIZE_VLA_VALUE
 *   (- SEMANTICS_ANALYZE_CONSTANT_PATH)
 * Resource needed:
 *   - REGIONS/OUT_REGIONS
 */

#include <stdlib.h>
#include <stdio.h>

#include "genC.h"
#include "linear.h"

#include "misc.h"
#include "pipsdbm.h"
#include "properties.h"

#include "ri.h"
#include "ri-util.h"
#include "prettyprint.h" // for debugging

#include "semantics.h" // used
#include "transformer.h" // print_any_transformer

/******************************************************
 * CHECK : BEGIN                                      *
 ******************************************************/

/**
 * error_on_uninitialize_p/warning_on_uninitialize_p correspond to property ERROR_ON_UNINITIALIZE_VLA (for check pass)
 * if error_on_uninitialize_p==true, generate error when find uninitialize_vla
 * if warning_on_uninitialize_p==true, generate warning when find uninitialize_vla
 * semantics_analyze_constant_path_p correspond to property SEMANTICS_ANALYZE_CONSTANT_PATH
 * uninitialize_vla_p is false by default, if we find uninitialize_vla it becomes true
 *                  it's redundant with to_initialize == NIL or != NIL
 * to_initialize, list or reference that need an initialization
 * init_value initial value that we want for to_initialize references.
 * init_value correspond to property INITIALIZE_VLA_VALUE
 */
typedef struct ctx_initvla {
  bool error_on_uninitialize_p;
  bool warning_on_uninitialize_p;
  bool semantics_analyze_constant_path_p;
  //bool uninitialize_vla_p; // redundant with to_initialize

  // don't forget to free ref in to_initialize
  list /*reference*/ to_initialize;
  entity init_value;
} ctx_initvla_t;


/**
 * /param ctx context that notably keep the variable to initialize
 * /param dep_ref reference of the variable length that need to be initialize
 * /param decl the intialization of vla that make problem
 * /param message to print a custom warning/error message
 * /param need_initialize_p, if the vla use a negative variable length value, the variable in himself don't be to be initialize
 *                  but we can still want the warning/error to prevent of a wrong intialization
 */
static void add_dependence_reference(ctx_initvla_t *ctx, reference dep_ref, entity decl, string message, bool need_initialize_p) {
  //ctx->uninitialize_vla_p = true;
  if (need_initialize_p) {
    if (gen_chunk_undefined_p(gen_find(dep_ref, ctx->to_initialize, (gen_filter2_func_t) reference_equal_p, gen_chunk_identity))) {
      pips_debug(2, "variable %s is added to the list of variable to initialize.\n", reference_to_string(dep_ref));
      ctx->to_initialize = CONS(REFERENCE, dep_ref, ctx->to_initialize);
    }
    else
      free_reference(dep_ref);
  }
  else
    free_reference(dep_ref);

  if (ctx->warning_on_uninitialize_p) {
    pips_user_warning("%s declaration of %s depend of %s\n",
        message, entity_user_name(decl), reference_to_string(dep_ref));
  }
  if (ctx->error_on_uninitialize_p) {
    pips_user_error("%s declaration of %s depend of %s\n",
        message, entity_user_name(decl), reference_to_string(dep_ref));
  }
}

/**
 * search uninitialized variable length in vla declaration
 */
static void statement_check_initialize_vla_with_preconditions(statement s, ctx_initvla_t *ctx) {
  // only declaration is interesting
  if (declaration_statement_p(s)) {
    ifdebug(2) {
      pips_debug(2, "declaration statement to analyze:\n");
      print_statement(s);
    }

    list ldecl = statement_declarations(s);

    transformer prec = load_statement_precondition(s);
    //list precarg = transformer_arguments(prec);
    Psysteme precsc = predicate_system(transformer_relation(prec));

    FOREACH(ENTITY, decl, ldecl) {
      type t = entity_type(decl);
      // no need to test if the entity is a variable (entity_variable_p)
      //   or has dependent type (dependent_type_p)
      //   because dependence_of_dependent_type also do it.
      list /*reference*/ ldep = dependence_of_dependent_type(t); // list of vla declaration

      ifdebug(2) {
        pips_debug(2, "list of dependence for entity %s: ", entity_name(decl));
        print_references(ldep);
      }

      // foreach variable length (of vla declaration) check if it is initialize
      FOREACH(REFERENCE, dep_ref, ldep) {
        entity dep_var = reference_variable(dep_ref);
        list dep_arg = reference_indices(dep_ref);
        entity dep_ent = entity_undefined;

        // in case of int a[b[0]];
        // b[0] need to be convert as an entity SEMANTICS_ANALYZE_CONSTANT_PATH?
        // as in precondition?
        if (!ENDP(dep_arg)) {
          //reference indices isn't NIL
          if (ctx->semantics_analyze_constant_path_p) {
            //convert reference to entity like precondition does it?
            pips_internal_error("management of semantics_analyze_constant_path, not implemented yet.\n");
            dep_ent = dep_var;
          }
          else {
            // variable present in precondition system are only compose of entity and not reference
            add_dependence_reference(ctx, dep_ref, decl,
                "Detection of a dependence with an array that can't be analyze.\n"
                "Try to set SEMANTICS_ANALYZE_CONSTANT_PATH at true.\n",
                true);
          }
        }
        else {
          //reference indices is NIL
          dep_ent = dep_var;
        }

        // we know the entity variable length (dep_ent) to check the initialization and the value.
        if (!entity_undefined_p(dep_ent)) {
          long long int min, max;
          if (sc_minmax_of_variable(sc_copy(precsc), dep_ent, &min, &max)) {
            if (max == VALUE_MAX && min == VALUE_MIN) {
              // dep_ent is uninitialized
              string mess;
              asprintf(&mess, "%s can be uninitialized when", entity_user_name(dep_ent));
              add_dependence_reference(ctx, dep_ref, decl, mess, true);
            }
            else if (min < 0) {
              // dep_ent is negative
              string mess;
              asprintf(&mess, "wrong declaration of array %s with %s<0\n", entity_user_name(decl), entity_user_name(dep_ent));
              add_dependence_reference(ctx, dep_ref, decl, mess, false);
            }
            else {
              //no memory leak, in the other case, it's add_dependence_reference which manage free or not dep_ref
              free_reference(dep_ref);
            }
          }
          else {
            pips_user_error("This case must never happen.\n It mean the precondition system is unconsistent?\n");
            //string mess;
            //asprintf(&mess, "%s can be uninitialize when", entity_user_name(dep_ent));
            //add_dependence_reference(ctx, dep_ref, decl, mess, true);
          }
        }
      }

      gen_free_list(ldep);
      ldep=NIL;
    }
  }
}

/**
 * static function due to ctx_initvla_t argument
 */
static bool check_initialize_vla_with_preconditions_on_statement(statement module_statement, ctx_initvla_t * ctx) {
  gen_context_recurse(module_statement, ctx,
      statement_domain, gen_true2, statement_check_initialize_vla_with_preconditions);

  return true;
}

static bool check_initialize_vla_generic(const char* module_name, bool with_preconditions_p, bool with_efects_p, bool with_regions_p) {
  //entity module;
  statement module_statement;
  bool good_result_p = false;

  pips_assert("with_preconditions_p or with_efects_p or with_regions_p must be true.\n",
      with_preconditions_p || with_efects_p || with_regions_p);

  debug_on("INITIALIZE_VLA_DEBUG_LEVEL");
  pips_debug(1, "begin\n");

  //-- configure environment --//
  set_current_module_entity(module_name_to_entity(module_name));
  //module = get_current_module_entity();

  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, module_name, true) );
  module_statement = get_current_module_statement();

  pips_assert("Statement should be OK before...",
      statement_consistent_p(module_statement));


  //-- get dependencies --//
  if (with_preconditions_p) {
    set_precondition_map( (statement_mapping)
        db_get_memory_resource(DBR_PRECONDITIONS, module_name, true) );
  }
//  if (with_regions_p) {
//    set_cumulated_rw_effects( (statement_effects)
//        db_get_memory_resource(DBR_XXX, module_name, true) );
//  }
//  else if (with_efects_p) {
//    set_cumulated_rw_effects((statement_effects)
//        db_get_memory_resource(DBR_XXX, module_name, true));
//  }


  //-- Init Context --//
  ctx_initvla_t ctx;
  //ctx.uninitialize_vla_p = false;
  ctx.to_initialize = NIL;
  ctx.warning_on_uninitialize_p = !get_bool_property("ERROR_ON_UNINITIALIZE_VLA");
  ctx.error_on_uninitialize_p = get_bool_property("ERROR_ON_UNINITIALIZE_VLA");
  ctx.semantics_analyze_constant_path_p = get_bool_property("SEMANTICS_ANALYZE_CONSTANT_PATH");
  //ctx.init_value = get_int_property("INITIALIZE_VLA_VALUE"); //not use for the check


  //-- Make the job -- //
  if (with_preconditions_p) {
    good_result_p = check_initialize_vla_with_preconditions_on_statement(module_statement, &ctx);
  }


  //-- Save modified code to database --//
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, strdup(module_name), module_statement);

  reset_current_module_statement();
  reset_current_module_entity();
  if (with_preconditions_p) {
    reset_precondition_map();
  }
//  if (with_efects_p || with_regions_p) {
//    reset_cumulated_rw_effects();
//  }

  pips_debug(1, "end\n");
  debug_off();

  return (good_result_p);
}

/**
 * PIPS pass
 */
bool check_initialize_vla_with_preconditions(const string module_name) {
  return check_initialize_vla_generic(module_name, true, false, false);
}

/**
 * PIPS pass
 */
bool check_initialize_vla_with_effects(const string module_name) {
  pips_internal_error("check_initialize_vla_with_effects(%s) "
                      "Not implemented yet.\n", module_name);
  return false;
//  return check_initialize_vla_generic(module_name, false, true, false);
}

/**
 * PIPS pass
 */
bool check_initialize_vla_with_regions(const string module_name) {
  pips_internal_error("check_initialize_vla_with_regions(%s) "
                      "Not implemented yet.\n", module_name);
  return false;
//  return check_initialize_vla_generic(module_name, false, false, true);
}

/******************************************************
 * CHECK : END                                        *
 ******************************************************/

//static bool statement_initialize_vla(statement s, ctx_initvla_t *ctx) {
//  // only declaration is interesting
//  if (declaration_statement_p(s)) {
//    ifdebug(5) {
//      pips_debug(5, "declaration statement to analyze:\n");
//      print_statement(s);
//    }
//
//    list ldecl = statement_declarations(s);
//
//    FOREACH(REFERENCE, ref, ctx->to_initialize) {
//      if (!gen_chunk_undefined_p(gen_find_eq(reference_variable(ref), ldecl))) {
//
//      }
//    }
//    FOREACH(ENTITY, decl, ldecl) {
//      if (!gen_chunk_undefined_p(gen_find(decl, ctx->to_initialize, gen_eq, reference_variable))) {
//
//      }
//    }
//
//    //No more variable length to initialize
//    if (ENDP(ctx->to_initialize)) {
//      pips_debug(5, "No more variable to initialize.\n");
//      gen_recurse_stop();
//    }
//  }
//  return true;
//}

/**
 * static function due to ctx_initvla_t argument
 * add an initial value for scalar variables in variable in ctx->to_initialize
 * add an affectation statement for cell array variable in ctx->to_initialize
 */
static bool initialize_vla_on_statement(statement module_statement __attribute__((unused)), ctx_initvla_t * ctx) {
  pips_debug(1, "begin\n");
  entity init_value = ctx->init_value;
  list l = gen_copy_seq(ctx->to_initialize);

  // treat scalar variables
  FOREACH(REFERENCE, ref, l) {
    entity var = reference_variable(ref);
    list ind = reference_indices(ref);
    if (ENDP(ind)) {
      value val = entity_initial(var);
      if (value_unknown_p(val)) {
        entity_initial(var) = make_value_expression(entity_to_expression(init_value));
        free_value(val);
        gen_remove(&(ctx->to_initialize), ref);
        free_reference(ref);
      }
      else {
        pips_internal_error("This case never happen.\n");
      }
    }
  }
  gen_free_list(l);

  // treat array variables
  if (!ENDP(ctx->to_initialize)) {
    // add affectation statement for cell array just after the declaration of the array
    // (the cell array to set is a length for the declaration of a vla)
    //  gen_context_recurse(module_statement, ctx,
    //      statement_domain, statement_initialize_vla, gen_null);
  }

  // still some variable uninitialized? as pointer?
  if (!ENDP(ctx->to_initialize)) {
    pips_user_warning("Some variables length are still uninitialized:\n");
    FOREACH(REFERENCE, ref, ctx->to_initialize) {
      pips_user_warning("%s is uninitialized.\n", reference_to_string(ref));
    }
  }
  pips_debug(1, "end\n");
  return true;
}

static bool initialize_vla_generic(const char* module_name, bool with_preconditions_p, bool with_efects_p, bool with_regions_p) {
  //entity module;
  statement module_statement;
  bool good_result_p = false;

  pips_assert("with_preconditions_p or with_efects_p or with_regions_p must be true.\n",
      with_preconditions_p || with_efects_p || with_regions_p);

  debug_on("INITIALIZE_VLA_DEBUG_LEVEL");
  pips_debug(1, "begin\n");

  //-- configure environment --//
  set_current_module_entity(module_name_to_entity(module_name));
  //module = get_current_module_entity();

  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, module_name, true) );
  module_statement = get_current_module_statement();

  pips_assert("Statement should be OK before...",
      statement_consistent_p(module_statement));

  set_ordering_to_statement(module_statement);


  //-- get dependencies --//
  if (with_preconditions_p) {
    set_precondition_map( (statement_mapping)
        db_get_memory_resource(DBR_PRECONDITIONS, module_name, true) );
  }
//  if (with_regions_p) {
//    set_cumulated_rw_effects( (statement_effects)
//        db_get_memory_resource(DBR_XXX, module_name, true) );
//  }
//  else if (with_efects_p) {
//    set_cumulated_rw_effects((statement_effects)
//        db_get_memory_resource(DBR_XXX, module_name, true));
//  }


  //-- Init Context --//
  ctx_initvla_t ctx;
  //ctx.uninitialize_vla_p = false;
  ctx.to_initialize = NIL;
  ctx.warning_on_uninitialize_p = false;                    //don't want warning or error
  ctx.error_on_uninitialize_p = false;                      //don't want warning or error
  ctx.semantics_analyze_constant_path_p = get_bool_property("SEMANTICS_ANALYZE_CONSTANT_PATH");
  int init_val = get_int_property("INITIALIZE_VLA_VALUE");
  ctx.init_value = make_integer_constant_entity(init_val);
  //ctx.init_value = int_to_entity(init_val);


  //-- Make the job -- //
  // search the uninitialized variable length of vla
  if (with_preconditions_p) {
    check_initialize_vla_with_preconditions_on_statement(module_statement, &ctx);
  }

  // make the initialization (if there is something to initialize)
  if (ctx.to_initialize != NIL) {
    good_result_p = initialize_vla_on_statement(module_statement, &ctx);
  }


  pips_assert("Statement should be OK after...",
      statement_consistent_p(module_statement));


  //-- Save modified code to database --//
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, strdup(module_name), module_statement);

  reset_ordering_to_statement();
  reset_current_module_statement();
  reset_current_module_entity();
  if (with_preconditions_p) {
    reset_precondition_map();
  }
//  if (with_efects_p || with_regions_p) {
//    reset_cumulated_rw_effects();
//  }

  pips_debug(1, "end\n");
  debug_off();

  return (good_result_p);
}

/**
 * PIPS pass
 */
bool initialize_vla_with_preconditions(const char* module_name) {
  return initialize_vla_generic(module_name, true, false, false);
}

/**
 * PIPS pass
 */
bool initialize_vla_with_effects(const char* module_name) {
  pips_internal_error("initialize_vla_with_effects(%s) "
                      "Not implemented yet.\n", module_name);
  return false;
//  return initialize_vla_generic(module_name, false, true, false);
}

/**
 * PIPS pass
 */
bool initialize_vla_with_regions(const char* module_name) {
  pips_internal_error("initialize_vla_with_regions(%s)"
                      " Not implemented yet.\n", module_name);
  return false;
//  return initialize_vla_generic(module_name, false, false, true);
}

#endif // BUILDER_*INITIALIZE_VLA_WITH*
