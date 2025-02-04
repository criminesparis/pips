/*

  $Id$

  Copyright 1989-2017 MINES ParisTech

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


/**
 * Pass: ELIMINATE_ORIGINAL_VARIABLES
 * Debug mode: MPI_GENERATION_DEBUG_LEVEL
 * Properties used:
 *   - MPI_NBR_CLUSTER
 *   - MPI_DUPLICATE_VARIABLE_PREFIX
 * Resource needed:
 *   - DBR_TASK
 *
 */

#include <stdlib.h>
#include <stdio.h>

#include "genC.h"
#include "linear.h"

#include "resources.h"
#include "database.h"
#include "ri.h"
#include "ri-util.h"
#include "effects.h"
#include "effects-util.h"
#include "pipsdbm.h"

#include "effects-generic.h"
#include "effects-simple.h"
#include "control.h"

#include "misc.h"

#include "properties.h"

#include "text-util.h"

#include "task_parallelization.h"
#include "prettyprint.h"
static int compteur_stack_task = 0;

/*******************************************************
 * CONTEXT MANAGEMENT : BEGIN                          *
 *******************************************************/

/**
 * ctx_eov:
 *   - stack_task
 *       stack_task is a stack of task
 *       each time we enter a statement,
 *         we add task corresponding to the statement into stack_task
 *       each time we leave a statement,
 *         we remove task corresponding to this statement (the last task added)
 *       we could access to the current task with function eov_current_task
 *   - hash_entity_to_eliminate
 *       hash_entity_to_eliminate is a hash table
 *         with key an variable entity, that we will have to eliminate/replace
 *         with value an array of entity that correspond to the entity that will replace the key
 *           the array size correspond to the number of cluster asked by the user
 *           (see property with #define MPI_GENERATION_NBR_CLUSTER)
 *       structure of hash_entity_to_eliminate
 *         entity_var_key0 -> 0 -> entity_new_var0_0
 *                            1 -> entity_new_var0_1
 *                            2 -> entity_new_var0_2
 *                            3 -> entity_new_var0_3
 *                            ...
 *         entity_var_key1 -> 0 -> entity_new_var1_0
 *                            1 -> entity_new_var1_1
 *                            2 -> entity_new_var1_2
 *                            3 -> entity_new_var1_3
 *                            ...
 *         ...
 *   - nbr_cluster
 *       nbr_cluster is the number of cluster
 *       it must be different than 0
 *       it's stocked in ctx to not always have to get it from properties
 *   - prefix_new_entity
 *       prefix_new_entity is a string corresponding to the prefix of the new entity
 *       it's stocked in ctx to not always have to get it from properties
 */
typedef struct ctx_eov {
  stack stack_task;
  task current_task;
  hash_table hash_entity_to_eliminate;
  int nbr_cluster;
  int current_cluster;
  string prefix_new_entity;
} ctx_eov_t;

static void print_ctx(const ctx_eov_t ctx) {
  fprintf(stderr, "current_task:\n");
  print_task(ctx.current_task);
  fprintf(stderr, "entities to eliminate:\n");
  HASH_FOREACH(entity, e, gen_array_t, a, ctx.hash_entity_to_eliminate) {
    print_entity_variable(e);
    fprintf(stderr, "\n");
  }
  fprintf(stderr, "nbr_cluster=%d", ctx.nbr_cluster);
  fprintf(stderr, "current_cluster=%d", ctx.current_cluster);
}

static ctx_eov_t eov_make_ctx(int nbr_cluster, string prefix_new_entity) {
  pips_assert("number of cluster can't be equal to 0", nbr_cluster != 0);
  ctx_eov_t ctx;
  ctx.stack_task = stack_make(task_domain, 0, 0);
  ctx.current_task = task_undefined;
  ctx.hash_entity_to_eliminate = hash_table_make(hash_pointer, 10);
  ctx.nbr_cluster = nbr_cluster;
  ctx.current_cluster = -2;
  ctx.prefix_new_entity = prefix_new_entity;
  return ctx;
}
static void eov_free_ctx(ctx_eov_t * ctx) {
  pips_assert("stack of task not empty", stack_size(ctx->stack_task) == 0);
//  pips_assert("current_task have to be undefined", ctx->current_task == task_undefined);
  HASH_FOREACH(entity, e, gen_array_t, a, ctx->hash_entity_to_eliminate) {
    gen_array_free(a);
  }
  hash_table_free(ctx->hash_entity_to_eliminate);
}

static void eov_stack_task_push_task(ctx_eov_t * ctx, task t) {
  compteur_stack_task++;
  ctx->current_task = t;
  ctx->current_cluster = task_on_cluster(t);
  stack_push((void *)t, ctx->stack_task);
}
static task eov_stack_task_pop_task(ctx_eov_t * ctx) {
  compteur_stack_task--;
  stack s = ctx->stack_task;
  task pop = (task) stack_pop(s);
  if (stack_empty_p(s)) {
    ctx->current_task = task_undefined;
    ctx->current_cluster = -2;
  }
  else {
    ctx->current_task = (task) stack_head(ctx->stack_task);
    ctx->current_cluster = task_on_cluster(ctx->current_task);
  }
  return pop;
}
//static task eov_current_task(ctx_eov_t * ctx) {
//  return ctx->current_task;
//}

static void eov_add_entity_to_eliminate(ctx_eov_t * ctx, entity e) {
  int nbr_cluster = ctx->nbr_cluster;
  string prefix = ctx->prefix_new_entity;

  gen_array_t array = gen_array_make(nbr_cluster);

  string name = "";
  entity new_entity = entity_undefined;

  for (int i=0; i<nbr_cluster; i++) {
    name = concatenate(
        entity_module_name(e), MODULE_SEP_STRING,
        local_name_to_scope(entity_local_name(e)),
        prefix, entity_user_name(e), "_", i2a(i),
        NULL);

    if ((new_entity = gen_find_tabulated(name, entity_domain)) != entity_undefined) {
      gen_array_addto(array, i, new_entity);
    }
    else {
      pips_internal_error("The variable with name %s doesn't exist.\n"
          "  PIPS can't generate the copy for this variable.\n"
          "  Try to launch pass VARIABLE_REPLICATION.\n", name);
    }
    name = "";
    new_entity = entity_undefined;
  }

  hash_put(ctx->hash_entity_to_eliminate, e, array);
}
static bool eov_entity_to_eliminate_p(ctx_eov_t * ctx, entity e) {
  return hash_defined_p(ctx->hash_entity_to_eliminate, e);
}
/**
 * call entity_to_eliminate_p before eov_get_replaced_enity
 * check on_cluster <= ctx->nbr_cluster before eov_get_replaced_enity
 */
static entity eov_get_replaced_enity(ctx_eov_t * ctx, entity e, int on_cluster) {
  //since it was only local call and I know what I do this assert was not needed
  // pips_assert("entity don't have to be eliminate", entity_to_eliminate_p(ctx, e));
  //since it was only local call and I know what I do this assert was not needed
  // pips_assert("entity asked out of bounded", on_cluster <= ctx->nbr_cluster);

  gen_array_t array = hash_get(ctx->hash_entity_to_eliminate, e);
  entity new_entity = gen_array_item(array, on_cluster);

  return new_entity;
}
static void eov_set_current_cluster(ctx_eov_t * ctx, int on_cluster) {
  ctx->current_cluster = on_cluster;
}
static int eov_get_current_cluster(ctx_eov_t * ctx) {
  return ctx->current_cluster;
}
/*******************************************************
 * CONTEXT MANAGEMENT : END                            *
 *******************************************************/


static void subtsitute_variable_in_reference (reference r, ctx_eov_t *ctx);

/*******************************************************
 * PREPARE THE CONTEXT: BEGIN                          *
 *******************************************************/
/**
 * The function in this section modify the context to know
 * - where we are
 * - on which cluster the statement is executed
 * - which variables will be replaced
 * - in which expression/loop the variable are replaced
 */

/**
 * update current_task
 * update list of entity_variable to eliminate
 * \param st        current statement
 * \param ctx       context to uppdate
 */
static bool prepare_context(statement st, ctx_eov_t *ctx) {
  ifdebug(2) {
    pips_debug(2, "prepare_context\n");
    print_statement(st);
  }
  //TODO have to do something for return statement... (on a previous pass?)
  if (statement_call_p(st) && ENTITY_C_RETURN_P(call_function(statement_call(st)))) {
    return false;
  }
  task t = load_parallel_task_mapping(st);

  // update the current task to work on
  eov_stack_task_push_task(ctx, t);
  pips_debug(4, "current_task modified:%s\n", task_to_string(t, false));

  // update the eliminated variable
  // Check if it's a declaration statement
  // if so maybe have to add entity to the list of entity to eliminate
  if (declaration_statement_p(st)) {
    // we don't have to eliminate variable on_cluster generated
    if (!comments_equal_p(statement_comments(st), COMMENT_VARIABLE_REPLICATION)) {
      FOREACH(ENTITY, var, statement_declarations(st)) {
        if (strncasecmp(entity_user_name(var), ctx->prefix_new_entity, strlen(ctx->prefix_new_entity)) != 0
            && !entity_in_list_p(var, task_private_data(t))) {
          //add entity to the list of entity to eliminate
          eov_add_entity_to_eliminate(ctx, var);
        }
      }
      ifdebug(4) {
        FOREACH(ENTITY, var, statement_declarations(st)) {
          if (strncasecmp(entity_user_name(var), ctx->prefix_new_entity, strlen(ctx->prefix_new_entity))) {
            pips_debug(5, "add entity to entity_to_eliminate:\n");
            print_entity_variable(var);
          }
        }
      }
    }
    // for variable on_cluster generated, check if it's an dynamic declaration of an array
    // and so modify the size of the array with the right new size (the old variable by the new one)
    else {
      FOREACH(ENTITY, var, statement_declarations(st)) {
        if (strncasecmp(entity_user_name(var), ctx->prefix_new_entity, strlen(ctx->prefix_new_entity)) == 0
            && !entity_in_list_p(var, task_private_data(t))) {
          //Modify type dependency declaration
          //a1[size] -> a1[size1]
          //TODO : modify type dependency
          variable vvar = type_variable(entity_type(var));
          if (variable_entity_dimension(var)>0) {
          //if (variable_dimension_number(vvar)) {
            string scurrent_cluster = strrchr(entity_user_name(var),'_');
            if (scurrent_cluster != NULL) {
              int current_cluster = atoi(scurrent_cluster+1);
              eov_set_current_cluster(ctx, current_cluster);
              gen_context_recurse(vvar, ctx, reference_domain, gen_true2, subtsitute_variable_in_reference);
            }
          }
        }
      }
    }
  }

  ifdebug(8) {
    print_ctx(*ctx);
  }
  return true;
}

static void release_context(__attribute__((unused)) statement st, ctx_eov_t *ctx) {
  pips_debug(2, "release_context\n");
  eov_stack_task_pop_task(ctx);
  ifdebug(8) {
    print_ctx(*ctx);
  }
}

/*******************************************************
 * PREPARE THE CONTEXT: END                            *
 *******************************************************/

/**
 * have to separate loop from reference because
 * index and locals of loop can also be entity variables
 * If it's needed, variable present in list of variable to eliminate,
 * substitute the variable entity present in loop l
 * by the corresponding one on the corresponding cluster.
 * \param l         loop on which the variable will be substituted
 * \param ctx       context that content the cluster in which the reference will be executed
 *                                       list on var to eliminate
 *                                       correspondence between variable and new_variable
 */
static bool loop_replace_variable(loop l, ctx_eov_t *ctx) {
  ifdebug(3) {
    pips_debug(3, "work on loop\n");
    printf_loop(l);
    ifdebug(8) {
      print_ctx(*ctx);
    }
  }
  //task t = eov_current_task(ctx);
  //int on_cluster = task_on_cluster(t);
  int on_cluster = eov_get_current_cluster(ctx);
  if (on_cluster>=ctx->nbr_cluster) {
    pips_user_error("the cluster asked is out of bounded, on_cluster=%%d", on_cluster);
    return true;
  }

  entity idx = loop_index(l);
  if (eov_entity_to_eliminate_p(ctx, idx)) {
    entity new_idx = eov_get_replaced_enity(ctx, idx, on_cluster);
    loop_index(l) = new_idx;
  }

  list new_locs = NIL;
  FOREACH(ENTITY, ent, loop_locals(l)) {
    if (eov_entity_to_eliminate_p(ctx, ent)) {
      entity new_ent = eov_get_replaced_enity(ctx, ent, on_cluster);
      new_locs = gen_nconc(new_locs, CONS(ENTITY,new_ent,NIL));
    }
    else {
      new_locs = gen_nconc(new_locs, CONS(ENTITY,ent,NIL));
    }
  }

  return true;
}

/**
 * if it's needed, variable present in list of variable to eliminate,
 * substitute the variable entity present in reference r
 * by the corresponding one on the corresponding cluster.
 * \param r         reference on which the variable will be substituted
 * \param ctx       context that content the cluster in which the reference will be executed
 *                                       list on var to eliminate
 *                                       correspondence between variable and new_variable
 */
static void subtsitute_variable_in_reference (reference r, ctx_eov_t *ctx) {
  ifdebug(3) {
    pips_debug(3, "work on reference\n");
    print_reference(r);
    ifdebug(8) {
      print_ctx(*ctx);
    }
  }
  //task t = eov_current_task(ctx);
  //int on_cluster = task_on_cluster(t);
  int on_cluster = eov_get_current_cluster(ctx);
  entity var = reference_variable(r);

  //Test if we want to substitute the variable
  if (eov_entity_to_eliminate_p(ctx, var)) {
    if (on_cluster==-1) {
      statement st = (statement)gen_get_ancestor(statement_domain, r);
      pips_user_error("statement %p in all cluster. This case may never happens.\n%s\n", st, text_to_string(statement_to_text(st)));
    }
    else if (on_cluster < ctx->nbr_cluster) {
      entity new_idx = eov_get_replaced_enity(ctx, var, on_cluster);
      reference_variable(r) = new_idx;
    }
    else {
      pips_user_error("the cluster asked is out of bounded, on_cluster=%%d", on_cluster);
    }
  }
}

/**
 * expression_substitute_variable will substitute variable entity that have to be substitute
 * In fact we can not recurse with this domain but directly recurse with reference_domain
 * It was done like this because at the beginning,
 * it was expected to use substitute_entity_in_expression
 * But a custom substitution is more efficient.
 * \return false    since we make another gen_context_recurse inside expression_substitute_variable
 *                  the filter always return false
 */
static bool expression_substitute_variable(expression e, ctx_eov_t *ctx) {
  ifdebug(3) {
    pips_debug(3, "work on expression\n");
    print_expression(e);
    ifdebug(8) {
      print_ctx(*ctx);
    }
  }

  //We don't use substitute_entity_in_expression for performance
  // to use substitute_entity_in_expression we will have to parse 2 times the expression
  // 1 time to find the entity to substitute and make some filter to not have duplicated
  // 1 time with substitute_entity_in_expression to make the substitution
  gen_context_recurse(e, ctx, reference_domain, gen_true2, subtsitute_variable_in_reference);

  return false;
}


static bool make_eliminate_original_variables(__attribute__((unused)) entity module, statement module_statement) {
  int nbr_cluster = get_int_property(MPI_GENERATION_NBR_CLUSTER);
  string prefix = (string)get_string_property(MPI_GENERATION_PREFIX);
  ctx_eov_t ctx = eov_make_ctx(nbr_cluster, prefix);

  ifdebug(1) {
    pips_debug(1, "begin\n");
    print_ctx(ctx);
  }

  // The domain was parse
  gen_context_multi_recurse(
      module_statement, &ctx,
      // to know in which task we are
      statement_domain, prepare_context, release_context,
      // do the work
      // have to distinguish loop since it can have variable entity not encapsulated inside an expression...
      loop_domain, loop_replace_variable, gen_null,
      expression_domain, expression_substitute_variable, gen_null,
      NULL);

  ifdebug(1) {
    pips_debug(1, "end\n");
    print_ctx(ctx);
  }
  eov_free_ctx(&ctx);
  return true;
}

/**
 * PIPS pass
 */
bool eliminate_original_variables(const char* module_name) {
  entity module;
  statement module_statement;
  bool good_result_p = true;

  debug_on("MPI_GENERATION_DEBUG_LEVEL");
  pips_debug(1, "begin\n");

  //-- configure environment --//
  set_current_module_entity(module_name_to_entity(module_name));
  module = get_current_module_entity();

  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, module_name, true) );
  module_statement = get_current_module_statement();

  pips_assert("Statement should be OK before...",
      statement_consistent_p(module_statement));

  set_ordering_to_statement(module_statement);

  //-- get dependencies --//
  set_parallel_task_mapping((statement_task)
      db_get_memory_resource(DBR_TASK, module_name, true));


  //-- Make the job -- //
  good_result_p = make_eliminate_original_variables(module, module_statement);
//  gen_recurse(module_statement, statement_domain, gen_true, eliminate_in_statement);


  /* Reorder the module, because some statements have been added.
     Well, the order on the remaining statements should be the same,
     but by reordering the statements, the number are consecutive. Just
     for pretty print... :-) */
  module_reorder(module_statement);

  pips_assert("Statement should be OK after...",
      statement_consistent_p(module_statement));

  //-- Save modified code to database --//
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, strdup(module_name), module_statement);

  reset_ordering_to_statement();
  reset_current_module_statement();
  reset_current_module_entity();
  reset_parallel_task_mapping();

  pips_debug(1, "end\n");
  debug_off();

  return (good_result_p);
}


