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
 * Pass: TASK_MAPPING
 * Debug mode: MPI_GENERATION_DEBUG_LEVEL
 * Resource generated:
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
#include "pipsdbm.h"

#include "misc.h"

#include "properties.h"

#include "task_private.h"
#include "task_parallelization.h"
#include "prettyprint.h"
/*
 * Generate function:
 *   parallel_task_mapping_undefined_p(void)
 *   reset_parallel_task_mapping(void)
 *   error_reset_parallel_task_mapping(void)
 *   set_parallel_task_mapping(statement_task o)
 *   get_parallel_task_mapping(void)
 *   init_parallel_task_mapping(void)
 *   close_parallel_task_mapping(void)
 *   store_parallel_task_mapping(statement k, task v)
 *   update_parallel_task_mapping(statement k, task v)
 *   load_parallel_task_mapping(statement k)
 *   delete_parallel_task_mapping(statement k)
 *   bound_parallel_task_mapping_p(statement k)
 *   store_or_update_parallel_task_mapping(statement k, task v)
 */
GENERIC_GLOBAL_FUNCTION(parallel_task_mapping, statement_task)

void print_task(task t) {
  if(task_undefined_p(t))
    fprintf(stderr, "Undefined task\n");
  // For debugging with gdb, dynamic type checking
  else if(task_domain_number(t)!=task_domain)
    (void) fprintf(stderr,"Arg. \"t\"is not a task.\n");
  else {
    fprintf(stderr, "%s", task_to_string(t, false));
  }
}

string task_to_string(task t, bool pretty_print) {
  char tid[10+4];
  string tprivate = "";
  char tcluster[18+4];
  char tsync[23+5];
  snprintf(tid, 10+4, "task_id=%"_intFMT"\n", task_id(t));
  snprintf(tcluster, 18+4, "task_on_cluster=%"_intFMT"\n", task_on_cluster(t));
  snprintf(tsync, 23+5, "task_synchronization=%s\n", task_synchronization(t)?"true":"false");
  tprivate = "task_private_data={";
  FOREACH(ENTITY, ep, task_private_data(t)) {
    pips_debug(8, "%s", entity_name(ep));
    tprivate = concatenate(tprivate, pretty_print?entity_user_name(ep):entity_name(ep), "; ", (char *) NULL);
  }
  tprivate = strdup(concatenate(tprivate, "}\n", (char *) NULL));
  return concatenate(tid, tprivate, tcluster, tsync, (char *) NULL);
}


/******************************************************
 * PRAGMA MANAGEMENT : BEGIN                          *
 ******************************************************/
#define PRAGMA_DISTRIBUTED "distributed"

/**
 * ctx_pragma_t:
 * on_cluster       on which cluster the pragma may be run (=-1 if run on all cluster)
 * synchro          if the communication between cluster are synchro (true) or asynchro(false)
 *                  if on_cluster=-1 we don't care about the value of synchro
 * d_...            if it's a default value or value ask by user
 */
typedef struct ctx_pragma {
  //string begin;
  int on_cluster;
  bool d_on_cluster;
  bool synchro;
  bool d_synchro;
} ctx_pragma_t;

static void print_ctx_pragma(const ctx_pragma_t ctx) {
  fprintf(stderr, "pragma info:\n");
  fprintf(stderr, "on_cluster=%d\n", ctx.on_cluster);
  fprintf(stderr, "synchro=%s\n", ctx.synchro?"true":"false");
}

/**
 * init a ctx_pragma_t
 * by default
 * ctx.on_cluster = -1                  run on all cluster
 * ctx.synchro = true                   com synchro
 */
static ctx_pragma_t init_ctx_pragma() {
  ctx_pragma_t ctx;
  ctx.on_cluster = -1;
  ctx.d_on_cluster = true;
  ctx.synchro = true;
  ctx.d_synchro = true;
  return ctx;
}
// Not use
///**
// * create a ctx_pragma_t with the parameter
// */
//static ctx_pragma_t make_ctx_pragma(int cluster, bool synchro) {
//  ctx_pragma_t ctx;
//  ctx.on_cluster = cluster;
//  ctx.d_on_cluster = false;
//  ctx.synchro = synchro;
//  ctx.d_synchro = false;
//  return ctx;
//}

/**
 * generate a error message about the for the parameter of the pragma to use
 */
static string pragma_parameter_unknown_message(string s) {
  return concatenate("\nUnknown ", s, " parameter.\n"
                     "Allowed parameters are:\n"
                     "\ton_cluster=n with n a positive number\n"
                     "\tnowait|wait\n", NULL);
}

/**
 * Test if the pragma is a PRAGMA_DISTRIBUTED
 * check the first element f the pragma
 * \param p         pragma to check
 * \return          true if p is a PRAGMA_DISTRIBUTED
 */
static bool pragma_PRAGMA_DISTRIBUTED_p(pragma p) {
  bool r = false;
  if(pragma_string_p(p)) {
    if(strncasecmp(PRAGMA_DISTRIBUTED, pragma_string(p), strlen(PRAGMA_DISTRIBUTED)) == 0) {
      r = true;
    }
  }
  else if(pragma_expression_p(p)) {
    list expr = pragma_expression(p);
    // The list is reversed !
    expression begin = EXPRESSION(CAR(gen_last(expr)));
    if(expression_call_p(begin)) {
      entity called = call_function(expression_call(begin));
      if(strncasecmp(PRAGMA_DISTRIBUTED, entity_local_name(called), strlen(PRAGMA_DISTRIBUTED)) == 0) {
        r = true;
      }
    }
  }
  else {
    pips_internal_error("We don't know how to handle this kind of pragma !\n");
  }
  return r;
}

/**
 * parse the pragma to generate a ctx_pragma_t
 * need to checked that the pragma sended is a PRAGMA_DISTRIBUTED before
 * \param p         pragma to be parsed
 * \return          a ctx_pragma_t with the value of the pragma
 */
static ctx_pragma_t pragma_parse_PRAGMA_DISTRIBUTED(pragma p) {
  ctx_pragma_t ctx = init_ctx_pragma();
  pips_debug(6, "begin\n parse pragma %p\n", p);

  if(pragma_string_p(p)) {
    list lst = strsplit(pragma_string(p), " ");
    //start at the second parameter so CDR(lst)
    FOREACH(STRING, str, CDR(lst)) {
      if(strncasecmp(str, "on_cluster=", 11) == 0) {
        list cluster = strsplit(str, "=");
        if (gen_length(cluster) == 2) {
          string cluster_number = STRING(gen_nth(1, cluster));
          //TODO a better function than atoi may be use, atoi doesn't manage error, strtol too much work is need, remake a custom function?
          ctx.on_cluster = atoi(cluster_number);
          ctx.d_on_cluster = false;
        } else {
          pips_user_warning("unexpected value for parameter on_cluster: %s\n", str);
        }
      }
      else if(strncasecmp(str, "nowait", 7) == 0) {
        ctx.synchro = false;
        ctx.d_synchro = false;
      }
      else if(strncasecmp(str, "wait", 5) == 0) {
        ctx.synchro = true;
        ctx.d_synchro = false;
      }
      else {
        pips_user_warning("%s", pragma_parameter_unknown_message(str));
      }
    }
  }
  //This case normally never appear.
  else if(pragma_expression_p(p)) {
    pips_user_warning("Parse pragma expressions for pragma %s not implemented. This case normally never appear.\n", PRAGMA_DISTRIBUTED);
  }
  else {
    pips_internal_error("We don't know how to handle this kind of pragma !\n");
  }

  pips_debug(6, "end\n");
  return ctx;
}

/**
 * Merge value of 2 ctx_pragma_t,
 * the 2 ctx_pragma_t can't conflict on value
 * \param ctx1      ctx_pragma_t to merge
 * \param ctx2      ctx_pragma_t to merge
 * \return          a new ctx_pragma_t with value of ctx1 and ctx2
 */
static ctx_pragma_t ctx_pragma_merge(ctx_pragma_t ctx1, ctx_pragma_t ctx2) {
  ctx_pragma_t ctx = init_ctx_pragma();

  if (!ctx1.d_on_cluster) {
    ctx.d_on_cluster = false;
    ctx.on_cluster = ctx1.on_cluster;
    if (!(!ctx2.d_on_cluster && ctx1.on_cluster==ctx2.on_cluster)) {
      pips_user_error("conflict between value ask by the user in pragma about on_cluster %d and %d\n", ctx1.on_cluster, ctx2.on_cluster);
    }
  } else if (!ctx2.d_on_cluster) {
    ctx.d_on_cluster = false;
    ctx.on_cluster = ctx2.on_cluster;
  }

  if (!ctx1.d_synchro) {
    ctx.d_synchro = false;
    ctx.synchro = ctx1.synchro;
    if (!(!ctx2.d_synchro && ctx1.synchro==ctx2.synchro)) {
      pips_user_error("conflict between value ask by the user in pragma about synchro(wait/nowait) %d and %d\n", ctx1.synchro, ctx2.synchro);
    }
  } else if (!ctx2.d_synchro) {
    ctx.d_synchro = false;
    ctx.synchro = ctx2.synchro;
  }

  return ctx;
}

//static bool print_pragma(statement s) {
//  print_statement(s);
//  pips_debug(0, "have pragma:\n");
//  if (statement_with_pragma_p(s)) {
//    list lpragmas = statement_pragmas(s);
//    FOREACH(PRAGMA, p, lpragmas) {
//      if (pragma_string_p(p)) {
//        pips_debug(0, "pragma is a string = \n  %s\n", pragma_string(p));
//      }
//      else if (pragma_expression_p(p)) {
//        pips_debug(0, "pragma is a expressions = \n");
//        print_expressions(pragma_expression(p));
//      }
//      else if (pragma_undefined_p(p)) {
//        pips_debug(0, "pragma is undefined !!!!!!!!!\n");
//      }
//      else {
//        pips_debug(0, "pragma NEVER OCCUR !!!!!!!!!\n");
//      }
//    }
//  }
//  return true;
//}
/******************************************************
 * PRAGMA MANAGEMENT : END                            *
 ******************************************************/

/**
 * ctx_task_t:
 * pragma           information from the pragma
 * task_id          id of the task
 * private          list of entity, private variables for the task
 */
typedef struct ctx_task {
  ctx_pragma_t pragma;
  int task_id;
  list private;
} ctx_task_t;

static void print_ctx_task(const ctx_task_t ctx) {
  print_ctx_pragma(ctx.pragma);
  fprintf(stderr, "task_id=%d\n", ctx.task_id);
  fprintf(stderr, "private list entities:\n");
  FOREACH(ENTITY, e, ctx.private) {
    print_entity_variable(e);
    fprintf(stderr, "\n");
  }
}

/**
 * compute what it must be add in the private entity list
 * essentially internal declaration of the statement
 * \param st        statement to check
 * \param ctx       context where private list is store and update
 */
static void compute_private_entity_list(statement st, ctx_task_t *ctx) {
  if (declaration_statement_p(st)) {
    // declarations list of entity declared
    list declarations = statement_declarations(st);
    ctx->private = gen_nconc(ctx->private, gen_copy_seq(declarations));
  }
}

/**
 * assign a task for the statement st
 * \param st        statement to be assigned
 * \param ctx       context where information about the task are store
 */
static void assign_statement_task_mapping(statement st, ctx_task_t *ctx) {
  task t;
  if (ctx->pragma.on_cluster == -1)
    t = make_task(ctx->task_id, NIL, ctx->pragma.on_cluster, ctx->pragma.synchro);
  else
    t = make_task(ctx->task_id,  gen_copy_seq(ctx->private), ctx->pragma.on_cluster, ctx->pragma.synchro);
  store_or_update_parallel_task_mapping(st, t);
  ifdebug(4) {
    pips_debug(4, "associate statement %p to task %p\n", st, load_parallel_task_mapping(st));
    pips_debug(4, "statement:\n");
    print_statement(st);
    pips_debug(4, "task:\n");
    print_task(load_parallel_task_mapping(st));
  }
}

/**
 * compute the task mapping requires the module statement as param
 * only parse pragma on fisrt level statement of the module
 *   then recurse on all sub-statement to assign the task
 * \param module_statement              module statement to work on
 */
static bool make_task_mapping (__attribute__((unused)) entity module, statement module_statement) {
  if (!statement_sequence_p(module_statement)) {
    pips_internal_error("module_statement have to be the statement of the module/function\n");
    return false;
  }

  int task_number = 0;
  // FOREACH statement of the module/function,
  FOREACH(STATEMENT, st, sequence_statements(statement_sequence(module_statement))) {
    //init a a pragma context (execution on all cluster
    ctx_pragma_t ctxp = init_ctx_pragma();
    //check if statement st have a pragma, if true modify pragma context in consequences
    if (statement_with_pragma_p(st)) {
      list lpragmas = statement_pragmas(st);
      FOREACH(PRAGMA, p, lpragmas) {
        if (pragma_PRAGMA_DISTRIBUTED_p(p)) {
          ctx_pragma_t ctxp_temp = pragma_parse_PRAGMA_DISTRIBUTED(p);
          ctxp = ctx_pragma_merge(ctxp, ctxp_temp);
        }
      }
    }

    //init the task context
    ctx_task_t ctx;
    ctx.task_id = task_number;
    ctx.pragma = ctxp;
    ctx.private = NIL;

    ifdebug(2) {
      pips_debug(2, "work on statement:\n");
      print_statement(st);
      print_ctx_task(ctx);
    }

    //make the job
    //first compute_private_entity_list to recursively add private entity
    //second assign_statement_task_mapping to assign a task to each statement
    //can't make the 2 gen_curse into 1 because I want the full private list variable before the assignment of task to statement
    gen_context_recurse(st, &ctx, statement_domain, gen_true2, compute_private_entity_list);
    gen_context_recurse(st, &ctx, statement_domain, gen_true2, assign_statement_task_mapping);

    task_number++;
  }

  // only present in case of gen_recurse with module_statement to not have seg fault
  // But normally will never be useful
  ctx_task_t ctx;
  ctx.task_id = -1;
  ctx.pragma = init_ctx_pragma();
  ctx.private = NIL;
  //no need
  //compute_private_entity_list(module_statement, &ctx);
  assign_statement_task_mapping(module_statement, &ctx);

  return true;
}

/**
 * PIPS pass
 */
bool task_mapping(const char* module_name) {
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

  init_parallel_task_mapping();

  //-- get dependencies --//
  // nothing except code and entity done before.

  //TODO look to add parameter in private list?
  //     look module is type functionnal -> list parameter convert to list entitty

  //-- Make the job -- //
  make_task_mapping(module, module_statement);
  //  gen_recurse(module_statement, statement_domain, gen_true, print_pragma);

  //useless, normally we don't modify the code
  //pips_assert("Statement should be OK after...",
  //    statement_consistent_p(module_statement));

  //-- Save modified code to database --//
  //  DB_PUT_MEMORY_RESOURCE(DBR_CODE, strdup(module_name), module_statement);
  DB_PUT_MEMORY_RESOURCE(DBR_TASK, module_name, get_parallel_task_mapping());
  //  DB_PUT_MEMORY_RESOURCE(DBR_CALLEES, module_name,
  //       compute_callees(module_statement));

  reset_current_module_statement();
  reset_current_module_entity();
  reset_parallel_task_mapping();

  pips_debug(1, "end\n");
  debug_off();

  return (good_result_p);
}

