/*

  $Id$

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
#ifdef HAVE_CONFIG_H
    #include "pips_config.h"
#endif

/**
 * Pass: VARIABLE_REPLICATION
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
#include "pipsdbm.h"

#include "control.h"

#include "misc.h"

#include "properties.h"

#include "task_parallelization.h"
#include "prettyprint.h"
static string variable_replication_declaration_commenter(__attribute__((unused)) entity e) {
  return strdup(COMMENT_VARIABLE_REPLICATION);
}

static void replicate_declaration(entity decl, statement module_statement, statement st) {
  ifdebug(4) {
    pips_debug(4, "begin\n");
    pips_debug(4, "declaration statement to replicated\n");
    print_statement(st);
  }
  const char * prefix = get_string_property((const char *) MPI_GENERATION_PREFIX);
  int nbr_copy = get_int_property(MPI_GENERATION_NBR_CLUSTER);
  statement declaration=statement_undefined;

  push_generated_variable_commenter(variable_replication_declaration_commenter);
  for (int i=0; i<nbr_copy; i++) {
    string new_name = "";
    entity new_entity = entity_undefined;
    new_name = concatenate(
        entity_module_name(decl), MODULE_SEP_STRING,
        local_name_to_scope(entity_local_name(decl)),
        prefix, entity_user_name(decl), "_", i2a(i),
        NULL);

    if (gen_find_tabulated(new_name, entity_domain) != entity_undefined) {
      pips_user_error("The entity %s already exist\n", new_name);
      return;
    }
    new_entity = make_entity_copy_with_new_name(decl, new_name, true);

    declaration = add_declaration_statement_here(module_statement, st, new_entity, true);

    //statement_declarations(module_statement) = CONS(ENTITY, new_entity, statement_declarations(module_statement));
  }
  pop_generated_variable_commenter();

  pips_assert("module_statement is consistent\n", statement_consistent_p(module_statement));
  ifdebug(4) {
    pips_debug(4, "declaration statement that be added\n");
    print_statement(declaration);
    print_statement(st);
    pips_debug(4, "end\n");
  }
}

/**
 *
 */
static bool make_global_variable_declaration_replication() {
  pips_user_warning("global variable not implemented yet.\n");
  return true;
}


/**
 * only replicate declaration declare at the first scope of the function.
 * The sub-scope has to be some pragma and don't have to be replicate.
 * \pragma module_statement statement to work on
 */
static bool make_declaration_replication(statement module_statement) {
  if (!statement_sequence_p(module_statement)) {
    pips_internal_error("module_statement have to be the statement of the module/function\n");
    return false;
  }

  // FOREACH statement of the module/function,
  //   check if it's a declaration
  //     then FOREACH declaration generate new variables (depend of the number of proc) and declare them
  FOREACH(STATEMENT, st, sequence_statements(statement_sequence(module_statement))) {
    if (declaration_statement_p(st)) {
      task t = load_parallel_task_mapping(st);
      // declarations list of entity declared
      list declarations = statement_declarations(st);
      FOREACH(ENTITY, decl, declarations) {
        // test if the entity decl is not in the private list of the task, if so no replication
        if (gen_position(decl, task_private_data(t)) == 0) {
          replicate_declaration(decl, module_statement, st);
        }
      }
    }
  }

  return true;
}


/**
 * PIPS pass
 */
bool variable_replication(const char* module_name) {
  //entity module;
  statement module_statement;
  bool good_result_p = true;

  debug_on("MPI_GENERATION_DEBUG_LEVEL");
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
  set_parallel_task_mapping((statement_task)
      db_get_memory_resource(DBR_TASK, module_name, true));

  //-- Make the job -- //
  good_result_p = make_declaration_replication(module_statement);
  good_result_p &= make_global_variable_declaration_replication();

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

