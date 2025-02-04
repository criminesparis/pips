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
 * Pass: COPY_VALUE_OF_WRITE
 * Debug mode: MPI_GENERATION_DEBUG_LEVEL
 * Properties used:
 *   - MPI_NBR_CLUSTER
 *   - MPI_DUPLICATE_VARIABLE_PREFIX
 * Resource needed:
 *   - DBR_PROPER_EFFECTS
 *   - DBR_CUMULATED_EFFECTS
 *   - DBR_TASK
 **
 * Pass: COPY_VALUE_OF_WRITE_WITH_CUMULATED_REGIONS
 * Debug mode: MPI_GENERATION_DEBUG_LEVEL
 * Properties used:
 *   - MPI_NBR_CLUSTER
 *   - MPI_DUPLICATE_VARIABLE_PREFIX
 * Resource needed:
 *   - DBR_PROPER_EFFECTS
 *   - DBR_CUMULATED_EFFECTS
 *   - DBR_LIVE_OUT_REGIONS
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
#include "effects-convex.h" //for debug prettyprint
#include "control.h"

#include "misc.h"

#include "properties.h"

#include "conversion.h"

#include "task_parallelization.h"
#include "prettyprint.h"
#include "workspace-util.h"
/**
 *
 */
static string copy_variable_declaration_commenter(__attribute__((unused)) entity e) {
  return strdup(COMMENT_COPY_VARIABLE);
}

/*******************************************************
 * UTILITIES : BEGIN                                   *
 *******************************************************/
/**
 * Maybe these function can be move in statement.c?
 */
/**
 * statement_convert_to_statement_with_sequence_of_intruction
 * transform a statement s to a statement of sequence
 * Maybe can be move to statement.C but need to add some tests in that case
 * inspired by generic_insert_statement
 * \param s         statement to convert into a sequence
 *                  modify s by side effect
 * \param extensions_on_sequence        determine where the extension have to be place
 *                                      if true, the extension is for the sequence statement
 *                                      if false, the extension is for the statement inside the sequence
 */
static void statement_convert_to_statement_with_sequence_of_intruction (statement s, bool extensions_on_sequence) {
  ifdebug(4) {
    pips_debug(4, "begin\n");
    pips_debug(4, "statement to put into a block : \n");
    print_statement(s);
  }

  // s2 will be the statement inside the sequence
  // it herite label, number, ordering, comment, declarations and instructions
  //   it doesn't have extensions or synchronization
  statement s2 = make_statement(
      statement_label(s),
      statement_number(s),
      statement_ordering(s),
      statement_comments(s),
      statement_instruction(s),
      statement_declarations(s),
      statement_decls_text(s),
      extensions_on_sequence?empty_extensions():statement_extensions(s),
      make_synchronization_none()
  );
  pips_assert("statement s2 is consistent", statement_consistent_p(s2));

  // no duplication
  // The sequence statement lost label, number, ordering, comment, declarations
  //   But keep extensions and synchronization
  statement_label(s)=entity_empty_label();
  statement_number(s)=STATEMENT_NUMBER_UNDEFINED;
  statement_ordering(s)=STATEMENT_ORDERING_UNDEFINED;
  statement_comments(s)=string_undefined;
  statement_instruction(s)=instruction_undefined;
  statement_declarations(s)=NIL;
  statement_decls_text(s)=NULL;
  if (!extensions_on_sequence)
    statement_extensions(s) = empty_extensions();
  //statement_synchronization(s) = make_synchronization_none();

  statement_instruction(s) =  make_instruction_sequence(make_sequence(CONS(STATEMENT, s2, NIL)));
  pips_assert("statement s is consistent", statement_consistent_p(s));

  /*
   * other possible version for this function
   * BUT statement s can change/isn't modify all the time by side effect
   *   so we have to return the value of a possible new statement
   *   and sometime not a new statement
   *   so not all the time homogeneous in the computation :(
   * remark: if we use this version also have to modify copy_n_reference to make a return statement
  s = make_block_with_stmt_if_not_already(s);
  if (extensions_on_sequence) {
    extensions_non_recursive_free(statement_extensions(s));
    statement_extensions(s) = statement_extensions(STATEMENT(CAR(sequence_statements(instruction_sequence(statement_instruction(s))))));
    statement_extensions(STATEMENT(CAR(sequence_statements(instruction_sequence(statement_instruction(s)))))) = empty_extensions();
  }
  pips_assert("statement s is consistent", statement_consistent_p(s));
  return s;
  */

  ifdebug(4) {
    pips_debug(4, "statement after put into a block : \n");
    print_statement(s);
    pips_debug(4, "end\n");
  }
}


/**
 * statement_with_side_effect_p
 * Check if the statement make side effect in a variable
 *   a side effect for a statement is defined by doing a read and
 *   a write on the same variable for the statement
 *
 * Maybe can be move to statement.c
 * \param s         statement to check the presence of modification by side effect
 * \return          true if the statement modify a variable by side effect
 */
static bool statement_with_side_effect_p (statement s) {
  list lceffects = load_cumulated_rw_effects_list(s);
  list lreffects = effects_read_effects(lceffects);
  list lweffects = effects_write_effects(lceffects);

  FOREACH(EFFECT, we, lweffects) {
    FOREACH(EFFECT, re, lreffects) {
      if (cells_may_conflict_p(effect_cell(we), effect_cell(re))) {
        return true;
      }
    }
  }
  return false;
}



//void sc_extract_sc_on_vars(Psysteme sc, Pbase b, Psysteme *pwith, Psysteme *pwithout) {
//  int nbvar0 = 0, nbvar = sc->dimension;
//  while (nbvar - nbvar0) {
//    sc_separate_on_vars(sc, b, pwith, pwithout);
//    nbvar0 = nbvar;
//    nbvar = (*pwith)->dimension;
//    b = (*pwith)->base;
//  }
//  ifdebug(5) {
//    printf("System WITH the variables \n");
//    sc_print(*pwith, (get_variable_name_t) pips_region_user_name);
//    printf("Nb_eq %d , Nb_ineq %d, dimension %d\n", (*pwith)->nb_eq, (*pwith)->nb_ineq, (*pwith)->dimension);
//    printf("System  WITHOUT the variables \n");
//    sc_print(*pwithout, (get_variable_name_t) pips_region_user_name);
//    printf("Nb_eq %d , Nb_ineq %d, dimension %d\n", (*pwithout)->nb_eq, (*pwithout)->nb_ineq, (*pwithout)->dimension);
//  }
//}

/*******************************************************
 * UTILITIES : END                                     *
 *******************************************************/


/**
 * translate an entity region in a variable entity if it's need
 * if ent is an entity region return a variable entity
 * else ent is already a variable entity so just return ent
 * \param ent       possible entity region
 * \return          an entity variable
 */
static entity region_entity_variable_to_new_declare_entity(entity ent, int taskid) {
  //TODO It will probably be better the have a mapping especially for the constant
  //string prefix = "__index_region_for_copy";
  string scope = strdup(concatenate("0", BLOCK_SEP_STRING, NULL));
  const char * prefix = get_string_property((const char *) MPI_GENERATION_PREFIX);
  string new_name = strdup(concatenate(scope, prefix, "_index_", entity_local_name(ent), "_", i2a(taskid), "_", NULL));

  const char * mod_name = get_current_module_name();
  if (variable_phi_p(ent)) {
    return find_or_create_scalar_entity(new_name, mod_name, is_basic_int);
  }
  if (variable_psi_p(ent)) {
    //really need?
    return find_or_create_scalar_entity(new_name, mod_name, is_basic_int);
  }
  if (variable_beta_p(ent)) {
    //really need?
    return find_or_create_scalar_entity(new_name, mod_name, is_basic_int);
  }
  if (variable_rho_p(ent)) {
    //really need?
    return find_or_create_scalar_entity(new_name, mod_name, is_basic_int);
  }
  free(new_name);
  return ent;
}

/**
 * call with gen_recurse
 * modify by side effect the variable of the reference to be sure to be a variable entity
 * and not a region entity in some cases
 * \param ref       reference to treat
 */
static void translate_reference_region(reference ref, int * taskid) {
  entity var = reference_variable(ref);
  reference_variable(ref) = region_entity_variable_to_new_declare_entity(var, *taskid);
}

/**
 * make_statement_copy_i
 * generate a copy_statement
 * with ref, generate a statement:
 * ref_i = ref;
 * \param ref       reference lhs/rhs
 * \param i         cluster number for the lhs of the statement generate
 * \return          statement: "ref_i = ref;"
 */
static statement make_statement_copy_i (reference ref, int i, int taskid) {
  statement scopy = statement_undefined;

  entity var = reference_variable(ref);
  reference rhsref = copy_reference(ref);
  gen_context_recurse(rhsref, &taskid, reference_domain, gen_true2, translate_reference_region);
  reference lhsref = reference_undefined;
  entity lhsent = entity_undefined;
  string name = "";
  const char * prefix = get_string_property((const char *) MPI_GENERATION_PREFIX);

  // name: name of the entity variable for cluster number i
  name = concatenate(
      entity_module_name(var), MODULE_SEP_STRING,
      local_name_to_scope(entity_local_name(var)),
      prefix, entity_user_name(var), "_", i2a(i),
      NULL);

  pips_debug(5, "entity name to find : %s \n", name);

  //search the entity on proc i corresponded to the entity var to copy
  if ((lhsent = gen_find_tabulated(name, entity_domain)) != entity_undefined) {
    //lhsref = make_reference(lhsent, index_copy_with_translation_of_region(reference_indices(ref)));
    lhsref = make_reference(lhsent, gen_full_copy_list(reference_indices(ref)));
    gen_context_recurse(lhsref, &taskid, reference_domain, gen_true2, translate_reference_region);
    scopy = make_assign_statement(reference_to_expression(lhsref), reference_to_expression(rhsref));
    statement_comments(scopy) = strdup("distributed send/receive");
    pips_assert("statement scopy is consistent", statement_consistent_p(scopy));
  }
  //TODO this is a workaround for global variable
  else if (true) {
    //TOP-LEVEL
    pips_user_warning("entity_module_name(var)=%s", entity_module_name(var));
    scopy = make_nop_statement();
    //scopy = make_continue_statement(entity_undefined);
  }
  else {
    pips_internal_error("The variable with name %s doesn't exist.\n"
        "  PIPS can't generate the copy for this variable.\n"
        "  Try to launch pass VARIABLE_REPLICATION.\n", name);
  }
  ifdebug(5) {
    pips_debug(5, "copy_statement generated:\n");
    print_statement(scopy);
  }
  return scopy;
}

/**
 * copy_n_statement
 * generate and add nbr statements of copy
 * with reference ref, we have the variable that has a write effect and
 * make some copy for the variables on the other proc
 * example:
 * lhs = rhs;
 * ------->
 *          lhs_0 = rhs;
 *          lhs_1 = rhs;
 *          ...
 * \param nbr       number of copy wanted (number of proc asked)
 * \param st        statement after which we make the copy/ statement which has a write effect
 */
static void copy_n_statement(list lweffects, int nbr, statement st) {
  pips_assert("statement st is consistent", statement_consistent_p(st));
  ifdebug(2) {
    pips_debug(2, "begin\n");
    pips_debug(2, "statement with : \n");
    print_statement(st);
  }

  task t = load_parallel_task_mapping(st);

  if (statement_with_side_effect_p(st)) {
    pips_user_warning("statement %s, have side effect.\n"
        "The result of the generated code can be wrong without no other pass transformation.\n"
        "Need to execute ELIMINATE_ORIGINAL_VARIABLE\n", statement_identification(st));
  }

  list lstatement = NIL;

  for (int i=0; i<nbr; i++) {
    statement sti;
    task new_task = make_task(
        task_id(t),
        task_private_data(t),
        i,
        task_synchronization(t)
        );

    sti = copy_statement(st);
    store_or_update_parallel_task_mapping(sti, new_task);
    ifdebug(3) {
      print_statement(sti);
    }

    if (//statement_with_pragma_p(sti) &&  //because of the mapping of the resource have to always doing it to update mapping of statement
        !instruction_sequence_p(statement_instruction(sti))) {
      statement_convert_to_statement_with_sequence_of_intruction(sti, false);
      pips_assert("statement sti is consistent", statement_consistent_p(sti));
      store_or_update_parallel_task_mapping(STATEMENT(CAR(sequence_statements(instruction_sequence(statement_instruction(sti))))), new_task);
    }
    statement scopy = statement_undefined;
    FOREACH(EFFECT, we, lweffects) {
      reference wref = effect_any_reference(we);
      entity went = reference_variable(wref);
      if(!effects_package_entity_p(went)
          && !ENTITY_STDERR_P(went) && !ENTITY_STDIN_P(went) && !ENTITY_STDOUT_P(went)) {
        scopy = make_statement_copy_i(wref, i, task_id(t));
        pips_assert("statement scopy is consistent", statement_consistent_p(scopy));
        store_or_update_parallel_task_mapping(scopy, new_task);

        insert_statement(sti, scopy, false);
        pips_assert("statement sti is consistent", statement_consistent_p(sti));
        scopy = statement_undefined;
      }
    }
    lstatement = CONS(STATEMENT, sti, lstatement);
  }

  if (!ENDP(lstatement)) {
    statement_label(st)=entity_empty_label();
    statement_number(st)=STATEMENT_NUMBER_UNDEFINED;
    statement_ordering(st)=STATEMENT_ORDERING_UNDEFINED;
    statement_comments(st)=string_undefined;
    statement_instruction(st)=instruction_undefined;
    statement_declarations(st)=NIL;
    statement_decls_text(st)=NULL;
    statement_extensions(st) = empty_extensions();
    //statement_synchronization(s) = make_synchronization_none();

    statement_instruction(st) =  make_instruction_sequence(make_sequence(lstatement));
  }
  else {
    pips_internal_error("Normally never appear.");
  }

  ifdebug(2) {
    pips_debug(2, "statement with : \n");
    print_statement(st);
    pips_debug(2, "end\n");
  }
}

/**
 * copy_n_reference
 * generate and add nbr statements of copy
 * with reference ref, we have the variable that has a write effect and
 * make some copy for the variables on the other proc
 * example:
 * lhs = rhs;
 * -------> lhs = rhs;
 *          lhs_0 = lhs;
 *          lhs_1 = lhs;
 *          ...
 * \param ref       reference of the variable written
 * \param nbr       number of copy wanted (number of proc asked)
 * \param st        statement after which we make the copy/ statement which has a write effect
 */
static void copy_n_reference(reference ref, int nbr, statement st) {
  pips_assert("statement st is consistent", statement_consistent_p(st));
  //entity var = reference_variable(ref);
  list indices = reference_indices(ref);
  task t = load_parallel_task_mapping(st);
  ifdebug(2) {
    pips_debug(2, "begin\n");
    pips_debug(2, "statement with : \n");
    print_statement(st);
  }

  if (indices != NIL) {
    FOREACH(EXPRESSION, index, indices) {
      if (expression_with_side_effect_p(index)) {
        /* TODO tester si side effect dans les subscripte
         * si oui renvoyer erreur
         * faire pass pour extraire side-effect des subscript si possible
         * existe déjà?
         */
        pips_user_warning("presence of side effect in subscript expression %p : %s\n"
            "Result of this pass can be false\n", index, expression_to_string(index));
      }
    }
  }

  // if the statement st have a pragma and it's not a block
  // we convert st to a block statement
  // if we don't make the convertion, the copy statement won't be affect by the pragma
  // another possible solution is to add the pragma for the copy statement
  if (//statement_with_pragma_p(st) &&  //because of the mapping of the resource have to always doing it to update mapping of statement
      !instruction_sequence_p(statement_instruction(st))) {
    statement_convert_to_statement_with_sequence_of_intruction(st, true);
    pips_assert("statement st is consistent", statement_consistent_p(st));
    store_or_update_parallel_task_mapping(STATEMENT(CAR(sequence_statements(instruction_sequence(statement_instruction(st))))), t);
  }

  statement scopy = statement_undefined;

  //Make copy for each cluster
  for (int i=0; i<nbr; i++) {
    scopy = make_statement_copy_i(ref, i, task_id(t));
    pips_assert("statement scopy is consistent", statement_consistent_p(scopy));
    store_or_update_parallel_task_mapping(scopy, t);

    insert_statement(st, scopy, false);
    pips_assert("statement st is consistent", statement_consistent_p(st));

    scopy = statement_undefined;
  }

  ifdebug(5) {
    pips_debug(5, "statement with : \n");
    print_statement(st);
    pips_debug(5, "end\n");
  }
}

/**
 * copy_write_statement
 * for the statement s, check if there is/are write effect
 * foreach write effect make a copy statement for the variable written on there equivalent for each cluster.
 * \param s         statement to check if it's need to make copy
 */
static void copy_write_statement(statement s) {
  pips_debug(3, "begin\n");
  if (!declaration_statement_p(s)) {
    list lpeffects = NIL;
    list lweffects = NIL;
    int nbr_copy = get_int_property(MPI_GENERATION_NBR_CLUSTER);
    task t = load_parallel_task_mapping(s);

    lpeffects = load_proper_rw_effects_list(s);
    lweffects = effects_write_effects(lpeffects);

    if (!ENDP(lweffects)) {
      //There is some write
      if (task_on_cluster(t) == -1) {
        //The statement must be executed by all the clusters
        // copy the same statement
        //    lhs=rhs;   ->    lhs=rhs; lhs_1=rhs; ...
        //TODO
        // print_statement(s);
        copy_n_statement(lweffects, nbr_copy, s);
      }
      else {
        //The statement is executed by 1 cluster
        //for each write effect, we make nbr_copy copy statement of the reference of the write effect
        FOREACH(EFFECT, we, lweffects)
          {
          reference wref = effect_any_reference(we);
          entity went = reference_variable(wref);
          // test if the entity decl is not in the private list of the task, if so no copy
          if (!entity_in_list_p(went, task_private_data(t))) {
            // copy the value of the lhs
            //    lhs=rhs;   ->    lhs=rhs; lhs_1=lhs; ...
            if(!effects_package_entity_p(went)
                && !ENTITY_STDERR_P(went) && !ENTITY_STDIN_P(went) && !ENTITY_STDOUT_P(went))
              //don't want, rand, malloc, printf, scanf...
              copy_n_reference(wref, nbr_copy, s);
          }
          }
      }
    }
  }
  pips_debug(3, "end\n");
}

/**
 * PIPS pass
 */
bool copy_value_of_write(const char* module_name) {
  statement module_statement;
  bool good_result_p = true;

  debug_on("MPI_GENERATION_DEBUG_LEVEL");
  pips_debug(1, "begin\n");

  //-- configure environment --//
  set_current_module_entity(module_name_to_entity(module_name));

  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, module_name, true) );
  module_statement = get_current_module_statement();

  pips_assert("Statement should be OK before...",
      statement_consistent_p(module_statement));

  set_ordering_to_statement(module_statement);

  //-- get dependencies --//
//  if(use_points_to) {
//    set_pointer_info_kind(with_points_to); //enough?
//  }
  set_proper_rw_effects((statement_effects)
      db_get_memory_resource(DBR_PROPER_EFFECTS, module_name, true));
  set_cumulated_rw_effects((statement_effects)
      db_get_memory_resource(DBR_CUMULATED_EFFECTS, module_name, true));
  set_parallel_task_mapping((statement_task)
      db_get_memory_resource(DBR_TASK, module_name, true));


  //-- Make the job -- //
  gen_recurse(module_statement, statement_domain, gen_true, copy_write_statement);
//  gen_recurse(module_statement, statement_domain, copy_write_statement, gen_true);
//  if(use_points_to) {
//    //TODO
//    //gen_recurse(module_statement, statement_domain, gen_true, identity_statement_remove_with_points_to);
//  }

  pips_assert("Statement should be OK after...",
      statement_consistent_p(module_statement));

  // Removed useless block created by the insert_statement
  unspaghettify_statement(module_statement);

  /* Reorder the module, because some statements have been added.
     Well, the order on the remaining statements should be the same,
     but by reordering the statements, the number are consecutive. Just
     for pretty print... :-) */
  module_reorder(module_statement);

  pips_assert("Statement should be OK after...",
      statement_consistent_p(module_statement));

  //-- Save modified code to database --//
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, strdup(module_name), module_statement);
  DB_PUT_MEMORY_RESOURCE(DBR_TASK, module_name, get_parallel_task_mapping());

  reset_ordering_to_statement();
  reset_cumulated_rw_effects();
  reset_proper_rw_effects();
  reset_current_module_statement();
  reset_current_module_entity();
  reset_parallel_task_mapping();

  pips_debug(1, "end\n");
  debug_off();

  return (good_result_p);
}

/*********************************************
 * With cumulated regions
 *********************************************/

/**
 * copy_write_statement_with_cumulated_regions
 * foreach first level statement in module_statement
 *   generate copies for variables present in out-region
 *   if it's an array region, generate variable for indices
 * \param module_statement              a module statement to work on
 * modification of module_statement by side effect
 */
static void copy_write_statement_with_cumulated_regions(statement module_statement) {
  ifdebug(2) {
    pips_debug(2, "begin\n");
    pips_debug(2, "statement with : \n");
    print_statement(module_statement);
  }

  if (statement_sequence_p(module_statement)) {
    list loutregioneffects = NIL;
    list lweffects = NIL;
    task t = task_undefined;
    int nbr_copy = get_int_property(MPI_GENERATION_NBR_CLUSTER);
    sequence seq = statement_sequence(module_statement);
    list stats = sequence_statements(seq);

    FOREACH(STATEMENT, s, stats) {
      loutregioneffects = load_live_out_regions_list(s);
      //loutregioneffects = load_statement_out_regions(s);
      //really need? since we use out_regions, all the list of effect must already be write.
      lweffects = effects_write_effects(loutregioneffects);
      t = load_parallel_task_mapping(s);

      if (!ENDP(lweffects)) {
        //There is some write
        if (task_on_cluster(t) == -1) {
          //The statement must be executed by all the clusters
          // copy the same statement
          //    lhs=rhs;   ->    lhs=rhs; lhs_1=rhs; ...
          copy_n_statement(lweffects, nbr_copy, s);
          //TODO boucle for min/max à rajouter pour les tableaux
        }
        else {
          //The statement is executed by 1 cluster
          //for each write effect, we make nbr_copy copy statement of the reference of the write effect
          FOREACH(EFFECT, we, lweffects) {
            reference wref = effect_any_reference(we);
            entity went = reference_variable(wref);

            /* test if the entity went is not in the private list of the task,
             * don't want rand, malloc, printf, scanf...
             * if so no copy
             */
            if (!entity_in_list_p(went, task_private_data(t)) &&
                !effects_package_entity_p(went) &&
                !ENTITY_STDERR_P(went) && !ENTITY_STDIN_P(went) && !ENTITY_STDOUT_P(went)
            ) {
              // copy the value of the lhs
              //    lhs=rhs;   ->    lhs=rhs; lhs_1=lhs; ...

              ifdebug(2) {
                pips_debug(2, "write effect on variable:\n");
                print_entity_variable(went);
                pips_debug(2, "system of constraints:\n");
                print_region_sc(we);
              }

              descriptor desceffect = effect_descriptor(we);
              list indices = reference_indices(wref);

              //not a write region but still write effect (eg x=0;)
              if (descriptor_none_p(desceffect) || indices == NIL) {
                copy_n_reference(wref, nbr_copy, s);
              }
              //write region (eg a[i]=i; with 0<i<10)
              else if (descriptor_convex_p(desceffect)) {
                Psysteme sc = descriptor_convex(desceffect);
                statement sequence_statement_for_copy = make_empty_block_statement();
                store_or_update_parallel_task_mapping(sequence_statement_for_copy, t);
                //statement sequence_statement_for_copy = make_block_statement(CONS(STATEMENT, make_plain_continue_statement(), NIL));

                Psysteme sc2 = sc_dup(sc);
                Pbase base_index = NULL;
                FOREACH(EXPRESSION, index, indices) {
                  entity indexent = expression_to_entity(index);
                  entity nent = region_entity_variable_to_new_declare_entity(indexent, task_id(t));

                  sc2 = sc_variable_rename(sc2, (Variable) indexent, (Variable) nent);
                  base_index = base_add_variable(base_index, (Variable) nent);
                }
                //base_index = base_reversal(base_index);

                Psysteme condition = SC_UNDEFINED,
                    enumeration = SC_UNDEFINED;

                algorithm_row_echelon(sc2, base_index,
                    &condition, &enumeration);

                ifdebug(8) {
                  pips_debug(8, "sc:\n");
                  if (sc2!=NULL){
                    sc_print(sc2, (get_variable_name_t) pips_region_user_name);
                    pips_debug(8, "Nb_eq %d , Nb_ineq %d, dimension %d\n", (sc2)->nb_eq, (sc2)->nb_ineq, (sc2)->dimension);
                  }
                  else
                    pips_debug(8, "sc2==NULL\n");

                  pips_debug(8, "condition:\n");
                  if (condition!=NULL){
                    sc_print(condition, (get_variable_name_t) pips_region_user_name);
                    pips_debug(8, "Nb_eq %d , Nb_ineq %d, dimension %d\n", (condition)->nb_eq, (condition)->nb_ineq, (condition)->dimension);
                  }
                  else
                    pips_debug(8, "condition==NULL\n");

                  pips_debug(8, "enumeration:\n");
                  if (enumeration!=NULL) {
                    sc_print(enumeration, (get_variable_name_t) pips_region_user_name);
                    pips_debug(8, "Nb_eq %d , Nb_ineq %d, dimension %d\n", (enumeration)->nb_eq, (enumeration)->nb_ineq, (enumeration)->dimension);
                  }
                  else
                    pips_debug(8, "enumeration==NULL\n");
                }

                statement stat;
                stat = systeme_to_loop_nest(enumeration, base_to_list(base_index),
                    sequence_statement_for_copy,
                    entity_intrinsic(DIVIDE_OPERATOR_NAME));
                statement_convert_to_statement_with_sequence_of_intruction(stat, true);

                //add the declarations if necessary
                push_generated_variable_commenter(copy_variable_declaration_commenter);
                BASE_FOREACH(var, base_index) {
                  entity ne = (entity) var;

                  //if entity ne not declare, add the declaration
                  if (!entity_in_list_p(ne, statement_to_direct_declarations(stat))) {
                    add_declaration_statement(stat, ne);
                    //add_declaration_statement_at_beginning(stat, ne);
                    statement_declarations(stat) = CONS(ENTITY, ne, statement_declarations(stat));
                    AddLocalEntityToDeclarationsOnly(ne, get_current_module_entity(), stat);
                    //ram r = storage_ram(entity_storage(ne));
                    //entity m = ram_function(r);
                    //AddEntityToDeclarations(ne, m);
                  }
                }
                pop_generated_variable_commenter();

                //fill the body of the loop
                //generate the copy lhs0[i0] = lhs[i0]
                copy_n_reference(wref, nbr_copy, sequence_statement_for_copy);

                //add the copy array statements (the loop) to the program
                if (!statement_sequence_p(s)) {
                  statement_convert_to_statement_with_sequence_of_intruction(s, true);
                  //statement_convert_to_statement_with_sequence_of_intruction(s, false);
                  //store_or_update_parallel_task_mapping(STATEMENT(CAR(sequence_statements(instruction_sequence(statement_instruction(s))))), t);
                }
                insert_comments_to_statement(stat, "Copy statements generated with OUT-REGION");
                insert_statement(s, stat, false);
              }
              else if (descriptor_convexunion_p(desceffect)) {
                //TODO
                pips_internal_error("Not done yet...\n");
              }
              else {
                pips_internal_error("This case never occurs\n descriptor = %d\n", descriptor_tag(desceffect));
              }
            }
          }
        }
      }

      loutregioneffects = NIL;
      lweffects = NIL;
      t = task_undefined;
    }
  }
  else {
    pips_internal_error("The statement must be the module statement (a sequence of instruction).\n");
  }

  ifdebug(2) {
    pips_debug(2, "statement with : \n");
    print_statement(module_statement);
    pips_debug(2, "end\n");
  }
}

/**
 * PIPS pass
 */
bool copy_value_of_write_with_cumulated_regions(const char* module_name) {
  statement module_statement;
  bool good_result_p = true;

  debug_on("MPI_GENERATION_DEBUG_LEVEL");
  pips_debug(1, "begin\n");

  //-- configure environment --//
  set_current_module_entity(module_name_to_entity(module_name));

  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, module_name, true) );
  module_statement = get_current_module_statement();

  pips_assert("Statement should be OK before...",
      statement_consistent_p(module_statement));

  set_ordering_to_statement(module_statement);

  //-- get dependencies --//
//  if(use_points_to) {
//    set_pointer_info_kind(with_points_to); //enough?
//  }
  set_proper_rw_effects((statement_effects)
      db_get_memory_resource(DBR_PROPER_EFFECTS, module_name, true));
  set_cumulated_rw_effects((statement_effects)
      db_get_memory_resource(DBR_CUMULATED_EFFECTS, module_name, true));
  set_live_out_regions((statement_effects)
  //set_out_effects((statement_effects)
      db_get_memory_resource(DBR_LIVE_OUT_REGIONS, module_name, true));
  set_parallel_task_mapping((statement_task)
      db_get_memory_resource(DBR_TASK, module_name, true));


  //-- Make the job -- //
  //No gen_recurse, only want to work on statement on the first level of the function
  copy_write_statement_with_cumulated_regions(module_statement);
//  gen_recurse(module_statement, statement_domain, gen_true, copy_write_statement_with_cumulated_regions);
//  if(use_points_to) {
//    //TODO
//    //gen_recurse(module_statement, statement_domain, gen_true, copy_write_statement_with_cumulated_regions);
//  }

  pips_assert("Statement should be OK after...",
      statement_consistent_p(module_statement));

  // Removed useless block created by the insert_statement
  unspaghettify_statement(module_statement);

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
  reset_proper_rw_effects();
  reset_cumulated_rw_effects();
  reset_live_out_regions();
  reset_current_module_statement();
  reset_current_module_entity();
  reset_parallel_task_mapping();

  pips_debug(1, "end\n");
  debug_off();

  return (good_result_p);
}




