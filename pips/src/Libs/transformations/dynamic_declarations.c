/*

  $Id: dynamic_declarations.c 23065 2016-03-02 09:05:50Z coelho $

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

// do not compile unless used
#include "phases.h"
#ifdef BUILDER_CLEAN_UNUSED_DYNAMIC_VARIABLES

#ifdef HAVE_CONFIG_H
    #include "pips_config.h"
#endif
/*
 * clean the declarations of a module.
 * to be called from pipsmake.
 */

#include <stdio.h>

#include "genC.h"
#include "linear.h"

#include "pipsdbm.h"
#include "misc.h"
#include "properties.h"

#include "ri.h"
#include "effects.h"
#include "ri-util.h"
#include "effects-util.h"

#include "effects-generic.h" // used
#include "control.h" // for clean_up_sequences, module_reorder
#include "transformations.h" // clean_declarations

/****************************************************** DYNAMIC DECLARATIONS */

#define expr_var(e) reference_variable(expression_reference(e))

#define call_assign_p(c) \
  same_string_p(entity_local_name(call_function(c)), ASSIGN_OPERATOR_NAME)

struct helper {
  int removed_vars;   // how many variables where removed
  const char* module;      // current module being cleaned up
  const char* func_malloc; // allocation function
  const char* func_free;   // deallocation function
  set referenced;     // referenced entities
};

// Pass 1: collect local referenced variables
static bool ignore_call_flt(call c, struct helper * ctx)
{
  // ignores free(var)
  if (same_string_p(entity_local_name(call_function(c)), ctx->func_free))
    return false;

  // ignores "var =  malloc(...)" (but not malloc arguments!)
  if (call_assign_p(c))
  {
    list args = call_arguments(c);
    pips_assert("2 args to assign", gen_length(args)==2);
    expression val = EXPRESSION(CAR(CDR(args)));

    if (expression_call_p(val) &&
        same_string_p(entity_local_name(call_function(expression_call(val))),
                      ctx->func_malloc))
    {
      pips_debug(5, "malloc called\n");
      gen_recurse_stop(EXPRESSION(CAR(args)));
    }

    // ??? should I also ignore "var = NULL"?
    // and other constant assignments?
  }

  return true;
}

static bool reference_flt(reference r, struct helper * ctx)
{
  // pips_debug(9, "%s used in statement %" _intFMT "\n",
  //   entity_name(reference_variable(r)),
  //   statement_number((statement) gen_get_ancestor(statement_domain, r)));
  set_add_element(ctx->referenced, ctx->referenced, reference_variable(r));
  return true;
}

static bool loop_flt(loop l, struct helper * ctx)
{
  set_add_element(ctx->referenced, ctx->referenced, loop_index(l));
  return true;
}

static bool unused_local_variable_p(entity var, set used, const char* module)
{
  bool unused = same_string_p(entity_module_name(var), module)
    // keep function auto-declaration for recursion
    && !same_string_p(entity_local_name(var), module)
    && !set_belong_p(used, var)
    && !formal_parameter_p(var)
    && type_variable_p(ultimate_type(entity_type(var)));
  pips_debug(8, "%s is %sused (%d)\n",
             entity_name(var), unused? "UN": "", set_belong_p(used, var));
  return unused;
}

// Pass 2:
static void cleanup_call(call c, struct helper * ctx)
{
  pips_debug(6, "call to %s\n", entity_name(call_function(c)));

  bool replace = false;

  if (same_string_p(entity_local_name(call_function(c)), ctx->func_free))
  {
    // get FREE-d variable, which is the first and only argument
    list args = call_arguments(c);
    if (gen_length(args)==1)
    {
      expression arg = EXPRESSION(CAR(args));
      if (expression_reference_p(arg) &&
          unused_local_variable_p(expr_var(arg), ctx->referenced, ctx->module))
        replace = true;
    }
    // else what?
  }
  else if (call_assign_p(c))
  {
    list args = call_arguments(c);
    expression val = EXPRESSION(CAR(CDR(args)));
    if (expression_call_p(val) &&
        same_string_p(entity_local_name(call_function(expression_call(val))),
                      ctx->func_malloc))
    {
      expression arg = EXPRESSION(CAR(args));
      if (expression_reference_p(arg) &&
          unused_local_variable_p(expr_var(arg), ctx->referenced, ctx->module))
        replace = true;
    }
    // var = NULL?
  }

  if (replace)
  {
    pips_debug(6, "replacing...\n");
    instruction ins =
      (instruction) gen_get_ancestor(instruction_domain, c);
    if (instruction_call_p(ins) && instruction_call(ins)==c)
      // continue is appropriate only if call is an instruction!
      call_function(c) = entity_intrinsic(CONTINUE_FUNCTION_NAME);
    else
      // ??? otherwise, let us try 0
      call_function(c) = int_to_entity(0);
    gen_full_free_list(call_arguments(c));
    call_arguments(c) = NIL;
  }
}

static void cleanup_stat_decls(statement s, struct helper * ctx)
{
  list decls = statement_declarations(s), kept = NIL;
  FOREACH(ENTITY, var, decls)
    if (!unused_local_variable_p(var, ctx->referenced, ctx->module))
      kept = CONS(ENTITY, var, kept);
    else
      ctx->removed_vars++;
  statement_declarations(s) = gen_nreverse(kept);
  gen_free_list(decls);
}

static void dynamic_cleanup(string module, statement stat)
{
  entity mod = local_name_to_top_level_entity(module);

  struct helper help;
  help.module = module;
  // use dynamic definition for malloc/free.
  help.func_malloc = get_string_property("DYNAMIC_ALLOCATION");
  help.func_free = get_string_property("DYNAMIC_DEALLOCATION");
  help.referenced = set_make(set_pointer);

  // transitive closure as dynamic allocation may depend one from another.
  // eg in FREIA, images are created with the size of another...
  do {
    help.removed_vars = 0;
    set_clear(help.referenced);

    // pass 1: collect references in code
    gen_context_multi_recurse
      (stat, &help,
       reference_domain, reference_flt, gen_null,
       loop_domain, loop_flt, gen_null,
       call_domain, ignore_call_flt, gen_null,
       NULL);

    // and in initializations
    FOREACH(ENTITY, var, entity_declarations(mod))
      gen_context_multi_recurse
        (entity_initial(var), &help,
         reference_domain, reference_flt, gen_null,
         call_domain, ignore_call_flt, gen_null,
         NULL);

    // pass 2: cleanup calls to  "= malloc" and "free" in code
    gen_context_multi_recurse
      (stat, &help,
       call_domain, gen_true, cleanup_call,
       statement_domain, gen_true, cleanup_stat_decls,
       NULL);

    // and in declarations
    list decls = entity_declarations(mod), kept = NIL;
    FOREACH(ENTITY, var, decls)
    {
      // pips_debug(8, "considering %s\n", entity_name(var));
      if (unused_local_variable_p(var, help.referenced, module))
      {
        value init = entity_initial(var);
        if (value_expression_p(init))
        {
          free_value(init);
          entity_initial(var) = make_value_unknown();
        }
        help.removed_vars++;
      }
      else
        kept = CONS(ENTITY, var, kept);
    }

    // is it useful? declarations are attached to statements in C.
    entity_declarations(mod) = gen_nreverse(kept);
    gen_free_list(decls), decls = NIL;

  } while (help.removed_vars>0);

  set_free(help.referenced);
}

/* A phase to remove useless dynamic heap variables that are not used but
   with malloc()/free()

   The names of the functions used to allocate/deallocate the variable can
   be specified by the DYNAMIC_ALLOCATION and DYNAMIC_DEALLOCATION
   properties.

   @param[in] module is the module name we want to clean

   @return true since everything should behave well...
 */
bool clean_unused_dynamic_variables(string module)
{
  debug_on("PIPS_CUDV_DEBUG_LEVEL");

  // get stuff from pipsdbm
  set_current_module_entity(module_name_to_entity(module));
  set_current_module_statement
    ((statement) db_get_memory_resource(DBR_CODE, module, true) );

  dynamic_cleanup(module, get_current_module_statement());
  clean_up_sequences(get_current_module_statement());

  // results
  module_reorder(get_current_module_statement());
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, module, get_current_module_statement());

  // cleanup
  reset_current_module_entity();
  reset_current_module_statement();
  debug_off();

  return true;
}

#endif // BUILDER_CLEAN_UNUSED_DYNAMIC_VARIABLES
