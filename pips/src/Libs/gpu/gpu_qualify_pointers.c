/*
  $Id: gpu_qualify_pointers.c 23367 2017-02-10 14:35:39Z coelho $

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

#include <assert.h>

#include "genC.h"
#include "linear.h"
#include "misc.h"

#include "properties.h"
#include "resources.h"
#include "pipsdbm.h"
#include "ri-util.h"

/********************************************************************* UTILS */

// return whether a variable has a given qualifier
static bool variable_is_qualified_as(variable var, enum qualifier_utype qt)
{
  FOREACH(qualifier, q, variable_qualifiers(var))
    if (qualifier_tag(q) == qt)
      return true;
  return false;
}

static bool variable_is_glopriv(variable var, bool is_glob)
{
  return variable_is_qualified_as(
    var, is_glob? is_qualifier_global: is_qualifier_private);
}

static void set_variable_qualifier(variable var, bool is_glob)
{
  pips_debug(8, "setting var %p as %s\n", var, is_glob? "global": "private");

  // check with a user error beforehand...
  pips_assert(!variable_is_glopriv(var, !is_glob), "cannot be private & global");

  // skip if already set
  if (!variable_is_glopriv(var, is_glob))
  {
    qualifier q = is_glob? make_qualifier_global(): make_qualifier_private();
    variable_qualifiers(var) =  gen_qualifier_cons(q, variable_qualifiers(var));
  }
}

// does it has "global" or "private"?
static bool is_glopriv(entity evar, bool is_glob)
{
  pips_assert(entity_variable_p(evar), "qualified entity is a variable");
  return variable_is_glopriv(type_variable(entity_type(evar)), is_glob);
}

/* add a qualifier to a variable, which should be a pointer...
 */
static void set_glopriv_qualifier(entity evar, bool is_glob)
{
  pips_debug(3, "marking %s as %s\n",
             entity_name(evar), is_glob? "global": "private");

  pips_assert(entity_variable_p(evar), "qualified entity is a variable");
  pips_assert(entity_pointer_p(evar) || entity_array_p(evar),
              "variable must be a pointer type");

  // check here to have the variable name
  variable var = type_variable(entity_type(evar));
  if (variable_is_glopriv(var, !is_glob))
    pips_user_error("pointer %s cannot be set as %s, it is already %s\n",
                    entity_name(evar),
                    is_glob? "global": "private", is_glob? "private": "global");

  // do not set if already set. not sure how it could get there...
  if (!variable_is_glopriv(var, is_glob))
    set_variable_qualifier(var, is_glob);
  // else could warn that it get there twice?
}

static bool is_global(entity evar)
{
  return is_glopriv(evar, true);
}

static bool is_private(entity evar)
{
  return is_glopriv(evar, false);
}

static void set_global(entity evar)
{
  set_glopriv_qualifier(evar, true);
}

static void set_as_private(entity evar)
{
  set_glopriv_qualifier(evar, false);
}

/************************************************************ GLOBALS/PRIVATES */

/* structure to collect whether anything should be qualified as
 * private or global, for OpenCL 1.X code.
 */
typedef struct
{
  bool changed; // hmmm... iterations
  // set of anything (entity, expression ...)
  set globals;
  set privates;
  // may skip
  bool do_call_sites;
  hash_table call_sites; // entity -> list<call>
  // whether to qualify casts
  bool do_casts;
} glopriv_context_t;

static glopriv_context_t * new_glopriv(void)
{
  glopriv_context_t * glc = malloc(sizeof(glopriv_context_t));
  glc->globals = set_make(set_pointer);
  glc->privates = set_make(set_pointer);
  glc->do_call_sites = true;
  glc->call_sites = hash_table_make(hash_pointer, 100);
  glc->changed = false;
  glc->do_casts = true;
  return glc;
}

static void set_glopriv(
  glopriv_context_t * glc, void * stuff, bool is_glob,
  string why)
{
  pips_assert(stuff != NULL, "some stuff");

  // not necessary
  if ((is_glob && set_belong_p(glc->globals, stuff)) ||
      (!is_glob && set_belong_p(glc->privates, stuff)))
    return;

  ifdebug(5)
  {
    int dom = * (int*) stuff;
    if (dom == entity_domain)
      pips_debug(5, "marking entity %s as %s (%s)\n",
                 entity_name((entity) stuff), is_glob? "global": "private", why);
    else
      pips_debug(5, "marking %s %p as %s (%s)\n",
                 gen_domain_name(* (int *) stuff),
                 stuff, is_glob? "global": "private", why);
  }

  if (is_glob && !set_belong_p(glc->globals, stuff))
  {
    set_add_element(glc->globals, glc->globals, stuff);
    glc->changed = true;
  }
  else if (!is_glob && !set_belong_p(glc->privates, stuff))
  {
    set_add_element(glc->privates, glc->privates, stuff);
    glc->changed = true;
  }
}

static void free_glopriv(glopriv_context_t ** pglc)
{
  set_free((*pglc)->globals);
  set_free((*pglc)->privates);
  HASH_FOREACH(entity, f, list, l, (*pglc)->call_sites) gen_free_list(l);
  hash_table_free((*pglc)->call_sites);
  free(*pglc);
  *pglc = NULL;
}

// analyse reference as private or global
static void glc_ref(reference r, glopriv_context_t * glc)
{
  entity var = reference_variable(r);

  // nothing to do? should it be marked anyway?
  if (!(entity_pointer_p(var) || entity_array_p(var)))
    return;

  // skip scalars?
  /*
  unsigned int ndims =
    gen_length(variable_dimensions(type_variable(entity_type(var))));
  if (ndims && gen_length(reference_indices(r)) == ndims)
    return;
  */

  expression enclosing =
    (expression) gen_get_current_ancestor(expression_domain);

  if (is_global(var))
  {
    set_glopriv(glc, var, true, "global ref ent");
    set_glopriv(glc, enclosing, true, "global ref expr");
  }
  else if (is_private(var))
  {
    set_glopriv(glc, var, false, "private ref ent");
    set_glopriv(glc, enclosing, false, "private ref expr");
  }
  // else do not know
}

/* ptr = ptr
 * & reference...
 * pointer arithmetic with +
 */
static void glc_call(call c, glopriv_context_t * glc)
{
  entity called = call_function(c);
  list args = call_arguments(c);

  pips_debug(3, "considering call to %s\n", entity_name(called));

  if (glc->do_call_sites)
  {
    // hm... need only keep track of "user" functions?
    if (!hash_defined_p(glc->call_sites, called))
      hash_put(glc->call_sites, called, CONS(call, c, NIL));
    else
      hash_update(glc->call_sites, called,
                  CONS(call, c, (list) hash_get(glc->call_sites, called)));
  }

  expression enclosing =
    (expression) gen_get_current_ancestor(expression_domain);

  if (ENTITY_ASSIGN_P(called))
  {
    pips_assert(gen_length(args) == 2, "2 operands to assign operator '='");
    expression e1 = EXPRESSION(CAR(args)), e2 = EXPRESSION(CAR(CDR(args)));
    pips_assert(expression_reference_p(e1),
                "assign left operator is a reference");

    if (expression_pointer_p(e1))
    {
      entity var = reference_variable(expression_reference(e1));
      if (set_belong_p(glc->globals, e2))
      {
        set_glopriv(glc, var, true, "assign global var ent");
        set_glopriv(glc, e1, true, "assign global lexpr");
        if (enclosing)
          set_glopriv(glc, enclosing, true, "assign global expr");
      }
      else if (set_belong_p(glc->privates, e2))
      {
        set_glopriv(glc, var, false, "assign private var ent");
        set_glopriv(glc, e1, false, "assign private lexpr");
        if (enclosing)
          set_glopriv(glc, enclosing, false, "assign private expr");
      }
    }
  }
  else if (enclosing && ENTITY_ADDRESS_OF_P(called))
  {
    pips_assert(gen_length(args) == 1, "one reference to &");
    expression arg = EXPRESSION(CAR(args));
    if (expression_reference_p(arg))
    {
      entity var = reference_variable(expression_reference(arg));
      if (set_belong_p(glc->globals, var))
        set_glopriv(glc, enclosing, true, "& global expr");
      else if (set_belong_p(glc->privates, var))
        set_glopriv(glc, enclosing, false, "& private expr");
    }
  }
  else if (enclosing &&
           (ENTITY_PLUS_P(called) || ENTITY_PLUS_C_P(called) ||
            ENTITY_MINUS_P(called) || ENTITY_MINUS_C_P(called)))
  {
    // just for pointer arithmetic
    pips_assert(gen_length(args) == 2, "2 operands to +/- operators");
    expression e1 = EXPRESSION(CAR(args)), e2 = EXPRESSION(CAR(CDR(args)));

    // should it detect bad typing, eg "ptr + ptr"? NOT THE POINT!

    if (set_belong_p(glc->globals, e1) || set_belong_p(glc->globals, e2))
      set_glopriv(glc, enclosing, true, "global ptr arith expr");
    else if (set_belong_p(glc->privates, e1) || set_belong_p(glc->privates, e2))
      set_glopriv(glc, enclosing, false, "private ptr arith expr");
  }
  // else: others??
}

// handle casts
// hmmm... type cast on the fly? but is it really needed?
static void glc_cast(cast c, glopriv_context_t * glc)
{
  expression enclosing =
    (expression) gen_get_current_ancestor(expression_domain);

  // empty cast? already processed?
  if (enclosing == NULL ||
      set_belong_p(glc->globals, enclosing) ||
      set_belong_p(glc->privates, enclosing))
    return;

  expression e = cast_expression(c);
  type t = cast_type(c);
  pips_assert(type_variable_p(t), "cast to a variable type");

  if (set_belong_p(glc->globals, e))
  {
    set_glopriv(glc, enclosing, true, "global cast");
    if (glc->do_casts)
      set_variable_qualifier(type_variable(t), true);
  }
  else if (set_belong_p(glc->privates, e))
  {
    set_glopriv(glc, enclosing, false, "private cast");
    if (glc->do_casts)
      set_variable_qualifier(type_variable(t), false);
  }
}

static void collect_glopriv(void * stuff, glopriv_context_t * glc)
{
  gen_context_multi_recurse(stuff, glc,
                            reference_domain, gen_true, glc_ref,
                            call_domain, gen_true, glc_call,
                            cast_domain, gen_true, glc_cast,
                            NULL);
}

static void collect_glopriv_data(entity f, statement s, glopriv_context_t * glc)
{
  pips_debug(2, "collecting glopriv data\n");

  // process code
  collect_glopriv(s, glc);

  // process initializations
  FOREACH(entity, var, code_declarations(value_code(entity_initial(f))))
  {
    value val = entity_initial(var);
    if (entity_variable_p(var) && entity_pointer_p(var) &&
        value_expression_p(val))
    {
      expression init = value_expression(val);
      collect_glopriv(init, glc);
      if (set_belong_p(glc->globals, init))
        set_glopriv(glc, var, true, "global init");
      else if (set_belong_p(glc->privates, init))
        set_glopriv(glc, var, false, "private init");
    }
  }

  // once is enough for getting calls
  glc->do_call_sites = false;
}

/******************************************************************* DRIVERS */

void do_gpu_qualify_pointers(
  entity module,
  statement code,
  callees funcs,
  bool do_casts)
{
  pips_debug(2, "qualifying pointers in module %s\n", entity_name(module));

  // check for module parameters, mark them if needed
  // note: there are declarations in the code and in the function signature
  // should it be set on both?
  pips_assert(entity_function_p(module), "module must be a function");
  value val = entity_initial(module);
  pips_assert(value_code_p(val), "function must have code");

  // set formal parameters as private or global, in doubt set as global
  list params = functional_parameters(type_functional(entity_type(module)));
  FOREACH(entity, var, code_declarations(value_code(val)))
  {
    if (formal_parameter_p(var))
    {
      if (entity_pointer_p(var) || entity_array_p(var))
      {
        int number = formal_offset(storage_formal(entity_storage(var)));
        type tn = parameter_type(PARAMETER(gen_nth(number-1, params)));
        pips_assert(type_variable_p(tn), "formal parameter is a variable");
        variable fp = type_variable(tn);

        if (variable_is_glopriv(fp, true))
          set_global(var);
        else if (variable_is_glopriv(fp, false))
          set_as_private(var);
        else  // in doubt, assume it is a global pointer
        {
          pips_user_warning("no clue, set formal parameter %s as global\n",
                            entity_name(var));
          set_variable_qualifier(fp, true);
          set_global(var);
        }
      }
    }
    else if (entity_array_p(var))
      // just a private array declaration
      set_as_private(var);
  }

  // pass through the code
  glopriv_context_t * glc = new_glopriv();
  glc->do_casts = do_casts;
  bool try_again = true;
  int iteration = 0;

  while (try_again)
  {
    iteration++;
    pips_debug(3, "propagating privates & globals iteration %d\n", iteration);

    // update global/private information
    glc->changed = false;
    collect_glopriv_data(module, code, glc);

    // if something is needed and it is not converging?
    if (iteration > 1 && !glc->changed)
      // this may happen if some pointers are not used,
      // or point to unqualified scalars
      break;

    // if changed, more expr may be qualified even if no entity is concerned
    // this iteration is needed for ensuring that calls are well qualified.
    try_again = glc->changed;

    // qualify pointers if possible
    FOREACH(entity, var, code_declarations(value_code(val)))
    {
      if (entity_variable_p(var))
      {
        pips_debug(8, "considering variable %s (global=%d, private=%d)\n",
                   entity_name(var), is_global(var), is_private(var));
        if (!formal_parameter_p(var) &&
            (entity_pointer_p(var) || entity_array_p(var)) &&
            !is_private(var) && !is_global(var))
        {
          bool
            var_is_global = set_belong_p(glc->globals, var),
            var_is_private = set_belong_p(glc->privates, var);

          // no "else", so as to trigger user errors if need be
          if (var_is_global)
            set_global(var);
          if (var_is_private)
            set_as_private(var);
          if (!var_is_global && !var_is_private) // in doubt? set_as_private(var);
          {
            pips_debug(5, "in doubt about %s, retrying...\n", entity_name(var));
            try_again = true;
          }
        }
      }
    }
  }

  // unmarked remaining pointers are expected to be private only
  // see x/z w/v in "validation/Gpu/glopriv04.c"
  FOREACH(entity, var, code_declarations(value_code(val)))
  {
    if (entity_variable_p(var) && !formal_parameter_p(var) &&
        (entity_pointer_p(var) || entity_array_p(var)) &&
        !is_private(var) && !is_global(var))
      set_as_private(var);
  }

  // now mark/check callee parameters
  FOREACH(string, f, callees_callees(funcs))
  {
    pips_debug(3, "updating call to %s\n", f);
    entity callee = module_name_to_entity(f);
    list params = functional_parameters(type_functional(entity_type(callee)));

    if (hash_defined_p(glc->call_sites, callee))
    {
      FOREACH(call, c, (list) hash_get(glc->call_sites, callee))
      {
        pips_assert(call_function(c) == callee, "good function called");
        pips_assert(gen_length(params) == gen_length(call_arguments(c)),
                    "matching #arguments & #parameters");
        list lp = params;
        int nparam = 0;
        FOREACH(expression, e, call_arguments(c))
        {
          parameter p = PARAMETER(CAR(lp));
          dummy d = parameter_dummy(p);
          const string sp = dummy_unknown_p(d)?
            "?": (const string) entity_local_name(dummy_identifier(d));
          type te = parameter_type(p);
          lp = CDR(lp);
          nparam += 1;

          if (!pointer_type_p(te) && !array_type_p(te))
          {
            pips_debug(5, "skipping non pointer parameter %s:%d (%s)\n",
                       entity_name(callee), nparam, sp);
            continue;
          }

          pips_assert(type_variable_p(te), "type is a variable");
          variable var = type_variable(te);
          bool global_expr = set_belong_p(glc->globals, e),
            private_expr = set_belong_p(glc->privates, e),
            var_is_global = variable_is_glopriv(var, true),
            var_is_private = variable_is_glopriv(var, false);

          if (global_expr && private_expr)
            // is it possible, or would it be an internal error?
            pips_user_error("formal parameter \"%s\" (#%d of \"%s\") is both "
                            "private & global\n",
                            sp, nparam, entity_name(callee));
          if (global_expr && var_is_private)
            pips_user_error("formal parameter \"%s\" (#%d of \"%s\") is "
                            "already private, cannot switch it to global\n",
                            sp, nparam, entity_name(callee));
          if (private_expr && var_is_global)
            pips_user_error("formal parameter \"%s\" (#%d of \"%s\") is "
                            "already global, cannot switch it to private\n",
                            sp, nparam, entity_name(callee));

          // no else so as to possibly trigger some errors...
          if (global_expr)
            set_variable_qualifier(var, true);
          if (private_expr)
            set_variable_qualifier(var, false);
          if (!global_expr && !private_expr) // in doubt, set as private...
          {
            pips_debug(5, "setting %s:%d (%s) as private by default\n",
                       entity_name(callee), nparam, sp);
            set_variable_qualifier(var, false);
          }
        }
      }
    }
    // else the callee is not called? unlikely:-)
  }

  // cleanup
  free_glopriv(&glc);
}

/*
  gpu_qualify_pointers  > MODULE.code
	       > PROGRAM.entities
         < PROGRAM.entities
         < MODULE.code
         < MODULE.callees

  Some limitations:
   - it does not deal with pointer in structures or arrays.
   - ...
*/
bool gpu_qualify_pointers(const string module_name)
{
  set_current_module_entity(module_name_to_entity(module_name));
  set_current_module_statement((statement)
    db_get_memory_resource(DBR_CODE, module_name, true));
  callees funcs = (callees)
    db_get_memory_resource(DBR_CALLEES, module_name, true);

  debug_on("GPU_QUALIFY_POINTERS_DEBUG_LEVEL");
  pips_debug(1, "running on %s", module_name);

  do_gpu_qualify_pointers(get_current_module_entity(),
                          get_current_module_statement(),
                          funcs,
                          get_bool_property("GPU_QUALIFY_POINTERS_DO_CASTS"));

  DB_PUT_MEMORY_RESOURCE(DBR_CODE, module_name,
                         get_current_module_statement());

  debug_off();

  reset_current_module_statement();
  reset_current_module_entity();

  return true;
}
