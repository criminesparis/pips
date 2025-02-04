/*

  $Id: freia_transformations.c 23495 2018-10-24 09:19:47Z coelho $

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

#include "genC.h"
#include "linear.h"

// newgen
#include "ri.h"
#include "effects.h"

#include "misc.h"
#include "ri-util.h"
#include "effects-util.h"
#include "callgraph.h"
#include "properties.h"

#include "resources.h"
#include "pipsdbm.h"

#include "control.h" // for clean_up_sequences
#include "effects-generic.h" // {set,reset}_proper_rw_effects

#include "freia.h"
#include "hwac.h"

/********************************************************************* UTILS */

/* remove "register" qualifier from qualifier list
 */
static list remove_register(list lq)
{
  FOREACH(qualifier, q, lq)
  {
    if (qualifier_register_p(q))
    {
      gen_remove_once(&lq, q);
      // register may be there once
      return lq;
    }
  }
  return lq;
}

// this should exists somewhere???
// top-down so that it is in ascending order?
// I'm not sure that it makes much sense, as
// the statement number is expected to be the source code line number?

static bool sr_flt(statement s, int * number)
{
  instruction i = statement_instruction(s);
  if (instruction_sequence_p(i))
    // it seems that sequences are expected not to have a number
    // just in case, force the property
    statement_number(s) = STATEMENT_NUMBER_UNDEFINED;
  else if (statement_number(s)!=STATEMENT_NUMBER_UNDEFINED)
    // just add a number if none are available?
    // otherwise, the initial number is kept
    statement_number(s) = (*number)++;
  return true;
}

static void stmt_renumber(statement s)
{
  int number=1;
  gen_context_recurse(s, &number, statement_domain, sr_flt, gen_null2);
}

/* look for a variable
 */
typedef struct
{
  bool used;
  entity var;
} vis_ctx;

static void vis_rwt(const reference r,  vis_ctx * ctx)
{
  if (reference_variable(r)==ctx->var)
  {
    ctx->used = true;
    gen_recurse_stop(NULL);
  }
}

static bool variable_is_used(statement s, entity var)
{
  vis_ctx ctx = { false, var };
  gen_context_recurse(s, &ctx, reference_domain, gen_true2, vis_rwt);
  return ctx.used;
}

/*********************************** UNROLL FREIA CONVERGENCE LOOPS FOR SPOC */

/*
  The purpose of this transformation is to unroll a special case of
  while convergence loop by an appropriate amount in order to fill-in
  the spoc pipeline.

  The implementation is quick and dirty, could be improved if needed.

  More could be done on these line if the pipeline before the while is not
  full, some iterations could be moved there as well. However, the information
  available when this transformation is applied is not sufficient to decide
  to do so.

  The two volumes to be compared are taken from the two last stages.
 */

typedef struct {
  int morpho;
  int comp;
  int vol;
  bool bad_stuff;
} fcs_ctx;

static bool fcs_count(statement s, fcs_ctx * ctx)
{
  if (!statement_call_p(s))
  {
    ctx->bad_stuff = true;
    gen_recurse_stop(NULL);
  }
  else
  {
    call c = freia_statement_to_call(s);
    if (c)
    {
      const char* called = entity_local_name(call_function(c));
      // could be: dilate + inf + vol or erode + sup + vol
      if (same_string_p(called, AIPO "erode_8c") ||
          same_string_p(called, AIPO "erode_6c") ||
          same_string_p(called, AIPO "dilate_8c") ||
          same_string_p(called, AIPO "dilate_6c"))
        ctx->morpho++;
      else if (same_string_p(called, AIPO "inf") ||
               same_string_p(called, AIPO "sup"))
        ctx->comp++;
      else if (same_string_p(called, AIPO "global_vol"))
        ctx->vol++;
      // else { // should do more filtering!
      // ctx->bad_stuff = true;
      // gen_recurse_stop(NULL);
      // }
    }
  }
  return false;
}

/* @return whether sq contains freia simple calls to E/D, </>, vol, =
 * this is rather an over approximation of whether it is a convergence
 * sequence, should be refined...
 */
static bool freia_convergence_sequence_p(sequence sq)
{
  fcs_ctx ctx = { 0, 0, 0, false };
  gen_context_recurse(sq, &ctx, statement_domain, fcs_count, gen_null2);
  return ctx.morpho==1 && ctx.comp==1 && ctx.vol==1 && !ctx.bad_stuff;
}

/* util defined somewhere ?????? */
typedef struct { entity ovar, nvar; } subs_ctx;

static void ref_rwt(reference r, subs_ctx * ctx)
{
  if (reference_variable(r)==ctx->ovar)
    reference_variable(r)=ctx->nvar;
}

static void substitute_reference_variable(statement s, entity ovar, entity nvar)
{
  subs_ctx ctx = { ovar, nvar };
  gen_context_recurse(s, &ctx, reference_domain, gen_true2, ref_rwt);
}

static void maybe_unroll_while_rwt(whileloop wl, bool * changed)
{
  if (statement_sequence_p(whileloop_body(wl)))
  {
    sequence sq = statement_sequence(whileloop_body(wl));
    if (freia_convergence_sequence_p(sq))
    {
      // unroll!
      int factor = get_int_property(spoc_depth_prop);
      pips_assert("some unrolling factor", factor>0);
      list ol = sequence_statements(sq);

      // sorry, just a hack to avoid a precise pattern matching
      statement first = STATEMENT(CAR(ol));
      pips_assert("s is an assignement", statement_call_p(first));
      gen_remove_once(&ol, first);
      list col = gen_copy_seq(ol), nl = NIL;
      list lass = call_arguments(statement_call(first));
      entity
        previous = expression_variable(EXPRESSION(CAR(lass))),
        current = expression_variable(EXPRESSION(CAR(CDR(lass))));

      // cleanup vol from col
      statement vols = statement_undefined;
      FOREACH(statement, s, col)
      {
        call c = freia_statement_to_call(s);
        if (c && same_string_p(entity_local_name(call_function(c)),
                               AIPO "global_vol"))
        {
          gen_remove_once(&col, s);
          vols = copy_statement(s);
          break;
        }
      }
      pips_assert("vol statement found", vols!=statement_undefined);

      // do factor-1
      while (--factor)
        nl = gen_nconc(gen_full_copy_list(col), nl);

      // compute "previous" volume for comparison
      substitute_reference_variable(vols, current, previous);

      // swith off "register" on previous, if need be...
      variable v = type_variable(entity_type(previous));
      variable_qualifiers(v) = remove_register(variable_qualifiers(v));

      // then reuse initial list for the last one
      sequence_statements(sq) = gen_nconc(nl, CONS(statement, vols, ol));

      // cleanup temporary list
      gen_free_list(col);

      // must renumber...
      *changed = true;
    }
  }
}

static bool freia_unroll_while_for_spoc(statement s)
{
  bool changed = false;
  gen_context_recurse(s, &changed,
                      whileloop_domain, gen_true2, maybe_unroll_while_rwt);
  return changed;
}

bool freia_unroll_while(const string module)
{
  // sanity check
  int factor = get_int_property(spoc_depth_prop);
  if (factor<=1)
  {
    pips_user_warning("cannot unroll with factor=%d\n", factor);
    return true;
  }

  // else, do the job
  debug_on("PIPS_HWAC_DEBUG_LEVEL");
  pips_debug(1, "considering module %s\n", module);

  // else do the stuff
  statement mod_stat =
    (statement) db_get_memory_resource(DBR_CODE, module, true);
  set_current_module_statement(mod_stat);
  set_current_module_entity(module_name_to_entity(module));

  // do the job
  bool changed = freia_unroll_while_for_spoc(mod_stat);

  // update if changed
  if (changed)
  {
    stmt_renumber(mod_stat);
    module_reorder(mod_stat);
    DB_PUT_MEMORY_RESOURCE(DBR_CODE, module, mod_stat);
  }

  // cleanup
  reset_current_module_statement();
  reset_current_module_entity();
  debug_off();
  return true;
}

/********************** SPECIAL CASE SCALAR WW DEPENDENCY HANDLING FOR FREIA */
/*
  When switching do-while to while on FREIA convergence loops, the code
  generates a scalar WW dependency within the sequence which prevents an
  operation to be merged. Pips is designed to be intelligent about loops
  for parallelization, whereas I really need some cleverness in sequences
  for FREIA compilation.

  The following code, where the reduction is a volume computation in our case:

    reductionl(image1, &something);
    somethingelse = something;
    reduction(image2, &something);

  should be replaced by:

    reduction(image1, &somethingelse);
    reduction(image2, &something);

  I'm not sure how this transformation could be generalized, possibly
  based on chains...
  Moreover, I'm not really sure how much I can rely on effects
  because of the pointers involved.
  So this is just a quick hack for my particular case.
*/

/* return the freia reduction entity, or NULL if it does not apply
 */
static entity freia_reduction_variable(const statement s)
{
  if (freia_statement_aipo_call_p(s))
  {
    const call c = freia_statement_to_call(s);
    const string called = (const string) entity_local_name(call_function(c));
    if (same_string_p(called, AIPO "global_min") ||
        same_string_p(called, AIPO "global_max") ||
        same_string_p(called, AIPO "global_min_coord") ||
        same_string_p(called, AIPO "global_max_coord") ||
        same_string_p(called, AIPO "global_vol"))
    {
      const expression last = EXPRESSION(CAR(gen_last(call_arguments(c))));
      // should be a call to "&" operator
      if (expression_address_of_p(last))
      {
        const expression arg =
          EXPRESSION(CAR(call_arguments(expression_call(last))));
        if (syntax_reference_p(expression_syntax(arg)))
          return expression_variable(arg);
      }
    }
  }
  // not found!
  return NULL;
}

static void sww_seq_rwt(const sequence sq, bool * changed)
{
  // current status of search
  statement previous_reduction = NULL;
  entity previous_variable = NULL;
  statement assignment = NULL;
  entity assigned = NULL;

  // this is a partial O(n) implementation
  // beware that we may have VERY LONG sequences...
  FOREACH(statement, s, sequence_statements(sq))
  {
    bool tocheck = true;
    entity red = freia_reduction_variable(s);
    if (red)
    {
      if (previous_reduction && assignment && red==previous_variable)
      {
        // matched!
        // replace variable in first reduction
        hash_table replacements = hash_table_make(hash_pointer, 0);
        hash_put(replacements, previous_variable, assigned);
        replace_entities(previous_reduction, replacements);
        hash_table_free(replacements);
        // and now useless remove assignment
        free_instruction(statement_instruction(assignment));
        statement_instruction(assignment) = make_continue_instruction();
        // make assigned NOT a register... just in case
        variable v = type_variable(entity_type(assigned));
        variable_qualifiers(v) = remove_register(variable_qualifiers(v));
        // we did something
        *changed = true;
      }

      // restart current status with new found reduction
      previous_reduction = s;
      previous_variable = red;
      assignment = NULL;
      assigned = NULL;
      tocheck = false;
    }

    // detect reduction variable assignment
    if (previous_reduction && !assignment &&
        instruction_assign_p(statement_instruction(s)))
    {
      list args = call_arguments(instruction_call(statement_instruction(s)));
      expression e1 = EXPRESSION(CAR(args)), e2 = EXPRESSION(CAR(CDR(args)));
      if (expression_reference_p(e1) && expression_reference_p(e2) &&
          reference_variable(expression_reference(e2))==previous_variable)
      {
        assignment = s;
        assigned = reference_variable(expression_reference(e1));
        tocheck = false;
      }
    }

    if (tocheck && previous_variable && variable_is_used(s, previous_variable))
    {
      // full cleanup
      previous_reduction = NULL;
      previous_variable = NULL;
      assignment = NULL;
      assigned = NULL;
    }
  }
}

bool freia_remove_scalar_ww_deps(const string module)
{
  debug_on("PIPS_HWAC_DEBUG_LEVEL");
  pips_debug(1, "considering module %s\n", module);

  // else do the stuff
  statement mod_stat =
    (statement) db_get_memory_resource(DBR_CODE, module, true);
  set_current_module_statement(mod_stat);
  set_current_module_entity(module_name_to_entity(module));

  // do the job
  bool changed = false;
  gen_context_recurse(mod_stat, &changed,
                      sequence_domain, gen_true2, sww_seq_rwt);

  // update database if changed
  if (changed)
    // stmt_renumber(mod_stat); module_reorder(mod_stat);
    DB_PUT_MEMORY_RESOURCE(DBR_CODE, module, mod_stat);

  reset_current_module_statement();
  reset_current_module_entity();
  debug_off();
  return true;
}

/********************************************** CLEANUP SOME SCALAR POINTERS */
/*
  // this break assumptions about "simple" deps made in the freia compiler
  int * foo;  // declaration
  foo = &bla; // only definition
  *foo = XXX; // only use

  // remove declaration & definition, and replace assign by
  bla = XXX;
*/

typedef struct {
  // entity -> entity
  hash_table points_to;
  // entity -> statement
  // hash_table declared;
  // entity -> call
  hash_table defined;
  // entity -> expression
  hash_table dereferenced;
  // of entities
  set candidates;
  set invalidated;
} rssp_ctx;

/* "&v"? return v, else return NULL
 */
static entity address_of_scalar(expression e)
{
  if (!expression_call_p(e)) return NULL;
  call c = expression_call(e);
  if (!ENTITY_ADDRESS_OF_P(call_function(c))) return NULL;
  list la = call_arguments(c);
  pips_assert("one argument to &", gen_length(la)==1);
  expression a = EXPRESSION(CAR(la));
  if (!expression_reference_p(a)) return NULL;
  reference r = expression_reference(a);
  if (reference_indices(r)) return NULL;
  entity v = reference_variable(r);
  if (entity_scalar_p(v))
    return v;
  return NULL;
}

static bool pointer_candidate_p(entity var)
{
  // other checks?
  pips_debug(5, "entity %s %d\n", entity_name(var), entity_pointer_p(var));
  return entity_pointer_p(var);
}

static void rssp_ref(reference r, rssp_ctx * ctx)
{
  string what = "unknown";
  entity var = reference_variable(r);
  pips_debug(8, "reference %p to %s\n", r, entity_name(var));
  if (pointer_candidate_p(var) && !reference_indices(r))
    set_add_element(ctx->candidates, ctx->candidates, var);
  if (set_belong_p(ctx->candidates, var))
  {
    expression enc = (expression) gen_get_ancestor(expression_domain, r);
    if (enc && expression_reference_p(enc) && expression_reference(enc)==r)
    {
      call called = (call) gen_get_ancestor(call_domain, enc);

      pips_debug(8, "called=%p %s\n", called, called?
                 entity_name(call_function(called)): "<nope>");

      if (called &&
          ENTITY_ASSIGN_P(call_function(called)) &&
          EXPRESSION(CAR(call_arguments(called)))==enc)
      {
        // is it a definition: var = ...
        list args = call_arguments(called);
        pips_assert("2 args to assign", gen_length(args)==2);
        entity v2 =
          address_of_scalar(EXPRESSION(CAR(CDR(call_arguments(called)))));
        if (v2)
        {
          if (!hash_defined_p(ctx->points_to, var))
            hash_put(ctx->points_to, var, v2),
              hash_put(ctx->defined, var, called),
              what="! var = &YYY";
          else
            set_add_element(ctx->invalidated, ctx->invalidated, var),
              what="already defined";
        }
        else
          set_add_element(ctx->invalidated, ctx->invalidated, var),
            what="no v2";
      }
      else if (called && ENTITY_DEREFERENCING_P(call_function(called)))
      {
        // *var ...
        call upper = (call) gen_get_ancestor(call_domain, called);
        expression first = (upper && call_arguments(upper))?
          EXPRESSION(CAR(call_arguments(upper))): NULL;

        pips_debug(8, "upper=%p first=%p %s\n", upper, first, upper?
                   entity_name(call_function(upper)): "<nope>");

        if (upper && first &&
            ENTITY_ASSIGN_P(call_function(upper)) &&
            expression_call_p(first) &&
            expression_call(first) == called &&
            !hash_defined_p(ctx->dereferenced, var))
          // *var = XXX
          hash_put(ctx->dereferenced, var, first),
            what="! *var = XXX";
        else
          set_add_element(ctx->invalidated, ctx->invalidated, var),
            what="not *var = ...";
      }
      else
        set_add_element(ctx->invalidated, ctx->invalidated, var),
          what="not = or *";
    }
    else
      set_add_element(ctx->invalidated, ctx->invalidated, var),
        what="not enc";
  }
  else
    what="not candidate";
  pips_debug(5, "candidate %s: %s\n", entity_name(var), what);
  //return true;
}

bool remove_simple_scalar_pointers(const string module)
{
  debug_on("PIPS_HWAC_DEBUG_LEVEL");
  pips_debug(1, "considering module %s\n", module);

  // else do the stuff
  statement mod_stat =
    (statement) db_get_memory_resource(DBR_CODE, module, true);
  set_current_module_statement(mod_stat);
  set_current_module_entity(module_name_to_entity(module));

  rssp_ctx ctx;
  ctx.candidates = set_make(set_pointer);
  ctx.points_to = hash_table_make(hash_pointer, 0);
  ctx.defined = hash_table_make(hash_pointer, 0);
  ctx.dereferenced = hash_table_make(hash_pointer, 0);
  ctx.invalidated = set_make(set_pointer);

  // get candidates
  FOREACH(entity, var, entity_declarations(get_current_module_entity()))
  {
    if (pointer_candidate_p(var))
    {
      set_add_element(ctx.candidates, ctx.candidates, var);
      if (value_expression_p(entity_initial(var)))
      {
        expression e = value_expression(entity_initial(var));
        entity v2 = address_of_scalar(e);
        if (v2)
        {
          hash_put(ctx.points_to, var, v2);
          hash_put(ctx.defined, var, expression_call(e));
        }
      }
    }
  }


  // check condition
  gen_context_multi_recurse
    (mod_stat, &ctx,
     reference_domain, gen_true, rssp_ref,
     // ignore sizeof
     sizeofexpression_domain, gen_false, gen_null,
     NULL);

  bool changed = false;
  // apply transformation
  SET_FOREACH(entity, var, ctx.candidates)
  {
    pips_debug(2, "considering entity %s inv=%d dr=%d def=%d pt=%d\n",
               entity_name(var), set_belong_p(ctx.invalidated, var),
               hash_defined_p(ctx.dereferenced, var),
               hash_defined_p(ctx.defined, var),
               hash_defined_p(ctx.points_to, var));

    if (!set_belong_p(ctx.invalidated, var) &&
        hash_defined_p(ctx.dereferenced, var) &&
        hash_defined_p(ctx.defined, var) &&
        hash_defined_p(ctx.points_to, var))
    {
      changed = true;
      // replace use
      expression deref = (expression) hash_get(ctx.dereferenced, var);
      expression_syntax(deref) = make_syntax_reference
        (make_reference((entity) hash_get(ctx.points_to, var), NIL));
      // drop definition
      call definition = (call) hash_get(ctx.defined, var);
      gen_free_list(call_arguments(definition)),
        call_arguments(definition) = NIL;
      call_function(definition) = make_integer_constant_entity(0);
      // declaration cleanup?
    }
  }

  // result
  if (changed)
    DB_PUT_MEMORY_RESOURCE(DBR_CODE, module, mod_stat);

  // cleanup
  set_free(ctx.candidates);
  set_free(ctx.invalidated);
  hash_table_free(ctx.points_to);
  hash_table_free(ctx.dereferenced);
  hash_table_free(ctx.defined);
  reset_current_module_statement();
  reset_current_module_entity();
  debug_off();

  return true;
}

/************************************************************ SHUFFLE FORWARD */
/*
 * Move forward image pointer assignments and cleanup... that is change
 *
 *   y = x;
 *   z = y;
 *   op(z);
 *
 * to:
 *
 *   op(x);
 *
 * This kind of simple image shuffling is generated by function inlining,
 * especially image returning functions from smil to freia conversion.
 * The code is too simplistic, it should rely on effects...
 *
 * TODO: handle declaration & initialization
 */

typedef struct {
  int changed;           // number of substitutions
  int removed;           // number of removed assignments
  list assigns;          // list of found image assignments
  hash_table equal;      // entity -> entity
} shuffle_context;

#define starts_with(s1, s2) (strncmp(s1, s2, strlen(s2))==0) /* a la java */

#define entity_update_p(e)                                             \
  (ENTITY_MULTIPLY_UPDATE_P(e) || ENTITY_DIVIDE_UPDATE_P(e) ||         \
   ENTITY_MODULO_UPDATE_P(e) || ENTITY_PLUS_UPDATE_P(e) ||             \
   ENTITY_MINUS_UPDATE_P(e) || ENTITY_LEFT_SHIFT_UPDATE_P(e) ||        \
   ENTITY_RIGHT_SHIFT_UPDATE_P(e) || ENTITY_BITWISE_AND_UPDATE_P(e) || \
   ENTITY_BITWISE_XOR_UPDATE_P(e) || ENTITY_BITWISE_OR_UPDATE_P(e))

// only visit = and freia functions (what about others? gen_true???)
static bool sio_call_flt(call c, _UNUSED_ shuffle_context *ctx)
{
  entity f = call_function(c);
  return ENTITY_ASSIGN_P(f) || entity_update_p(f) ||
    hwac_freia_api(entity_local_name(f)) != NULL ||
    // hmmm... also freia_common_ functions
    starts_with(entity_local_name(f), "freia_common_");
}

// substitute with image assignment in reference
static void sio_ref_rwt(reference r, shuffle_context *ctx)
{
  if (reference_indices(r) != NIL)
    return;
  entity v = reference_variable(r);
  if (hash_defined_p(ctx->equal, v))
  {
    reference_variable(r) = hash_get(ctx->equal, v);
    ctx->changed++;
  }
}

// substititute images in some cases
static void substitute_image_occurrences(void * s, shuffle_context *ctx)
{
  gen_context_multi_recurse(s, ctx,
                            call_domain, sio_call_flt, gen_null,
                            reference_domain, gen_true, sio_ref_rwt,
                            NULL);
}

/*
 * Forward substitute simple image pointer assignments in a sequence.
 *
 * TODO: deal with declaration initialization
 */
static void seq_rwt(sequence sq, shuffle_context * ctx)
{
  ctx->equal = hash_table_make(hash_pointer, 10);

  FOREACH(statement, s, sequence_statements(sq))
  {
    if (statement_call_p(s))
    {
      call c = statement_call(s);
      list args = call_arguments(c);
      if (ENTITY_ASSIGN_P(call_function(c)))
      {
        // ... = ...
        pips_assert("2 arguments", gen_length(args)==2);
        expression e1 = EXPRESSION(CAR(args)), e2 = EXPRESSION(CAR(CDR(args)));
        if (expression_reference_p(e1))
        {
          entity v1 = expression_variable(e1);
          if (freia_image_variable_p(v1))
          {
            // is the second image an image?
            entity v2 = NULL;
            if (expression_reference_p(e2))
            {
              v2 = expression_variable(e2);
              if (!freia_image_variable_p(v2))
                v2 = NULL;
            }

            // img = ...
            // cleanup all equalities with img, but not on img=img
            if (v1 != v2)
            {
              list delete = CONS(entity, v1, NIL);
              HASH_FOREACH(entity, k, entity, v, ctx->equal)
                // maybe could replace by other equal if any?
                if (v == v1)
                  delete = CONS(entity, k, delete);
              FOREACH(entity, e, delete)
                (void) hash_del(ctx->equal, e);
              gen_free_list(delete), delete = NIL;
            }

            // image assignement
            if (v2 != NULL)
            {
              // img1 = img2
              ctx->assigns = CONS(statement, s, ctx->assigns);
              if (v1 != v2) // distinct images
              {
                // point to prior image if any
                if (hash_defined_p(ctx->equal, v2))
                {
                  entity end = hash_get(ctx->equal, v2);
                  reference_variable(expression_reference(e2)) = end;
                  hash_put(ctx->equal, v1, end);
                }
                else
                  hash_put(ctx->equal, v1, v2);
              }
              // else skip silently "img = img;"
            }
            // else no image on rhs
          }
          else // not image assignment
          {
            substitute_image_occurrences(e2, ctx);
          }
        }
      }
      else // a call, but not an assignment
      {
        substitute_image_occurrences(s, ctx);
      }
    }
    else // not a call
    {
      // hmmm... safe option for now, cleanup current equalities
      // ??? could keep those on which there is no effect?
      hash_table_clear(ctx->equal);
    }
  }
  hash_table_free(ctx->equal); ctx->equal = NULL;
}

// count use references, but left part of assignments is skipped
static void ref_count_rwt(reference r, hash_table counts)
{
  entity v = reference_variable(r);
  if (freia_image_variable_p(v))
  {
    if (hash_defined_p(counts, v))
    {
      _int count = (_int) hash_get(counts, v) + 1;
      hash_update(counts, v, (void *) count);
    }
    else
      hash_put(counts, v, (void *) (_int) 1);
  }
}

// skip left part of assignments, or useless assignments
static bool call_count_flt(call c, _UNUSED_ hash_table counts)
{
  if (ENTITY_ASSIGN_P(call_function(c)))
  {
    list args = call_arguments(c);
    pips_assert(gen_length(args) == 2, "2 args to assign");
    expression e1 = EXPRESSION(CAR(args));
    if (expression_reference_p(e1))
    {
      reference r1 = expression_reference(e1);
      gen_recurse_stop(r1);
      // deal with x = x
      expression e2 = EXPRESSION(CAR(CDR(args)));
      if (expression_reference_p(e2))
      {
        reference r2 = expression_reference(e2);
        if (reference_variable(r1) == reference_variable(r2) &&
            reference_indices(r1) == NIL &&
            reference_indices(r2) == NIL)
          return false;
      }
    }
  }
  return true;
}

void freia_shuffle_move_forward(statement s)
{
  shuffle_context ctx = { 0, 0, NIL, NULL };
  // forward substitude simple image assignments
  gen_context_recurse(s, &ctx, sequence_domain, gen_true2, seq_rwt);
  // remove image assignments that are not used
  // TODO ??? initializations...
  // count image read references
  hash_table reads = hash_table_make(hash_pointer, 100); // entity -> _int
  gen_context_multi_recurse(s, reads,
                            call_domain, call_count_flt, gen_null2,
                            reference_domain, gen_true2, ref_count_rwt,
                            NULL);
  // cleanup assignments of unused images
  FOREACH(statement, sa, ctx.assigns)
  {
    // be safe
    pips_assert(statement_call_p(sa), "statement is a call");
    call c = statement_call(sa);
    pips_assert(ENTITY_ASSIGN_P(call_function(c)), "call is assign");
    list args = call_arguments(c);
    pips_assert(gen_length(args) == 2, "2 args to assign");
    expression e1 = EXPRESSION(CAR(args));
    pips_assert(expression_reference_p(e1), "expr is reference");
    reference r = expression_reference(e1);
    entity img = reference_variable(r);
    pips_assert(reference_indices(r) == NIL, "no array reference");
    pips_assert(freia_image_variable_p(img), "reference an image");

    // cleanup unused images
    if (!hash_defined_p(reads, img))
    {
      // remove assignment of unused image pointer
      free_instruction(statement_instruction(sa));
      statement_instruction(sa) = make_continue_instruction();
      // coldly cleanup corresponding effects... (free effects not needed?)
      delete_cumulated_rw_effects(sa);
      store_cumulated_rw_effects_list(sa, NIL);
      // ??? what about proper effects?
      // stats
      ctx.removed ++;
    }
  }
  hash_table_free(reads), reads = NULL;

  // be verbose because I'm not sure of the pass
  if (ctx.changed != 0 || ctx.removed != 0)
    pips_user_warning("%d subsitution(s) and %d assignment(s) removed",
                      ctx.changed, ctx.removed);

  gen_free_list(ctx.assigns), ctx.assigns = NIL;
}
