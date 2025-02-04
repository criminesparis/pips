/*

 $Id: strength_reduction.c 23495 2018-10-24 09:19:47Z coelho $

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

// do not compiled unless required
#include "phases.h"
#ifdef BUILDER_STRENGTH_REDUCTION

#ifdef HAVE_CONFIG_H
    #include "pips_config.h"
#endif
/* package induction_substitution
 */

#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#include "genC.h"
#include "linear.h"

#include "misc.h"
#include "pipsdbm.h"
#include "properties.h"

#include "ri.h"
#include "ri-util.h"
#include "text-util.h" // dump_text

#include "control.h" // clean_up_sequences, module_reorder

#include "transformer.h"     // used
#include "effects.h"         // used by semantics.h
#include "semantics.h"       // used
#include "effects-generic.h" // used

/* strength reduction context */
typedef struct {
    hash_table entity_to_coeff; ///< mapping between an entity and the value of the involved induction variable
    hash_table entity_to_entity; ///< mapping between an entity and its strength_reduced value
    entity index;               ///< induction variable
    expression increment;       ///< original loop increment
    expression init;            ///< original loop increment initial value
    list header_statements;     ///< assignments from external to internal var
    list incr_statements;       ///< the internal vars increments
} strength_reduction_context_t;

/* the big stuff is there
 * for each candidate expression, we examine its linear field and look for something
 * link a0.{variable}+a1.TCST+a2.{induction variable}+a3.{other symbolic constant}
 * we normalize this, and if it's ok, we can transform this into
 * a0'.{variable}+a1'.TCST+a3'.{other symbolic constant}
 * and increment by @p ctxt->increment * a2'
 * a new variable is created for each different increment
 */
static bool do_strength_reduction_gather(expression exp, strength_reduction_context_t *ctxt) {
    /* ensure the normalized field is filled */
    NORMALIZE_EXPRESSION(exp);
    normalized n = expression_normalized(exp);
    /* focus on the linear problem */
    if(normalized_linear_p(n) && VALUE_ZERO != vect_coeff(ctxt->index,normalized_linear(n)) ) {
        /* we look for a linear form involving constants and our index */
        entity other = entity_undefined;
        for(Pvecteur iter=normalized_linear(n);
                !VECTEUR_NUL_P(iter);iter=vecteur_succ(iter)) {
            entity var = (entity)vecteur_var(iter);
            /* constant terms and the index are ignored  */
            if(term_cst(iter) ||
                same_entity_p(ctxt->index,var) ||
                entity_constant_p(var)) {
                continue;
            }
            /* the others are stored, but only one per expression
             * eg: what to do with a + b +i ?
             * we also have to pay attention to 2a-6i: this one is ok,
             * it will lead to 2a; a-=3;
             * but not 3a-4i
             */
            else /*if(entity_undefined_p(other))*/ {
                Pvecteur pv = vect_copy(normalized_linear(n));
                vect_normalize(pv);
                Value v = vect_coeff(var,pv);
                if(value_one_p(v)&& // prefer pointer over scalars to hold the increment
                        (entity_undefined_p(other)||entity_scalar_p(other)||entity_pointer_p(other)))
                    other= var;
                //else {other=entity_undefined;};//do not manage this case as of now
            }
            /*else {
                other=entity_undefined;// cannot decide between two not constant entities
                break;
            }*/
        }
        /* we only take care of scalar variables */
        if(!entity_undefined_p(other) && (entity_scalar_p(other) || entity_pointer_p(other)) ) {
            /* look for an entity that olds the same increment as ours */
            entity already_there = entity_undefined;
            HASH_FOREACH(entity,e,intptr_t,v,ctxt->entity_to_coeff) {
                if(((intptr_t)vect_coeff(ctxt->index,normalized_linear(n))==v) &&
                        same_entity_p(other,(entity)hash_get(ctxt->entity_to_entity,e)))
                {
                    already_there=e;
                    break;
                }
            }
            Pvecteur pv = vect_copy(normalized_linear(n));
            if(entity_undefined_p(already_there)) {
                /* create a new induction variable */
                already_there=make_new_scalar_variable_with_prefix(
                        entity_user_name(other),get_current_module_entity(),
                        copy_basic(entity_basic(other))
                        );
                /* memorize it for further use:
                 * *(a+i)=(*a+1)+1;
                 * should lead to *a0=*a0+1; a0++;
                 * and not *a1=*a1+1; a1++;
                 */
                Value coeff = vect_coeff(ctxt->index,pv);
                hash_put(ctxt->entity_to_coeff,already_there,(void*)(intptr_t)coeff);
                hash_put(ctxt->entity_to_entity,already_there,other);
                AddEntityToCurrentModule(already_there);
                /* and fill the header / footer / increment */
                intptr_t v;
                ctxt->header_statements=CONS(
                        STATEMENT,
                        make_assign_statement(
                            entity_to_expression(already_there),
                            expression_integer_value(ctxt->init,&v) && v == 0 ?
                            entity_to_expression(other):
                            make_op_exp(
                                PLUS_C_OPERATOR_NAME,
                                entity_to_expression(other),
                                copy_expression(ctxt->init)
                                )
                            ),
                        ctxt->header_statements);
                /* compute the value of the new increment */
                expression new_increment=int_to_expression(coeff>0?coeff:-coeff);
                ctxt->incr_statements=CONS(
                        STATEMENT,
                        call_to_statement(
                            make_call(
                                entity_intrinsic(coeff>0?PLUS_UPDATE_OPERATOR_NAME:MINUS_UPDATE_OPERATOR_NAME),
                                make_expression_list(
                                    entity_to_expression(already_there),
                                    make_op_exp(MULTIPLY_OPERATOR_NAME,
                                        copy_expression(ctxt->increment),
                                        new_increment)
                                    )
                                )
                            ),
                        ctxt->incr_statements);

            }
            /* either way regenerate the expression from the patched linear field*/
            vect_erase_var(&pv,ctxt->index);
            vect_chg_var(&pv,other,already_there);
            expression p = Pvecteur_to_expression(pv);
            update_expression_syntax(exp,
                    expression_syntax(p)
                    );
            expression_syntax(p)=syntax_undefined;
            free_expression(p);
            return false;
        }
    }
    return true;
}

/* looks for expression in @p l's body that are linear combination of @p l's index
 * those expressions are strength reduced
 */
static bool do_strength_reduction_in_loop(loop l) {
    // parent statement
    statement s = (statement) gen_get_ancestor(statement_domain,l);
    // context
    strength_reduction_context_t ctxt = {
        hash_table_make(hash_pointer,HASH_DEFAULT_SIZE),
        hash_table_make(hash_pointer,HASH_DEFAULT_SIZE),
        loop_index(l),
        range_increment(loop_range(l)),
        range_lower(loop_range(l)),
        NIL,NIL
    };
    // find all possible & relevant cases and fill the context
    gen_context_recurse(loop_body(l), &ctxt,
            expression_domain, do_strength_reduction_gather, gen_null2);
    // insert prelude and postlude that take care of the assignment to the iterator
    // plus the increments
    insert_statement(s,
            make_block_statement(ctxt.header_statements),
            true);
    insert_statement(loop_body(l),
            make_block_statement(ctxt.incr_statements),
            false);

    hash_table_free(ctxt.entity_to_coeff);
    hash_table_free(ctxt.entity_to_entity);
    return true;
}

/* dispatch over all loops */
static
void do_strength_reduction(
  _UNUSED_ entity module,
  statement module_statement)
{
  gen_recurse(module_statement,
              loop_domain, do_strength_reduction_in_loop, gen_null);
}

/* this phase is the opposite of induction substitution:
 * it generates induction variables
 * It is a lame implementation without much smart things in it:
 * works only for loops, generates a lot of copy ...
 * But it does the job for the simple case I (SG) need in Terapix
 *
 *
 * after a talk with FI, it appears that transformers should be used
 * to detect induction variable
 *
 * deriving the preconditions with respect to induction variable should
 * also give insightful informations about the strength reduction pattern
 *
 * see paper from Robert Paije
*/
bool strength_reduction(const string module_name) {
    /* prelude */
    set_current_module_entity(module_name_to_entity(module_name));
    set_current_module_statement(
            (statement) db_get_memory_resource(DBR_CODE, module_name, true)
            );
    /* To set up the hash table to translate value into value names */
    set_cumulated_rw_effects((statement_effects)
            db_get_memory_resource(DBR_CUMULATED_EFFECTS, module_name, true)
            );
    /* do the job */
    do_strength_reduction(get_current_module_entity(),get_current_module_statement());
    // we may have done bad things, such has inserting empty statements
    clean_up_sequences(get_current_module_statement());

    /* some declaration statements may have been added */
    module_reorder(get_current_module_statement());
    DB_PUT_MEMORY_RESOURCE(DBR_CODE, module_name, get_current_module_statement());

    reset_semantic_map();
    reset_cumulated_rw_effects();
    reset_current_module_statement();
    reset_current_module_entity();
    return true;
}

#endif // BUILDER_STRENGTH_REDUCTION
