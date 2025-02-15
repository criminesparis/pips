/*

  $Id: declarations.c 23495 2018-10-24 09:19:47Z coelho $

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

static void remove_unread_variable(statement s, entity e)
{
  if(statement_call_p(s)&&!declaration_statement_p(s))
  {
        list effects = load_cumulated_rw_effects_list(s);
        bool entity_written = false;
        FOREACH(EFFECT,eff,effects)
            if(effect_write_p(eff) && entities_must_conflict_p(reference_variable(effect_any_reference(eff)),e))
            { entity_written = true; break; }
        if(entity_written) /* we only manage written entity in the form of e binary_op something else */
        {
            call c = statement_call(s);
            expression lhs = binary_call_lhs(c);
            if(expression_reference_p(lhs) && entities_may_conflict_p(reference_variable(expression_reference(lhs)),e))
            {
                list next = CDR(call_arguments(c));
                if(ENDP(next))
                    call_function(c) = entity_intrinsic(CONTINUE_FUNCTION_NAME);
                else if( ENDP(CDR(next)) ) {
                    expression rhs =  binary_call_rhs(c);
                    if(expression_call_p(rhs))
                    {
                        call new_c = expression_call(rhs);
                        syntax_call(expression_syntax(rhs))=call_undefined;
                        free_call(c);
                        instruction_call(statement_instruction(s))=new_c;
                    }
                    else {
                        expression exp = copy_expression(rhs);
                        free_instruction(statement_instruction(s));
                        statement_instruction(s)=make_instruction_expression(exp);
                    }
                }
                else {
                    pips_internal_error("case unhandled yet\nfell free to contribute :-)");
                }
            }
        }

    }
}
static bool entity_may_conflict_with_a_formal_parameter_p(entity e, entity module)
{
    FOREACH(entity,d,entity_declarations(module))
        if(formal_parameter_p(d) && entities_may_conflict_p(e,d)) return true;
    return false;
}

typedef struct {
    entity e;
    bool result;
} entity_used_somewhere_param;

static void entity_used_somewhere_walker(statement s, entity_used_somewhere_param *p)
{
    list effects =load_cumulated_rw_effects_list(s);
    if(effects_read_variable_p(effects,p->e))
        { p->result = true; gen_recurse_stop(0); }
}

static bool entity_read_somewhere_p(entity e, statement in)
{
    entity_used_somewhere_param p = { e, false };
    gen_context_recurse(in,&p,statement_domain,gen_true2,entity_used_somewhere_walker);
    return p.result;
}
static void remove_unread_variables(statement s)
{
    if(statement_block_p(s))
    {
        FOREACH(ENTITY,e,statement_declarations(s))
        {
            if(entity_variable_p(e)) {
                if(!entity_may_conflict_with_a_formal_parameter_p(e,get_current_module_entity()) && /* it is useless to try to remove formal parameters */
                        entity_scalar_p(e) ) /* and we cannot afford removing something that may implies aliasing */
                {
                    bool effects_read_variable = entity_read_somewhere_p(e,s);
                    if(!effects_read_variable) {
                        /* the entity is never read, it is disposable */
                        pips_debug(4,"Entity %s is never read, we can remove "
                                   "statements that only produce it.\n",
                                   entity_name(e));
                        gen_context_recurse(s,e,statement_domain,gen_true2,remove_unread_variable);
                    }
                }
            }
        }
    }
}

void module_clean_declarations(entity module, statement module_statement) {
  entity_clean_declarations(module,module_statement);

  gen_recurse(module_statement,statement_domain, gen_true, statement_clean_declarations);
}

/* A phase to remove the declaration of useless variables

   It recursively calls statement_remove_unused_declarations on all module
   statement

   @param[in] module_name is the name of the module to process

   @return true because always successful
*/
bool clean_declarations(const string module_name)
{
  /* prelude */
  set_current_module_entity(module_name_to_entity( module_name ));
  set_current_module_statement((statement) db_get_memory_resource(DBR_CODE, module_name, true) );
  set_cumulated_rw_effects((statement_effects)db_get_memory_resource(DBR_CUMULATED_EFFECTS,module_name,true));

  debug_on("CLEAN_DECLARATIONS_DEBUG_LEVEL");

  /* first remove any statement that writes only variable that are never read */
  gen_recurse(get_current_module_statement(),statement_domain,gen_true,remove_unread_variables);

  /* body*/
  module_clean_declarations(get_current_module_entity(),get_current_module_statement());

  DB_PUT_MEMORY_RESOURCE(DBR_CODE, module_name, get_current_module_statement());

  debug_off();

  /*postlude */
  reset_cumulated_rw_effects();
  reset_current_module_entity();
  reset_current_module_statement();
  return true;
}

