/*

  $Id: static.c 23065 2016-03-02 09:05:50Z coelho $

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
/* static variables and related access functions concerning the current module
 *
 * Be'atrice Apvrille, august 27, 1993
 */

/* used to store the summary transformer ?
   to retrieve intraprocedural effects ? */

#include <stdio.h>
#include <string.h>

#include "linear.h"

#include "genC.h"
#include "misc.h"

#include "ri.h"
#include "ri-util.h"


/*********************************************************** CURRENT ENTITY */

static entity current_module_entity = entity_undefined;
static list current_module_declaration_list=list_undefined;

/** @defgroup current_module Methods related to the current module

    Many parts of PIPS guesses that a current module is defined.

    These methods are used to set or get the module statement, entity, name...

    @{
*/

/** Set the current module entity

    It returns also the given entity to ease macro writing
*/
entity
set_current_module_entity(entity e)
{
    pips_assert("entity is a module", entity_module_p(e));

    /* FI: I should perform some kind of memorization for all static variables
       including the value maps (especially them) */

    pips_assert("current module is undefined",
		entity_undefined_p(current_module_entity));

    current_module_entity = e;
    reset_current_module_declarations();
    return e;
}


/** Get the entity of the current module
 */
entity
get_current_module_entity()
{
    return current_module_entity;
}



/** Reset the current module entity

    It asserts the module entity was previously set.
 */
void
reset_current_module_entity()
{
    pips_assert("current entity defined",
		!entity_undefined_p(current_module_entity));
    current_module_entity = entity_undefined;
    reset_current_module_declarations();
}

/** @} */

/* To be called by an error management routine only */
void
error_reset_current_module_entity()
{
    current_module_entity = entity_undefined;
    reset_current_module_declarations();
}


/** @addtogroup current_module
    @{
*/

/** Get the name of the current module */
const char* get_current_module_name()
{
  if(entity_undefined_p(current_module_entity))
    return string_undefined;
  else
    return module_local_name(current_module_entity);
  /* return entity_user_name(current_module_entity); */
}


void set_current_module_declarations(list l)
{
  current_module_declaration_list = l;
}

void reset_current_module_declarations()
{
  current_module_declaration_list = list_undefined;
}

list get_current_module_declarations()
{
  return current_module_declaration_list;
}

/** @} */


/******************************************************* CURRENT STATEMENT */

/* used to retrieve the intraprocedural effects of the current module */

static statement current_module_statement = statement_undefined;
static statement stacked_current_module_statement = statement_undefined;

/** @addtogroup current_module
    @{
*/

/** Set the current module statement

    It returns also the given statement to ease macro writing
*/
statement
set_current_module_statement(statement s)
{
  pips_assert("The current module statement is undefined",
	      current_module_statement == statement_undefined);
  pips_assert("The new module statement is not undefined",
	      s != statement_undefined);
  current_module_statement = s;
  reset_current_module_declarations();
  return s;
}


/** Set the statement of the current module and push the statement of the
    previous one on a stack
 */
void push_current_module_statement(statement s)
{
    pips_assert("The stacked_current module statement is undefined", 
		stacked_current_module_statement == statement_undefined);
    pips_assert("The new module statement is not undefined", 
		s != statement_undefined);
    stacked_current_module_statement = current_module_statement;
    current_module_statement = s;
}


/** Pop the current module statement stack and use it as the current
    module statement
 */
void pop_current_module_statement(void)
{
    pips_assert("The current module statement is undefined",
		current_module_statement != statement_undefined);
    current_module_statement = stacked_current_module_statement;
    stacked_current_module_statement = statement_undefined;
}


/** Get the current module statement

    It returns also the given statement to ease macro writing
*/
statement
get_current_module_statement()
{
  pips_assert("The current module statement is defined",
	      current_module_statement != statement_undefined);
  return current_module_statement;
}


/** Reset the current module statement

    It asserts the module statement was previously set.
 */
void
reset_current_module_statement()
{
  pips_assert("current module statement defined",
	      !statement_undefined_p(current_module_statement));
  current_module_statement = statement_undefined;
  reset_current_module_declarations();
}

/** @} */


/* To be called by an error management routine only */
void
error_reset_current_module_statement()
{
    current_module_statement = statement_undefined;
    stacked_current_module_statement = statement_undefined;
    reset_current_module_declarations();
}

/* Because of typedefs, the C lexers need help to decide if a
 * character string such as toto is a type name or a keyword or an identifier.
 * 
 * Such a table is used by the C preprocessor and by the C parser. It
 * is also updated for in- or outlining with new typedef names.
 *
 * The table must be initialized with token values generated by
 * bison. The token values could possibly be different for the PIPS
 * preprocessor and syntactic analyzer. Each has its own
 * initialization function, parser_init_keyword_typedef_table() and
 * preprocessor_init_keyword_table().
 */
hash_table keyword_typedef_table = hash_table_undefined;
static int token_named_type = -1;

hash_table make_keyword_typedef_table(int tk)
{
  token_named_type = tk;
  keyword_typedef_table = hash_table_make(hash_string,0);
  return keyword_typedef_table;
}

void set_keyword_typedef_table(hash_table h)
{
  keyword_typedef_table = h;
}

void reset_keyword_typedef_table()
{
  keyword_typedef_table = hash_table_undefined;
  // No need to reset this value. It is a constant defined by Bison.
  // token_named_type = -1;
}

void free_keyword_typedef_table()
{
  hash_table_free(keyword_typedef_table);
  keyword_typedef_table = hash_table_undefined;
  // No need to reset this value. It is a constant defined by Bison.
  // token_named_type = -1;
}

void declare_new_typedef(const string tn)
{
  hash_put(keyword_typedef_table, strdup(tn), (const void *) ((long long int) token_named_type));
}

/* This function checks if s is a C keyword or typedef name and
 * returns the token number thanks to the hash-table
 * keyword_typedef_table.
 *
 * It returns an integer number corresponding to the keyword.
 *
 * It returns 0 if s is not a keyword/typedef name
 */
_int
is_c_keyword_typedef(char * s)
{
  _int i = (_int) hash_get(keyword_typedef_table,s);
  return ((char *) i == HASH_UNDEFINED_VALUE) ? 0: i;
}
/*********
 * Begin definition for the stack current_statement_global_stack
 *
 * Because Newgen makes it easy to define a statement stack using
 * DEFINE_LOCAL_STACK(), the very same functions are redefined each
 * time they are needed (transformations/sequence_gcm_cse.s,
 * transformations/simple_atomizer.c, hpfc/io-util.c,
 * instrumentation/alias_propagation.c,
 * transformations/array_resizing_top_down.c and
 * transformations/dead_code_elimination.c). And because they are
 * defined by macro-expansion, they are a pain to use for debugging
 * with gdb.
 */

static stack statement_global_stack = stack_undefined;

void make_statement_global_stack()
{
  /* This assert is too strong when user errors occur. Each pass
   * should pprovide a "clean-up" function to be called by
   * user_error() without creating a library cycle
   */
  //pips_assert("statement_global_stack is undefined",
  //              stack_undefined_p(statement_global_stack));
  if(!stack_undefined_p(statement_global_stack)) {
    /* This is an error recovery */
    free_statement_global_stack();
  }
  statement_global_stack = stack_make(statement_domain, 0, 0);
}

void push_statement_on_statement_global_stack(statement st)
{
  stack_push((void *) st, statement_global_stack);
}

//static int get_current_statement_line_number()
//{
//  statement st = (statement) stack_head(statement_global_stack));
//  return statement_number(st);
//}

statement get_current_statement_from_statement_global_stack()
{
  statement st = statement_undefined;
  if(!stack_empty_p(statement_global_stack))
    st = (statement) stack_head(statement_global_stack);
  return st;
}

statement pop_statement_global_stack(void)
{
  statement st = (statement) stack_pop(statement_global_stack);
  return st;
}

void free_statement_global_stack()
{
  stack_free(&statement_global_stack);
  statement_global_stack = stack_undefined;
}

bool statement_global_stack_defined_p()
{
  return !stack_undefined_p(statement_global_stack);
}

/*********
 * End definition for the stack statement_global_stack
 */
