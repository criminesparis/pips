/*

  $Id: statement.c 23489 2018-10-22 09:12:55Z coelho $

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
    Function for statement, and its subtypes:
     - instruction
  */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>

#include "linear.h"
#include "genC.h"

#include "misc.h"
#include "properties.h"

#include "ri-util.h"
#include "text-util.h"

#include "prettyprint.h"

void print_statement_set(FILE * fd, set r)
{
    fprintf(fd, "Set contains statements");

    SET_MAP(s, {
	fprintf(fd, " %02td", statement_number((statement) s));
    }, r);

    fprintf(fd, "\n");
}


/** Print statement "s" on file descriptor "fd"

    Print the statement according to the current PRETTYPRINT_LANGUAGE
    property

    See text_named_module() for improvements.
*/
void fprint_statement(FILE * fd, statement s)
{
  if(statement_undefined_p(s))
    fprintf(fd, "Undefined statement\n");
  // For debugging with gdb, dynamic type checking
  else if(statement_domain_number(s)!=statement_domain)
    (void) fprintf(fd,"Arg. \"s\"is not a statement.\n");
  else {
    debug_on("TEXT_DEBUG_LEVEL");
    set_alternate_return_set();
    reset_label_counter();
    push_current_module_statement(s);
    list pdl = NIL;
    text txt = text_statement(entity_undefined, 0, s, &pdl);
    gen_free_list(pdl);
    print_text(fd, txt);
    free_text(txt);
    pop_current_module_statement();
    reset_alternate_return_set();
    debug_off();
  }
}

/** Print a statement on stderr

    Print the statement according to the current PRETTYPRINT_LANGUAGE
    property

    See text_named_module() for improvements.
*/
void print_statement(statement s)
{
  fprint_statement(stderr, s);
}

void print_statements(list sl)
{
  FOREACH(STATEMENT, s, sl) {
    print_statement(s);
  }
}


void print_statement_of_module(statement s, const char* mn)
{
  if(entity_undefined_p(get_current_module_entity())) {
    entity m = local_name_to_top_level_entity(mn);
    set_current_module_entity(m);
    reset_label_counter();
    print_statement(s);
    reset_current_module_entity();
  }
  else
    print_statement(s);
}

text statement_to_text(statement s)
{
  text t = text_undefined;

  debug_on("PRETTYPRINT_DEBUG_LEVEL");
  set_alternate_return_set();
  reset_label_counter();
  list pdl = NIL;
  t = text_statement(entity_undefined, 0, s, &pdl);
  gen_free_list(pdl);
  reset_alternate_return_set();
  debug_off();

  return t;
}

void safe_print_statement(statement s)
{
  if(statement_undefined_p(s)) {
    fprintf(stderr, "Statement undefined\n");
  }
  else if(continue_statement_p(s)
     && entity_return_label_p(statement_label(s))) {
    /* The return label only can be associated to a RETURN call,
       however the controlizer does not follow this consistency
       rule. */
    fprintf(stderr, "%s\n", statement_identification(s));
  }
  else
    print_statement(s);
}

void print_parallel_statement(statement s)
{
  string cstyle = strdup(get_string_property(PRETTYPRINT_PARALLEL));
  set_string_property(PRETTYPRINT_PARALLEL, "doall");
  print_statement(s);
  set_string_property(PRETTYPRINT_PARALLEL, cstyle);
  free(cstyle);
}

/* A simplified version of find_last_statement() located in
 * prettyprint.c and designed to be used within the prettyprinter
 */
statement last_statement(statement s)
{
    statement last = statement_undefined;

    pips_assert("statement is defined", !statement_undefined_p(s));

    if(statement_sequence_p(s)) {
	list ls = instruction_block(statement_instruction(s));

	last = (ENDP(ls)? statement_undefined :
		last_statement(STATEMENT(CAR(gen_last(ls)))));
    }
    else if(statement_unstructured_p(s)) {
	unstructured u = statement_unstructured(s);
	list trail = unstructured_to_trail(u);

	last = control_statement(CONTROL(CAR(trail)));

	gen_free_list(trail);
    }
    else if(statement_call_p(s)) {
	/* Hopefully it is a return statement.
	 * Since the semantics of STOP is ignored by the parser, a
	 * final STOp should be followed by a RETURN.
	 */
	last = s;
    }
    else if(statement_goto_p(s))
      last = s;
    else if(statement_expression_p(s))
      last = s;
    else if(statement_loop_p(s))
      last = s;
    else if(statement_whileloop_p(s))
      last = s;
    else if(statement_forloop_p(s))
      last = s;

    return last;
}

void print_number_to_statement(hash_table nts)
{
    HASH_MAP(number, stmt, {
	fprintf(stderr,"%td\t", (_int) number);
	print_statement((statement) stmt);
    }, nts);
}


static bool find_statements_interactively_walker(statement s, list *l)
{
  string answer = string_undefined;
  do {
    while( string_undefined_p(answer) || empty_string_p(answer)  )
      {
	user_log("Do you want to pick the following statement ?\n"
		 "*********************************************\n");
	print_statement(s);

	answer = user_request(
			      "*********************************************\n"
			      "[y/n] ?"
			      );
	if( !answer ) pips_user_error("you did not answer !\n");
      }
    if( answer[0]!='y' && answer[0]!='n' )
      {
	pips_user_warning("answer by 'y' or 'n' !\n");
	free(answer);
	answer=string_undefined;
      }
  } while(string_undefined_p(answer));
  bool pick = answer[0]=='y';
  if(pick) {
    *l=CONS(STATEMENT,s,*l);
    return false;
  }
  else if( !ENDP(*l) )
    gen_recurse_stop(NULL);
  return true;
}

/**
 * prompt the user to select contiguous statement in s
 *
 * @param s statement to search into
 *
 * @return list of selected statement
 */
list find_statements_interactively(statement s)
{
  list l =NIL;
  gen_context_recurse(s,&l,statement_domain,find_statements_interactively_walker,gen_null2);
  return gen_nreverse(l);
}
