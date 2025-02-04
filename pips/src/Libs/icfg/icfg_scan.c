/*

  $Id: icfg_scan.c 23065 2016-03-02 09:05:50Z coelho $

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
   icfg_scan.c
   module_to_icfg(0, mod) recursively to_icfgs module "mod" and its callees
   and writes its icfg in indented form
*/
#include <stdio.h>
#include <string.h>

#include "genC.h"
#include "linear.h"

#include "properties.h"  // get_bool_property
#include "misc.h"
#include "pipsdbm.h"     // DB_PUT_FILE_RESOURCE

#include "ri.h"
#include "effects.h"
#include "text.h"

#include "text-util.h"
#include "ri-util.h"
#include "prettyprint.h" // for debugging

#include "control.h"      // CONTROL_MAP

#include "icfg.h"

// loops
#define st_DO		prettyprint_fortran_icfg_p ? "do " : "for "
#define st_ENDDO	prettyprint_fortran_icfg_p ? "enddo" : "}"
#define st_FOR		"for "
#define st_ENDFOR	"}"
#define st_DOWHILE	prettyprint_fortran_icfg_p ? "do while " : "while "
#define st_ENDDOWHILE	prettyprint_fortran_icfg_p ? "enddo" : "}"
#define st_REPEAT	prettyprint_fortran_icfg_p ? "repeat " : "do {"
#define st_UNTIL	prettyprint_fortran_icfg_p ? "until" : "} while ();"
// conditions
#define st_IF		prettyprint_fortran_icfg_p ? "if" : "if () {"
#define st_THEN		prettyprint_fortran_icfg_p ? "then" : ""
#define st_ELIF	       prettyprint_fortran_icfg_p ? "else if" : "} else if () {"
#define st_ELSE		prettyprint_fortran_icfg_p ? "else" : "} else {"
#define st_ENDIF	prettyprint_fortran_icfg_p ? "endif" : "}"
/* These last two strings are used for unstructured */
#define st_WHILE	prettyprint_fortran_icfg_p? "while": "while () {"
#define st_ENDWHILE	prettyprint_fortran_icfg_p? "endwhile": "}"

#define some_text_p(t) (t!=text_undefined && text_sentences(t)!=NIL)

/* We want to keep track of the current statement inside the recurse */
#define current_stmt_head() \
  ((statement) gen_get_ancestor(statement_domain, gen_get_current_object()))

/********************************************************** GLOBAL VARIABLES */

// indentation
#define ICFG_DEFAULT_INDENTATION (4)
static int icfg_indent = ICFG_DEFAULT_INDENTATION;

/* We store the text for each statement in a mapping during a code traversal
   in order to print it afterwards
*/
GENERIC_LOCAL_MAPPING(icfg, text, statement)

/* static drivers
 */
static bool
  print_loops = false,
  print_ifs = false,
  do_reset_current_module_entity_on_decoration = false,
  prettyprint_fortran_icfg_p = true,
  prettyprint_C_icfg_p = false;

static text (*module_decoration)(const string) = NULL;
static text (*precise_decoration)(entity, entity, statement, call) = NULL;

static text (*filter_decoration_call)(entity, statement, call) = NULL;
static text (*filter_decoration_stmt)(entity, statement) = NULL;

static int current_margin;

static list /* of vertex */ verlist = NIL; /* to make graph daVinci */
static vertex current_vertex = NULL; /* caller */

/***************************************************************** FUNCTIONS */

void icfg_set_indentation(int indent)
{
  icfg_indent = indent;
}

void icfg_reset_indentation(void)
{
  icfg_indent = ICFG_DEFAULT_INDENTATION;
}

void icfg_error_handler(void)
{
  // ???
}

static void append_marged_text(
    text t,
    int margin,
    const char* what1,
    const char* what2)
{
  char *buffer;
  asprintf(&buffer, "%*s%s%s\n", margin, "", what1, what2);
  ADD_SENTENCE_TO_TEXT(t, make_sentence(is_sentence_formatted, buffer));
}

/* STATEMENT
 */
static bool statement_flt(statement s)
{
  text t;

  pips_debug (5,"going down\n");

  /* process the not call statement to print out filtered proper effects */
  if (filter_decoration_stmt)
  {
    entity e_caller = get_current_module_entity();
    t = (*filter_decoration_stmt)(e_caller, s);
  }
  else
    t  = make_text (NIL);

  store_statement_icfg(s, t);
  return true;
}

static void statement_rwt(statement s)
{
  pips_debug (5,"going up\n");
  ifdebug(9) print_text(stderr,(text) load_statement_icfg (s));
  return;
}

/* CALL
 */
static void call_flt(call c)
{
  entity e_callee = call_function(c);
  const string callee_name = (const string) module_local_name(e_callee);

  pips_debug (5,"called entity is %s\n", entity_name(e_callee));

  /* If this is a "real function" (defined in the code elsewhere) */
  if (value_code_p(entity_initial(e_callee))) {
    text r = (text) load_statement_icfg (current_stmt_head());

    /* hum... pushes the current entity... */
    entity e_caller = get_current_module_entity();

    vertex ver_child = get_vertex_by_string(callee_name, verlist);
    if (ver_child != vertex_undefined)
      verlist = safe_make_successor(current_vertex, ver_child, verlist);

    // this hack is really needed...
    if (do_reset_current_module_entity_on_decoration)
      reset_current_module_entity();

    if (module_decoration)
      MERGE_TEXTS(r, (*module_decoration)(callee_name));
    else if (precise_decoration)
      MERGE_TEXTS(r,
          (*precise_decoration)(e_caller, e_callee, current_stmt_head(), c));
    else if (filter_decoration_call)
      MERGE_TEXTS(r,
                  (*filter_decoration_call)(e_caller, current_stmt_head(), c));

    // really needed, retrieve the caller entity
    if (do_reset_current_module_entity_on_decoration)
      set_current_module_entity(e_caller);

    /* append the callee' icfg */
    /*append_icfg_file (r, callee_name);*/
    append_marged_text(r, current_margin, CALL_MARK, callee_name);
    /* store it to the statement mapping */
    update_statement_icfg(current_stmt_head(), r);
  }
  return;
}

/* LOOP
 */
static bool loop_flt (loop __attribute__ ((unused)) l)
{
  pips_debug (5, "Loop begin\n");
  if (print_loops) current_margin += icfg_indent;
  return true;
}

static void anyloop_rwt(
    const char* st_what,
    const char* st_end_what,
    const char* st_index,
    statement body)
{
  text inside_the_loop = text_undefined,
    inside_the_do = text_undefined,
    t = make_text (NIL);
  bool text_in_do_p, text_in_loop_p;

  pips_debug (5,"Loop end\n");

  if (print_loops) current_margin -= icfg_indent;

  inside_the_do = (text) load_statement_icfg (current_stmt_head());
  text_in_do_p = some_text_p(inside_the_do);

  inside_the_loop = (text) load_statement_icfg (body);
  text_in_loop_p = some_text_p(inside_the_loop);

  /* Print the text inside do expressions (before the DO!)
   */
  if (text_in_do_p)
    {
      pips_debug(9, "something inside_the_do\n");
      MERGE_TEXTS (t, inside_the_do);
    }

  /* Print the DO
   */
  if ((text_in_loop_p || text_in_do_p) && print_loops)
    {
      if(prettyprint_fortran_icfg_p)
	append_marged_text(t, current_margin, st_what, st_index);
      else {
	string st_end =	string_undefined;
	asprintf(&st_end, "(%s) {", st_index);
	append_marged_text(t, current_margin, st_what, st_end);
	free(st_end);
      }
    }

  /* Print the text inside the loop
   */
  if (text_in_loop_p)
    {
      pips_debug(9, "something inside_the_loop\n");
      MERGE_TEXTS (t, inside_the_loop);
    }

  /* Print the ENDDO
   */
  if ((text_in_loop_p || text_in_do_p) && print_loops)
    {
      append_marged_text(t, current_margin, st_end_what, "");
    }

  /* store it to the statement mapping */
  update_statement_icfg (current_stmt_head(), t);

  return ;
}

static void loop_rwt(loop l)
{
  anyloop_rwt(st_DO, st_ENDDO, entity_user_name(loop_index(l)), loop_body(l));
}

static void forloop_rwt(forloop l)
{
  anyloop_rwt(st_FOR, st_ENDFOR, "", forloop_body(l));
}

static void while_rwt(whileloop w)
{
  evaluation e = whileloop_evaluation(w);

  if(evaluation_before_p(e))
    anyloop_rwt(st_DOWHILE, st_ENDDOWHILE, "", whileloop_body(w));
  else
    anyloop_rwt(st_REPEAT, st_UNTIL, "", whileloop_body(w));
}

/* INSTRUCTION
 */
static bool instruction_flt (instruction i)
{
  if(instruction_unstructured_p(i)
     && unstructured_while_p(instruction_unstructured(i))) {
    pips_debug (5, "While begin\n");
    if (print_loops) current_margin += icfg_indent;
  }
  return true;
}

static void instruction_rwt (instruction i)
{
  text t = make_text (NIL);
  bool text_in_unstructured_p = false;

  pips_debug (5,"going up\n");
  pips_debug (9,"instruction tag = %d\n", instruction_tag (i));

  switch (instruction_tag (i)) {
  case is_instruction_block:
    {
      pips_debug (5,"dealing with a block, appending texts\n");

      MAP(STATEMENT, s,
	  MERGE_TEXTS(t, load_statement_icfg(s)),
	  instruction_block(i));

      /* store it to the statement mapping */
      update_statement_icfg (current_stmt_head (), t);
      break;
    }
  case is_instruction_unstructured:
    {
      unstructured u = instruction_unstructured (i);
      list blocs = NIL ;
      control ct = unstructured_control(u) ;
      text inside_the_unstructured = make_text(NIL);
      bool while_p = false;

      pips_debug (5,"dealing with an unstructured, appending texts\n");

      if(unstructured_while_p(u)) {
	while_p = true;
	pips_debug (5,"dealing with a WHILE\n");
      }

      /* SHARING! Every statement gets a pointer to the same precondition!
	 I do not know if it's good or not but beware the bugs!!! */
      FORWARD_CONTROL_MAP(c, {
	  statement st = control_statement(c) ;
	  MERGE_TEXTS(inside_the_unstructured, load_statement_icfg (st));
	}, ct, blocs) ;

      gen_free_list(blocs) ;

      text_in_unstructured_p = some_text_p(inside_the_unstructured);

      /* Print the WHILE
       */
      if(print_loops && while_p) {
	current_margin -= icfg_indent;
	if(text_in_unstructured_p) {
	  append_marged_text(t, current_margin, st_WHILE, "");
	}
      }

      /* Print the text inside the unstructured (possibly the while body)
       */
      if(text_in_unstructured_p) {
	pips_debug(9, "something inside_the_loop\n");
	MERGE_TEXTS (t, inside_the_unstructured);
      }

      /* Print the ENDDWHILE
       */
      if (text_in_unstructured_p && print_loops && while_p)
	{
	  append_marged_text(t, current_margin, st_ENDWHILE, "");
	}

      update_statement_icfg (current_stmt_head (), t);
      break;
    }
  default:
    break;
  }

}

/* RANGE
 * functions to avoid the indentation when dealing with DO expressions.
 */
static bool range_flt(range __attribute__ ((unused)) r)
{
    statement s = current_stmt_head();

    if (statement_loop_p(s) && loop_range(statement_loop(s)) && print_loops)
       current_margin -= icfg_indent;
    return true;
}

static void range_rwt(range __attribute__ ((unused)) r)
{
  statement s = current_stmt_head();

  if (statement_loop_p(s) && loop_range(statement_loop(s)) && print_loops)
    current_margin += icfg_indent;
}

/* TEST
   functions to deal with the indentation of ELSIFs.
 */

/* This function tests if t is the exact content of and ELSE clause.
 */
static bool is_elsif_test_p(test t) {

  bool elsif_p = false;

  /*
  gen_chunk p1 = gen_get_recurse_ancestor((void *)t);
  gen_chunk * pp1 = &p1;
  int * pi = pp1;
  int i = *pi;
  if (i != ((int)(HASH_UNDEFINED_VALUE)))
    if ( i != ((int)(NULL)))
      pips_debug(1, "Type of p1 %d\n", gen_type(i));
  */

  /* Determine if t is inside another test */
  test pt = (test)gen_get_ancestor_type(test_domain, (void *)t);
  if (pt != (test)HASH_UNDEFINED_VALUE && pt != (test)(NULL)) {
    // Get the "ELSE Clause" statement of the parent test
    statement ptf = test_false(pt);
    ifdebug(4) {
      pips_debug(4, "Parent test_false is:\n");
      print_statement(ptf);
      fprintf(stderr, "\n");
    }

    // Get the statement corresponding to t
    statement ts = (statement)gen_get_ancestor_type(statement_domain, (void *)t);
    if (ts != (statement)HASH_UNDEFINED_VALUE && ts != (statement)(NULL)) {
      ifdebug(4) {
	pips_debug(4, "My test statement is:\n");
	print_statement(ts);
	fprintf(stderr, "\n");
      }
      // If these two statements are the same, then we are in an ELSIF clause.
      elsif_p = (ptf == ts);
    }
  }
  return elsif_p;
}

/* This function tests if the ELSE clause of t is an ELIF.
 */
static bool has_elsif_test_p(test t) {

  bool has_elsif_p = false;

  pips_debug (3, ">>>has_elsif_test_p begins for test=%p\n", t);

  statement   tfs = test_false(t);
  instruction tfi = statement_instruction(tfs);

  has_elsif_p = instruction_test_p(tfi);

  pips_debug (3, "has_elsif_p = %d\n", has_elsif_p);
  pips_debug (3, ">>>has_elsif_test_p ends for test=%p\n", t);

  return (has_elsif_p);
}


static bool test_flt (test t)
{
  bool is_elsif_p = false;

  pips_debug (3, ">>>Test_flt begins for test=%p\n", t);

  is_elsif_p = is_elsif_test_p(t);
  int offset = (is_elsif_p ? 0 : icfg_indent);

  if (print_ifs) {
    current_margin += offset;
    pips_debug( 4, "is_elsif_p = %d\n", is_elsif_p);
    pips_debug( 4, "current_margin increased: %d -> %d\n",
		current_margin - offset, current_margin
		);
  }
  pips_debug (3, ">>>Test_flt ends for test=%p\n", t);

  return true;
}

static void test_rwt (test l)
{
  text inside_then = text_undefined;
  text inside_else = text_undefined;
  text inside_if = text_undefined;
  text t = make_text (NIL);
  bool something_to_print;

  bool is_elsif_p  = false;
  bool has_elsif_p = false;
  int  offset;
  int  else_margin  = current_margin;

  pips_debug (3, ">>>Test_rwt begins for test=%p\n", l);

  is_elsif_p  = is_elsif_test_p(l);
  has_elsif_p = has_elsif_test_p(l);
  offset      = (is_elsif_p ? 0 : icfg_indent);

  inside_if   = copy_text((text) load_statement_icfg (current_stmt_head ()));
  inside_then = copy_text((text) load_statement_icfg (test_true (l)));
  inside_else = copy_text((text) load_statement_icfg (test_false (l)));

  something_to_print = (some_text_p(inside_else) ||
			some_text_p(inside_then) ||
			some_text_p(inside_if));

  if (print_ifs) {
    current_margin -= offset;
    pips_debug( 4, "is_elsif_p = %d\n", is_elsif_p);
    pips_debug( 4, "current_margin decreased: %d -> %d\n",
		current_margin + offset, current_margin
		);
  }

  /* Print the IF.

     If this is the IF of an ELIF, don't print it.
   */
  if (something_to_print && print_ifs && !is_elsif_p)
    append_marged_text(t, current_margin, st_IF, "");

  /* print things in the if expression*/
  if (some_text_p(inside_if))
    MERGE_TEXTS (t, inside_if);

  /* print then statements */
  if (some_text_p(inside_then)) {
    /* Print the THEN */
    if (something_to_print && print_ifs && strlen(st_THEN)>0) {
      append_marged_text(t, current_margin, st_THEN, "");
    }
    MERGE_TEXTS (t, inside_then);
  }

  /* print else/elif statements */
  if (some_text_p(inside_else)){
    /* Print the ELSE / ELIF */
    if (something_to_print && print_ifs) {

      // Margin correction
      else_margin -= (is_elsif_p  ? icfg_indent : 0);
      else_margin -= (has_elsif_p && !is_elsif_p ? icfg_indent : 0);

      //else_margin += (has_elsif_p ? icfg_indent : 0);
      if (has_elsif_p)
	append_marged_text(t, else_margin, st_ELIF, "");
      else {
	append_marged_text(t, else_margin, st_ELSE, "");
      }
    }
    MERGE_TEXTS (t, inside_else);
  }

  /* Print the ENDIF.

     If this is the ENDIF of an ELIF, don't print it
   */
  if (something_to_print && print_ifs && !is_elsif_p) {
    append_marged_text(t, current_margin, st_ENDIF, "");
  }

  /* store it to the statement mapping */
  update_statement_icfg (current_stmt_head(), t);

  pips_debug (3, ">>>Test_rwt ends for test=%p\n", l);

  return;
}

static void print_module_icfg(entity module)
{
  const char* module_name = module_local_name(module);
  statement s = (statement) db_get_memory_resource(DBR_CODE,module_name,true);
  text txt = make_text(NIL);
  append_marged_text(txt, 0, module_name, "");
  current_vertex = make_vertex((vertex_label)txt, NIL);

  set_current_module_entity(module);

  /* allocate the mapping  */
  make_icfg_map();

  reset_hooks_register(icfg_error_handler);

  current_margin = icfg_indent;

  print_loops = get_bool_property(ICFG_DOs);
  print_ifs = get_bool_property(ICFG_IFs);

  gen_multi_recurse
    (s,
     statement_domain, statement_flt, statement_rwt,
     call_domain     , call_flt     , gen_null,
     loop_domain     , loop_flt     , loop_rwt,
     instruction_domain    , instruction_flt  , instruction_rwt,
     test_domain     , test_flt     , test_rwt,
     whileloop_domain, loop_flt       , while_rwt,
     forloop_domain, loop_flt       , forloop_rwt,
     range_domain    , range_flt    , range_rwt,
     NULL);

  // ???
  if (filter_decoration_call) {
    if (vertex_successors(current_vertex) == NIL) {
      bool found = false;
      MAP(SENTENCE, sen, {
          string one_line = sentence_to_string(sen);
          if (strstr(one_line, CALL_MARK) == NULL) {
            found = true;
            break;
          }
        }, text_sentences(load_statement_icfg(s)));
      if (found) {
        verlist = safe_add_vertex_to_list(current_vertex, verlist);
      } else {
        safe_free_vertex(current_vertex, verlist);
        current_vertex = vertex_undefined;
      }
    } else {
      verlist = safe_add_vertex_to_list(current_vertex, verlist);
    }
  } else {
    verlist = safe_add_vertex_to_list(current_vertex, verlist);
  }

  if (!vertex_undefined_p(current_vertex))
    MERGE_TEXTS(txt, (text) load_statement_icfg(s));

  make_resource_from_starting_node(module_name, DBR_ICFG_FILE,
                                   get_bool_property(ICFG_IFs) ? ".icfgc" :
                                   (get_bool_property(ICFG_DOs) ? ".icfgl" :
                                    ".icfg"),
                                   current_vertex, verlist, true);

  if (get_bool_property(ICFG_DV))
    make_resource_from_starting_node(module_name, DBR_DVICFG_FILE, ".dvicfg",
                                     current_vertex, verlist, false);

  // cleanup
  free_icfg_map();
  reset_hooks_unregister(icfg_error_handler);
  reset_current_module_entity();
}

static bool internal_print_icfg(
  const string module_name,
  bool with_ifs,
  bool with_loops,
  bool do_graph,
  bool do_reset,
  text (*deco1)(const string),
  text (*deco2)(entity, entity, statement, call),
  text (*deco3)(entity, statement, call),
  text (*deco4)(entity, statement))
{
  entity mod = local_name_to_top_level_entity(module_name);

  pips_debug(1,"===%s===%s===\n", module_name, entity_name(mod));
  debug_on(ICFG_DEBUG_LEVEL);

  // select language
  prettyprint_fortran_icfg_p = fortran_module_p(mod);
  prettyprint_C_icfg_p = c_module_p(mod);

  // hmm... not whether sure using properties is a good idea
  set_bool_property(ICFG_IFs, with_ifs);
  set_bool_property(ICFG_DOs, with_loops);
  set_bool_property(ICFG_DV, do_graph);

  do_reset_current_module_entity_on_decoration = do_reset;

  module_decoration = deco1;
  precise_decoration = deco2;
  filter_decoration_call = deco3;
  filter_decoration_stmt = deco4;

  icfg_set_indentation(get_int_property("ICFG_INDENTATION"));
  print_module_icfg(mod);
  icfg_reset_indentation();

  module_decoration = NULL;
  precise_decoration = NULL;
  filter_decoration_call = NULL;
  filter_decoration_stmt = NULL;

  debug_off();
  return true;
}

bool generic_print_icfg(
  const string module_name,
  bool with_ifs,
  bool with_loops,
  bool do_graph,
  text (*decoration)(const string))
{
  return internal_print_icfg(module_name, with_ifs, with_loops, do_graph,
                             true, decoration, NULL, NULL, NULL);
}

bool generic_print_icfg_precise(
  const string module_name,
  bool with_ifs,
  bool with_loops,
  bool do_graph,
  text (*decoration)(entity, entity, statement, call))
{
  return internal_print_icfg(module_name, with_ifs, with_loops, do_graph,
                             true, NULL, decoration, NULL, NULL);
}

bool generic_print_icfg_filtered(
  const string module_name,
  bool with_ifs,
  bool with_loops,
  bool do_graph,
  text (*decoration_call)(entity, statement, call),
  text (*decoration_stmt)(entity, statement))
{
  return internal_print_icfg(module_name, with_ifs, with_loops, do_graph,
                         false, NULL, NULL, decoration_call, decoration_stmt);
}
