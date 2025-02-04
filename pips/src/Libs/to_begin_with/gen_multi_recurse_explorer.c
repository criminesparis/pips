/* A simple phase to show up the path explore by gen_multi_recurse */

#include "genC.h"
#include "linear.h"
#include "ri.h"
#include "ri-util.h"
#include "misc.h"
#include "control.h"
#include "pipsdbm.h"
#include "resources.h"
#include "prettyprint.h"

static bool statement_filter(statement obj) {
  pips_debug(0, "\t IN\n");
  ifdebug(0) {
    print_statement(obj);
  }
  return true;
}

static void statement_rewrite(statement obj) {
  pips_debug(0, "\t OUT\n");
  ifdebug(2) {
    print_statement(obj);
  }
}

static bool call_filter(__attribute__((unused)) call obj) {
  pips_debug(0, "\t IN\n");
  return false;
}

static void call_rewrite(__attribute__((unused)) call obj) {
  pips_debug(0, "\t OUT\n");
}

static bool sequence_filter(__attribute__((unused)) sequence obj) {
  pips_debug(0, "\t IN\n");
  return true;
}

static void sequence_rewrite(__attribute__((unused)) sequence obj) {
  pips_debug(0, "\t OUT\n");
}

static bool test_filter(__attribute__((unused)) test obj) {
  pips_debug(0, "\t IN\n");
  return true;
}

static void test_rewrite(__attribute__((unused)) test obj) {
  pips_debug(0, "\t OUT\n");
}

static bool loop_filter(__attribute__((unused)) loop obj) {
  pips_debug(0, "\t IN\n");
  return true;
}

static void loop_rewrite(__attribute__((unused)) loop obj) {
  pips_debug(0, "\t OUT\n");
}

static bool forloop_filter(__attribute__((unused)) forloop obj) {
  pips_debug(0, "\t IN\n");
  return true;
}

static void forloop_rewrite(__attribute__((unused)) forloop obj) {
  pips_debug(0, "\t OUT\n");
}

static bool whileloop_filter(__attribute__((unused)) whileloop obj) {
  pips_debug(0, "\t IN\n");
  return true;
}

static void whileloop_rewrite(__attribute__((unused)) whileloop obj) {
  pips_debug(0, "\t OUT\n");
}

static bool multitest_filter(__attribute__((unused)) multitest obj) {
  pips_debug(0, "\t IN\n");
  return true;
}

static void multitest_rewrite(__attribute__((unused)) multitest obj) {
  pips_debug(0, "\t OUT\n");
}

static bool unstructured_filter(__attribute__((unused)) unstructured obj) {
  pips_debug(0, "\t IN\n");
  return true;
}

static void unstructured_rewrite(__attribute__((unused)) unstructured obj) {
  pips_debug(0, "\t OUT\n");
}

//static bool expression_filter(expression obj) {
//  pips_debug(0, "\n");
//  return true;
//}
//
//static void expression_rewrite(expression obj) {
//  pips_debug(0, "\n");
//}

bool gen_multi_recurse_explorer(char * module_name) {
  statement module_statement;
  bool good_result_p = true;

  debug_on("GMRE_DEBUG_LEVEL");
  pips_debug(1, "begin\n");

  //-- configure environment --//
  set_current_module_entity(module_name_to_entity(module_name));

  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, module_name, true) );
  module_statement = get_current_module_statement();

  pips_assert("Statement should be OK before...",
      statement_consistent_p(module_statement));

  //set_ordering_to_statement(module_statement);

  //-- Make the job -- //
  gen_multi_recurse(module_statement
      , statement_domain,               statement_filter, statement_rewrite
      , call_domain,                    call_filter, call_rewrite
      , sequence_domain,                sequence_filter, sequence_rewrite
      , test_domain,                    test_filter, test_rewrite
      , loop_domain,                    loop_filter, loop_rewrite
      , whileloop_domain,               whileloop_filter, whileloop_rewrite
      , forloop_domain,                 forloop_filter, forloop_rewrite
      , multitest_domain,               multitest_filter, multitest_rewrite
      , unstructured_domain,            unstructured_filter, unstructured_rewrite
      , NULL
//      , expression_domain, gen_true, gen_true
      );


  pips_assert("Statement should be OK after...",
      statement_consistent_p(module_statement));

  //-- Save modified code to database --//
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, strdup(module_name), module_statement);

  //reset_ordering_to_statement();

  pips_debug(1, "end\n");
  debug_off();

  return (good_result_p);
}


