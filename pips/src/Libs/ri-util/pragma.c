/*

  $Id: pragma.c 22764 2015-08-07 13:25:47Z coelho $

  Copyright 1989-2010 HPC Project

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
  This file define methods to deal with objects extensions and pragma
  used as extensions to statements in the PIPS internal representation.

  A middle term, extensions method could go in another file.

  It is a trivial implementation based on strings for a proof of concept.

  Pierre.Villalon@hpc-project.com
  Ronan.Keryell@hpc-project.com
*/

#include "linear.h"
#include "genC.h"
#include "misc.h"
#include "ri.h"
#include "naming.h"
#include "ri-util.h"
#include "properties.h"

//*************************************************** Not so Local constant

// unused: static const string C_PRAGMA_HEADER = C_PRAGMA_HEADER_STRING;
// FI: progress over #define and #include?
const string FORTRAN_PRAGMA_HEADER = FORTRAN_PRAGMA_HEADER_STRING;
const string FORTRAN_OMP_CONTINUATION = FORTRAN_OMP_CONTINUATION_STRING;



/*****************************************************Local static function
 */
static bool is_expression_omp_private_p (expression exp) {
  entity ent = expression_to_entity (exp);
  return (ENTITY_OMP_PRIVATE_P (ent));
}

static bool is_expression_omp_if_p (expression exp) {
  entity ent = expression_to_entity (exp);
  return (ENTITY_OMP_IF_P (ent));
}

static bool is_expression_omp_reduction_p (expression exp) {
  entity ent = expression_to_entity (exp);
  return (ENTITY_OMP_REDUCTION_P (ent));
}

static bool is_expression_omp_omp_p (expression exp) {
  entity ent = expression_to_entity (exp);
  return ENTITY_OMP_OMP_P(ent);
}

static bool is_expression_omp_for_p (expression exp) {
  entity ent = expression_to_entity (exp);
  return ENTITY_OMP_FOR_P(ent);
}

static bool is_expression_omp_parallel_p (expression exp) {
  entity ent = expression_to_entity (exp);
  return ENTITY_OMP_PARALLEL_P(ent);
}

static if_clause_policy get_if_clause_policy (void) {
  if_clause_policy result = IGNORE_IF_POLICY;
  const char* prop = get_string_property ("OMP_IF_MERGE_POLICY");
  if (strcmp (prop, "ignore") == 0) {
    result = IGNORE_IF_POLICY;
  }
  else if (strcmp (prop, "or") == 0) {
    result = OR_IF_POLICY;
  }
  else if (strcmp (prop, "and") == 0) {
    result = AND_IF_POLICY;
  }
  return result;
}

// merge all if conditions
static expression merge_conditions(list l_cond, if_clause_policy policy, language l) {
  expression result = expression_undefined;
  entity op = entity_undefined;
  switch(policy) {
    case IGNORE_IF_POLICY:
      break;
    case AND_IF_POLICY:
      // switch(get_prettyprint_language_tag()) {
      switch(language_tag(l)) {
        case is_language_fortran:
        case is_language_fortran95:
          op = CreateIntrinsic(AND_OPERATOR_NAME);
          break;
        case is_language_c:
          op = CreateIntrinsic(C_AND_OPERATOR_NAME);
          break;
        default:
          pips_internal_error ("This case should have been handled before");
          break;
      }
      break;
    case OR_IF_POLICY:
      //switch(get_prettyprint_language_tag()) {
      switch(language_tag(l)) {
        case is_language_fortran:
        case is_language_fortran95:
          op = CreateIntrinsic(OR_OPERATOR_NAME);
          break;
        case is_language_c:
          op = CreateIntrinsic(C_OR_OPERATOR_NAME);
          break;
        default:
          pips_internal_error ("This case should have been handled before");
          break;
      }
      break;
    default:
      pips_internal_error ("update switch case");
      break;
  }
  // now we have a list of condition and an operator -> merge them
  result = expressions_to_operation(l_cond, op);
  return result;
}


/***************************************************PRAGMA AS EXPRESSION PART
 */

/**
   @brief build the expression to be put in the if clause. This functions
   takes care of the output language.
   @return the condition compared to the threshold as an expression
   @param cond, the condition to be compared to the threshold
**/
expression pragma_build_if_condition(expression cond, language l) {
  entity op = entity_undefined;
  //switch(get_prettyprint_language_tag()) {
  switch(language_tag(l)) {
    case is_language_fortran:
    case is_language_fortran95:
      op = CreateIntrinsic(GREATER_OR_EQUAL_OPERATOR_NAME);
      break;
    case is_language_c:
      op = CreateIntrinsic(C_GREATER_OR_EQUAL_OPERATOR_NAME);
      break;
    default:
      pips_internal_error ("This case should have been handled before" );
      break;
  }
  int threshold = get_int_property("OMP_LOOP_PARALLEL_THRESHOLD_VALUE");
  list args_if = gen_expression_cons(int_to_expression(threshold), NIL);
  args_if = gen_expression_cons(cond, args_if);
  call c = make_call(op, args_if);
  return call_to_expression(c);
}

/** @return "if (cond)" as an expression
 *  @param arg, the condition to be evaluted by the if clause
 */
expression pragma_if_as_expr (expression arg) {
  entity omp = CreateIntrinsic(OMP_IF_FUNCTION_NAME);
  list args_expr = gen_expression_cons (arg, NIL);
  call c = make_call (omp, args_expr);
  //  syntax s = make_syntax_call (c);
  expression expr_if = call_to_expression (c);// make_expression (s, normalized_undefined);
  return expr_if;
}

/** @return "private (x,y)" as an expression
 *  @param args_expr, the private variables as a list of expression
 */
expression pragma_private_as_expr_with_args (list args_expr) {
  entity omp = CreateIntrinsic(OMP_PRIVATE_FUNCTION_NAME);
  call c = make_call (omp, args_expr);
  syntax s = make_syntax_call (c);
  expression expr_omp = make_expression (s, normalized_undefined);
  return expr_omp;
}

/** @return "private (x,y)" as an expression
 *  @param arg, the private variables as a list of entities
 */
expression pragma_private_as_expr (list args_ent) {
  // build the privates variable as a list of expression
  list args_expr = entities_to_expressions (args_ent);
  return pragma_private_as_expr_with_args (args_expr);
}

/** @return "omp parallel" as a list of expression
 */
list pragma_omp_parallel_as_exprs (void) {
  // first prepare "omp" as an expression
  entity omp = CreateIntrinsic(OMP_OMP_FUNCTION_NAME);
  call c = make_call (omp, NULL);
  syntax s = make_syntax_call (c);
  expression expr_omp = make_expression (s, normalized_undefined);

  //secondly prepare "parallel" as an expression
  entity parallel = CreateIntrinsic(OMP_PARALLEL_FUNCTION_NAME);
  c = make_call (parallel, NULL);
  s = make_syntax_call (c);
  expression expr_parallel = make_expression (s, normalized_undefined);

  // build the list of expression
  list result = CONS(EXPRESSION, expr_omp, NIL);
  result = gen_expression_cons (expr_parallel, result);
  return result;
}

/** @return "omp parallel for" as an expression
 */
list pragma_omp_parallel_for_as_exprs (void) {
  // first prepare "for" as an expression
  entity e = CreateIntrinsic(OMP_FOR_FUNCTION_NAME);
  call c = make_call (e, NULL);
  syntax s = make_syntax_call (c);
  expression expr_for = make_expression (s, normalized_undefined);

  //secondly get "omp parallel as an expr and concat
  list result = pragma_omp_parallel_as_exprs ();
  result = gen_expression_cons (expr_for, result);

  return result;
}


/**
 * @brief filter out a pragma (expression list) removing all requested variables
 * @params l_expr is the list of expressions to filter
 * @params to_filter is the list of entities to remove from l_pragma
 */
list filter_variables_in_pragma_expr(list /* of expr */ l_expr,
                                     list /* of entities */to_filter) {

  // If all variable in exp are removed, we remove the expr from the list
  list expr_to_remove = NIL;

  FOREACH (EXPRESSION, expr, l_expr) {
    // Get the list of arguments, to filter out
    call c = expression_call(expr);
    list args = call_arguments (c);

    // The list where we will record arg to remove from args
    list entity_to_remove = NIL;

    // FI: to avoid cycles between librairies ri-util and prettyprint
    /* ifdebug(5) { */
    /*   pips_debug(5,"Handling expression : "); */
    /*   print_expression(expr); */
    /* } */
    if(is_expression_omp_private_p(expr)) {
      // Handle private omp clause
      // Lookup each requested entities
      FOREACH(ENTITY, e, to_filter)
      {
        FOREACH (EXPRESSION, exp, args)
        {
          pips_debug(6,"Matching %s against %s\n",entity_name(e),
              entity_name(expression_to_entity(exp)));
          if(expression_to_entity(exp) == e) {
            entity_to_remove = gen_expression_cons(exp, entity_to_remove);
            break;
          }
        }
      }
      FOREACH(EXPRESSION,exp,entity_to_remove)
      {
        gen_remove(&call_arguments(c), exp);
      }
      if(ENDP(call_arguments(c))) {
        expr_to_remove = gen_expression_cons(expr, expr_to_remove);
      }
    } else if(is_expression_omp_if_p(expr)) {
      // FIXME : todo, merge with previous case ?
    } else if(is_expression_omp_reduction_p(expr)) {
      // FIXME : shouldn't be a problem ! (handled before)
    } else if(is_expression_omp_omp_p(expr) || is_expression_omp_for_p(expr)
        || is_expression_omp_parallel_p(expr)) {
      // FIXME : is there anything to do here ?
    } else {
      pips_debug(0,"Unsupported case : ");
      // FI: to avoid cycles between librairies ri-util and prettyprint
      // print_expression(expr);
      pips_internal_error("We don't know how to handle this omp clause !");
    }
  }
  //Remove expression that are now empty
  FOREACH(EXPRESSION,expr,expr_to_remove) {
    gen_remove(&l_expr, expr);
  }

  return l_expr;
}

/**
   @brief merge omp pragma.
   @return the merged pragma as a list of expression
   @param l_pragma, the list of pragma to merge. The pragma as to be
   a list of expression ordered. The pragma list has to be ordered
   from the outer pragma to the inner pragma as in the original loop nest.
**/
list pragma_omp_merge_expr (list outer_extensions, list l_pragma, language l) {
  // The "omp parallel for" as a list of expression
  list result = pragma_omp_parallel_for_as_exprs ();
  // The list of the variables of the private clauses
  list priv_var = NIL;
  // The list of condition of the if clauses
  list if_cond = NIL;
  // The list of reductions
  list red = NIL;
  // Get the if clause policy
  if_clause_policy policy = get_if_clause_policy ();
  // the outer pragmas
  set outer_pragmas = set_make(set_pointer);
  FOREACH(EXTENSION,ex, outer_extensions) {
      pragma p = extension_pragma(ex);
      if(pragma_expression_p(p)) {
          FOREACH(EXPRESSION, e, pragma_expression (p))
              set_add_element(outer_pragmas,outer_pragmas,e);
      }
  }

  // look into each pragma for private, reduction and if clauses
  FOREACH (PRAGMA, p, l_pragma) {
    pips_assert ("Can only merge a list of pragma as expression",
        pragma_expression_p (p));
    FOREACH (EXPRESSION, e, pragma_expression (p)) {
      // check each expression and save what need to be saved to generate
      // the new omp pragma
      call c = expression_call(e);
      list args = call_arguments (c);
      // bind the args to the right list
      if(is_expression_omp_private_p(e)) {
        // each private var has to be uniquely declared
        list add = NIL;
        FOREACH (EXPRESSION, exp, args) {
          if(!expression_equal_in_list_p(exp, priv_var) )
            add = gen_expression_cons(exp, add);
        }
        priv_var = gen_nconc(priv_var, add);
      } else if(is_expression_omp_if_p(e)) {
        // if clause : check the policy
        switch(policy) {
          case IGNORE_IF_POLICY:
            // do nothing
            break;
          case AND_IF_POLICY:
          case OR_IF_POLICY:
            if_cond = gen_nconc(if_cond, args);
            break;
          default:
            pips_internal_error ("Should not happen");
            break;
        }
      } else if(is_expression_omp_reduction_p(e)) {
          // only reductions on outer statement are kept
        if(set_belong_p(outer_pragmas,e) ) {
          red = gen_expression_cons(e, red);
        }
      } else if(is_expression_omp_omp_p(e) || is_expression_omp_for_p(e)
          || is_expression_omp_parallel_p(e)) {
        // nothing to do the omp parallel for will be automaticly generated
      } else {
	// FI: to avoid cycles between librairies ri-util and prettyprint
        // print_expression(e);
        pips_internal_error("pips cannot merge this pragma clause");
      }
    }
  }
  set_free(outer_pragmas);
  // build the private clause if needed
  if(priv_var != NIL) {
    expression priv = pragma_private_as_expr_with_args(priv_var);
    // append the private clause to the omp parallel for
    result = gen_expression_cons(priv, result);
  }
  // append the reduction clauses if any
  if(red != NIL) {
    result = gen_nconc(red, result);
  }
  // merge the if condition if needed
  if(policy != IGNORE_IF_POLICY) {
    expression expr_if = merge_conditions(if_cond, policy, l);
    // encapsulate the condition into the if clause
    expr_if = pragma_if_as_expr(expr_if);
    // append the if clause to the omp parallel for
    result = gen_expression_cons(expr_if, result);
  }
  return result;
}

/********************************************************** PRAGMA MANAGEMENT
 */

/** @brief  Add a string as a pragma to a statement.
 *  @return void
 *  @param  st, the statement on which we want to add a pragma
 *  @param  s, the pragma string.
 *  @param  copy_flag, to be set to true to duplicate the string
 */
void add_pragma_str_to_statement(statement st, const char* s, bool copy_flag) {
  /* Duplicate string if requested */
  string ps = copy_flag ? strdup(s) : (char*)s /* dangerous !*/;

  /* Make a new pragma */
  pragma p = make_pragma_string(ps);

  /* Will be save as an extension attached to
   * the statement's extension list
   */
  extensions es = statement_extensions(st);
  extension e = make_extension_pragma(p);
  list el = extensions_extension(es);
  el = gen_extension_cons(e, el);
  extensions_extension(es) = el;
}


/** Add a list of strings as as many pragmas to a statement
    @param  st, the statement on which we want to add a pragma
    @param  l, a list of pragma string(s)
    @param  copy_flag, to be set to true to duplicate the string
 */
void add_pragma_strings_to_statement(statement st, list l, bool copy_flag) {
  FOREACH(STRING, p, l)
    add_pragma_str_to_statement(st, p, copy_flag);
}


/** @brief  Add a pragma as a list of expression to a statement.
 *  @return void
 *  @param  st, the statement on which we want to add a pragma
 *  @param  l, the list of expression.
 */
void
add_pragma_expr_to_statement(statement st, list l) {
  extensions es = statement_extensions(st);
  /* Make a new pragma: */
  pragma p = pragma_undefined;
  p = make_pragma_expression(l);
  extension e = make_extension_pragma(p);
  /* Add the new pragma to the extension list: */
  list el = extensions_extension(es);
  el = gen_extension_cons(e, el);
  extensions_extension(es) = el;
  ifdebug (5) {
    // This is debugging code. It creates a cycle between ri-util and prettyprint
    /* extern string pragma_to_string(pragma); */
    /* string str = pragma_to_string (p); */
    /* if (str != string_undefined) */
    /*   pips_debug (5, "pragma : %s added\n", str); */
    ;
  }
}

