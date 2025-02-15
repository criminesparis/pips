/*

  $Id: declarations.c 23265 2016-11-02 08:07:40Z coelho $

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
/* Regeneration of declarations from the symbol table
 *
 * Regeneration of declarations...
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "linear.h"
#include "genC.h"

#include "misc.h"
#include "properties.h"

#include "ri-util.h"
#include "text-util.h"
#include "prettyprint.h"

/*===================== Variables and Function prototypes for C ===========*/

/* pdl is the parser declaration list. It is used to decide if a
 * derived entity should be simply declared, "struct s", or fully
 * defined, "struct s {....}". It is accessed by its pointer ppdl
 */
text c_text_entity(entity module, entity e, int margin, list * ppdl, bool init_p);
list c_words_entity(type t, list name, list * ppdl);
static list words_initial_qualifiers(list obj);
list words_dimensions(list dims, list * ppdl);

/********************************************************************* WORDS */

static list
words_constant(constant obj)
{
    list pc=NIL;

    if (constant_int_p(obj)) {
	pc = CHAIN_IWORD(pc,constant_int(obj));
    }
    else {
	pips_internal_error("unexpected tag");
    }
    /*What about real, double, string constants ... ?*/
    return(pc);
}

static list words_value(value obj)
{
    list pc=NIL;

    if (value_symbolic_p(obj)) {
	pc = words_constant(symbolic_constant(value_symbolic(obj)));
    }
    else if (value_constant_p(obj)) {
	pc = words_constant(value_constant(obj));
    }
    else if (value_unknown_p(obj)) {
      // FI: Only good for Fortran
      pc = CHAIN_SWORD(pc, "(*)");
    }
    else {
	pips_internal_error("unexpected tag");
	pc = NIL;
    }

    return(pc);
}

static list words_parameters(entity e, list * ppdl)
{
  list pc = NIL;
  type te = entity_type(e);
  functional fe;
  int nparams, i;
  bool space_p = get_bool_property("PRETTYPRINT_LISTS_WITH_SPACES");

  pips_assert("is functionnal", type_functional_p(te));

  fe = type_functional(te);
  nparams = gen_length(functional_parameters(fe));

  for (i = 1; i <= nparams; i++) {
    entity param = find_ith_parameter(e, i);
    if (pc != NIL) {
      pc = CHAIN_SWORD(pc, space_p? ", " : ",");
    }

    /* If prettyprint alternate returns... Property to be added. */
    if ( get_bool_property( "PRETTYPRINT_REGENERATE_ALTERNATE_RETURNS" )
        && formal_label_replacement_p( param ) ) {
      pc = CHAIN_SWORD(pc, "*");
    } else if ( entity_undefined_p(param) ) {
      parameter p = PARAMETER(gen_nth(i-1,functional_parameters(fe)));
      type t = parameter_type(p);
      switch(get_prettyprint_language_tag()) {
        case is_language_fortran:
        case is_language_fortran95:
          pips_user_warning("%dth parameter out of %d parameters not found for "
              "function %s\n", i, nparams, entity_name(e));
          break;
        case is_language_c:
          /* param can be undefined for C language: void foo(void)
           * We do not have an entity corresponding to the 1st argument
           */
          break;
        default:
          pips_internal_error("Language unknown !");
          break;
      }
      pc = gen_nconc( pc, words_type( t, ppdl, true ) );
      /* Should be correct, but seems useless */
      //if(!same_string_p(pn, "")) {
      //  pc = gen_nconc(pc, strdup(" "));
      //  pc = gen_nconc(pc, strdup(pn));
      //}
    } else {
      switch(get_prettyprint_language_tag()) {
        case is_language_fortran:
        case is_language_fortran95:
          /*
           * Variable type and dimensions will be (eventually) specified
           * in declarations
           */
          pc = CHAIN_SWORD(pc, entity_local_name(param));
          break;
        case is_language_c: {
          /*
           * We have to print variable's type, dimensions, ... with C
           * This can be also a formal function
           */
          type t = type_undefined;
          t = entity_type(param);
	  //list npdl = NIL;
	  /* FI: types and derived entities used for the formal
	   * parameters should be defined before end. If ever they are
	   * defined in the formal scope, they cannot be used
	   * elsewhere.
	   *
	   * FI: It might be better to implement the same behavior
	   * without building npdl, by passing an extra
	   * parameter... But you would have to check all call sites
	   * to c_words_entity().
	   */
	  //npdl = type_supporting_entities(npdl, t);
          list entity_word = CHAIN_SWORD(NIL,entity_local_name(param));
          pc = gen_nconc( pc,
                          c_words_entity( t,
                                          entity_word,
                                          ppdl /*&npdl*/ ) );
	  //gen_free_list(npdl);
          break;
        }
        default:
          pips_internal_error("Language unknown !");
          break;
      }
    }
  }
  return ( pc );
}

static list words_dimension(dimension obj, list * ppdl)
{
  list pc = NIL;
  call c = call_undefined;
  entity f = entity_undefined;
  expression eup = expression_undefined;
  expression e1 = expression_undefined;
  expression e2 = expression_undefined;
  intptr_t up, i;
  switch (get_prettyprint_language_tag())
  {
  case is_language_fortran95:
    // Not asterisk for unbound dimension in F95
    if(unbounded_dimension_p(obj)) {
      pc = CHAIN_SWORD(pc,":");
      break;
    }
    // paste code to avoid fall-through warnings
    pc = words_expression( dimension_lower(obj), ppdl );
    pc = CHAIN_SWORD(pc,":");
    pc = gen_nconc( pc, words_expression( dimension_upper(obj), ppdl ) );
    break;
  case is_language_fortran:
    pc = words_expression( dimension_lower(obj), ppdl );
    pc = CHAIN_SWORD(pc,":");
    pc = gen_nconc( pc, words_expression( dimension_upper(obj), ppdl ) );
    break;
  case is_language_c:
    /* The lower bound of array in C is always equal to 0,
       we only need to print (upper dimension + 1) */
    if ( unbounded_dimension_p( obj ) )
      pc = CHAIN_SWORD(pc,"");
    else {
      eup = dimension_upper(obj);
      if ( false && expression_integer_value( eup, &up ) ) {
        /*
         * FI: why do you want to change the source code? Because it may no
         * longer be the user source code after partial evaluation
         */
        pc = CHAIN_IWORD(pc,up+1);
      }
      if ( expression_constant_p( eup )
           && constant_int_p(expression_constant(eup)) ) {
        /* To deal with partial eval generated expressions */
        up = expression_to_int( eup );
        pc = CHAIN_IWORD(pc,up+1);
      } else {
        list ql = dimension_qualifiers(obj);
        list qpc = words_qualifiers(ql);
        if ( expression_call_p( eup ) ) {
          c = syntax_call(expression_syntax(eup));
          f = call_function(c);
          if ( ENTITY_MINUS_P(f) || ENTITY_MINUS_C_P(f) ) {
            e1 = binary_call_lhs(c);
            e2 = binary_call_rhs(c);
            if ( expression_integer_value( e2, &i ) && i == 1 )
              pc = words_expression( e1, ppdl );
          }
        }
        if ( pc == NIL ) {
          /* to be refined here to make more beautiful expression,
           * use normalize ? FI: why would we modify the user C source code?
           */
          pc = words_expression( MakeBinaryCall( CreateIntrinsic( "+" ),
                                                 eup,
                                                 int_to_expression( 1 ) ),
                                 ppdl );
        }
        if(!ENDP(qpc))
          pc = gen_nconc(qpc, pc);
      }
    }
    break;
  default:
    pips_internal_error("Language tag=%d unknown.\n",
                        get_prettyprint_language_tag());
    break;
  }
  return pc;
}

/* some compilers don't like dimensions that are declared twice.
 * this is the case of g77 used after hpfc. thus I added a
 * flag not to prettyprint again the dimensions of common variables. FC.
 *
 * It is in the standard that dimensions cannot be declared twice in a
 * single module. BC.
 */
list words_declaration(entity e,
                       bool prettyprint_common_variable_dimensions_p,
                       list * ppdl) {
  list pl = NIL;
  bool space_p = get_bool_property("PRETTYPRINT_LISTS_WITH_SPACES");

  pl = CHAIN_SWORD(pl, entity_user_name(e));

  if (type_variable_p(entity_type(e))) {
    if (prettyprint_common_variable_dimensions_p || !(variable_in_common_p(e)
        || variable_static_p(e))) {
      if (variable_dimensions(type_variable(entity_type(e))) != NIL) {
        list dims = variable_dimensions(type_variable(entity_type(e)));

        switch(get_prettyprint_language_tag()) {
          case is_language_fortran:
          case is_language_fortran95:
            pl = CHAIN_SWORD(pl, "(");
            MAPL(pd,
                {
                  pl = gen_nconc(pl, words_dimension(DIMENSION(CAR(pd)), ppdl));
                  if (CDR(pd) != NIL) pl = CHAIN_SWORD(pl, space_p? ", " : ",");
                }, dims)
            ;
            pl = CHAIN_SWORD(pl, ")");
            break;
          case is_language_c:
            MAPL(pd,
                {
                  pl = CHAIN_SWORD(pl, "[");
                  pl = gen_nconc(pl, words_dimension(DIMENSION(CAR(pd)), ppdl));
                  pl = CHAIN_SWORD(pl, "]");
                }, dims)
            ;
            break;
          default:
            pips_internal_error("Language unknown !");
        }
      }
    }
  }
  attach_declaration_to_words(pl, e);
  return (pl);
}

/* what about simple DOUBLE PRECISION, REAL, INTEGER... */
list words_basic(basic obj, list * ppdl)
{
  list pc = NIL;

  if ( basic_undefined_p(obj) ) {
    /* This may happen in debugging statements */
    pc = CHAIN_SWORD(pc,"undefined");
  } else {
    switch ( basic_tag(obj) ) {
      case is_basic_int: {
        switch(get_prettyprint_language_tag()) {
          case is_language_fortran:
          case is_language_fortran95:
/*            if(basic_int(obj)==4) {
              pc = CHAIN_SWORD(pc,"INTEGER");
            } else { */
              pc = CHAIN_SWORD(pc,"INTEGER*");
              pc = CHAIN_IWORD(pc,basic_int(obj));
//            }
            break;
          case is_language_c:
          {
            string pn;
            switch (basic_int(obj)) {
              // FC: if the numbering was nice, it could use an array...
            case 1: pn = "PRETTYPRINT_C_CHAR_TYPE";
              break;
            case 2: pn = "PRETTYPRINT_C_SHORT_TYPE";
              break;
            case 4: pn = "PRETTYPRINT_C_INT_TYPE";
              break;
            case 6: pn = "PRETTYPRINT_C_LONG_TYPE";
              break;
            case 8: pn = "PRETTYPRINT_C_LONGLONG_TYPE";
              break;
            case 9: pn = "PRETTYPRINT_C_INT128_TYPE";
              break;
            case 11: pn = "PRETTYPRINT_C_UCHAR_TYPE";
              break;
            case 12: pn = "PRETTYPRINT_C_USHORT_TYPE";
              break;
            case 14: pn = "PRETTYPRINT_C_UINT_TYPE";
              break;
            case 16: pn = "PRETTYPRINT_C_ULONG_TYPE";
              break;
            case 18: pn = "PRETTYPRINT_C_ULONGLONG_TYPE";
              break;
            case 19: pn = "PRETTYPRINT_C_UINT128_TYPE";
              break;
            case 21: pn = "PRETTYPRINT_C_SCHAR_TYPE";
              break;
            case 22: pn = "PRETTYPRINT_C_SSHORT_TYPE";
              break;
            case 24: pn = "PRETTYPRINT_C_SINT_TYPE";
              break;
            case 26: pn = "PRETTYPRINT_C_SLONG_TYPE";
              break;
            case 28: pn = "PRETTYPRINT_C_SLONGLONG_TYPE";
              break;
            default:
              pips_internal_error("Unexpected int number %d\n", basic_int(obj));
            }
            pc = CHAIN_SWORD(pc, get_string_property(pn));
            break;
          }
        default:
          pips_internal_error("Language unknown !");
          break;
        }
        break;
      }
      case is_basic_float: {
        switch(get_prettyprint_language_tag()) {
          case is_language_fortran:
          case is_language_fortran95:
            pc = CHAIN_SWORD(pc,"REAL*");
            pc = CHAIN_IWORD(pc,basic_float(obj));
            break;
          case is_language_c:
            switch ( basic_float(obj) ) {
              case 4:
                pc = CHAIN_SWORD(pc,"float");
                break;
              case 8:
                pc = CHAIN_SWORD(pc,"double");
                break;
              case 16:
                pc = CHAIN_SWORD(pc,"long double");
                break;
            }
            break;
          default:
            pips_internal_error("Language unknown !");
            break;
        }
        break;
      }
      case is_basic_logical: {
        switch(get_prettyprint_language_tag()) {
          case is_language_fortran:
            pc = CHAIN_SWORD(pc,"LOGICAL*");
            pc = CHAIN_IWORD(pc,basic_logical(obj));
            break;
          case is_language_c:
            pc = CHAIN_SWORD(pc,"int"); /* FI: Use "bool" of stdbool.h instead
					    of "int" but it leads to
					    include issue for
					    generated code; avoid stdbool.h
					    and use "_Bool" directly
					    but it leads to infinite
					    loop from "_Bool" to
					    "_Bool" because "_Bool"
					    is declared as a typedef
					    in anr999 */
            break;
          case is_language_fortran95:
            pips_internal_error("Need to update F95 case");
            break;
          default:
            pips_internal_error("Language unknown !");
            break;
        }
        break;
      }
      case is_basic_overloaded: {
        /* should be a user error? Or simply bootstrap.c is not accurate? */
        switch(get_prettyprint_language_tag()) {
          case is_language_fortran:
            pc = CHAIN_SWORD(pc,"OVERLOADED");
            break;
          case is_language_c:
            pc = CHAIN_SWORD(pc,"overloaded");
            break;
          case is_language_fortran95:
            pips_internal_error("Need to update F95 case");
            break;
          default:
            pips_internal_error("Language unknown !");
            break;
        }
        break;
      }
      case is_basic_complex: {
        switch(get_prettyprint_language_tag()) {
          case is_language_fortran:
          case is_language_fortran95:
            pc = CHAIN_SWORD(pc,"COMPLEX*");
            pc = CHAIN_IWORD(pc,basic_complex(obj));
            break;
          case is_language_c:
            switch ( basic_complex(obj) ) {
              case 8:
                pc = CHAIN_SWORD(pc,"_Complex");
                break;
              case 9:
                pc = CHAIN_SWORD(pc,"float _Complex");
                break;
              case 16:
                pc = CHAIN_SWORD(pc,"double _Complex");
                break;
              case 32:
                pc = CHAIN_SWORD(pc,"long double _Complex");
                break;
              default:
                pips_internal_error("Unexpected complex size");
            }
            break;
          default:
            pips_internal_error("Language unknown !");
            break;
        }
        break;
      }
      case is_basic_string: {
        switch(get_prettyprint_language_tag()) {
          case is_language_fortran:
            pc = CHAIN_SWORD(pc,"CHARACTER*");
            pc = gen_nconc( pc, words_value( basic_string(obj) ) );
            break;
          case is_language_c:
            pc = CHAIN_SWORD(pc,"char *"); // FI: should it be char[]?
            break;
          case is_language_fortran95:
            pips_internal_error("Need to update F95 case");
            break;
          default:
            pips_internal_error("Language unknown !");
            break;
        }
        break;
      }
      case is_basic_bit: {
        symbolic bs = basic_bit(obj);
        int i = constant_int(symbolic_constant(bs));
        pips_debug(7,"Bit field basic: %d\n",i);
        pc = CHAIN_SWORD(pc,"int"); /* ignore if it is signed or unsigned */
        break;
      }
      /* The following code maybe redundant, because of tests in c_words_entity*/
      case is_basic_pointer: {
        type t = basic_pointer(obj);
        pips_debug(7,"Basic pointer\n");
        if ( type_undefined_p(t) ) {
          /* This may occur in the parser when a variable is used
           before it is fully defined (see ptr in decl42.c) */
          pc = CHAIN_SWORD(pc,"type_undefined *");
        } else {
	  pc = gen_nconc( pc, words_type( t, ppdl, false ) );
          pc = CHAIN_SWORD(pc," *");
        }
        break;
      }
      case is_basic_derived: {
        entity ent = basic_derived(obj);
        const char* name = entity_user_name( ent );
        const char* lname = entity_local_name( ent );
        type t = entity_type(ent);

        if ( strstr( lname, STRUCT_PREFIX DUMMY_STRUCT_PREFIX ) == NULL
            && strstr( lname, UNION_PREFIX DUMMY_UNION_PREFIX ) == NULL
            && strstr( lname, ENUM_PREFIX DUMMY_ENUM_PREFIX ) == NULL ) {
	  pc = gen_nconc( pc, words_type( t, ppdl, false ) );
          pc = CHAIN_SWORD(pc," ");
          pc = CHAIN_SWORD(pc,name);
          pc = CHAIN_SWORD(pc," "); /* FI: This space may not be always useful */
        } else {
          pc = gen_nconc( pc, c_words_entity( t, NIL, ppdl ) );
        }
        break;
      }
      case is_basic_typedef: {
        entity ent = basic_typedef(obj);
        pc = CHAIN_SWORD(pc,entity_user_name(ent));
        break;
      }
      default:
        pips_internal_error("unexpected basic tag %d", basic_tag(obj));
    }
  }
  return(pc);
}

/**************************************************************** SENTENCE */

sentence sentence_variable(entity e, list * ppdl)
{
    list pc = NIL;
    type te = entity_type(e);

    pips_assert("is a variable", type_variable_p(te));

    pc = gen_nconc(pc, words_basic(variable_basic(type_variable(te)), ppdl));
    pc = CHAIN_SWORD(pc, " ");

    pc = gen_nconc(pc, words_declaration(e, true, ppdl));

    return(make_sentence(is_sentence_unformatted,
			 make_unformatted(NULL, 0, 0, pc)));
}

sentence Sentence_Variable(entity e)
{
  list pdl = NIL;
  sentence s = sentence_variable(e, &pdl);
  gen_free_list(pdl);
  return s;
}

/* We have no way to distinguish between the SUBROUTINE and PROGRAM
 * They two have almost the same properties.
 * For the time being, especially for the PUMA project, we have a temporary
 * idea to deal with it: When there's no argument(s), it should be a PROGRAM,
 * otherwise, it should be a SUBROUTINE.
 * Lei ZHOU 18/10/91
 *
 * correct PROGRAM and SUBROUTINE distinction added, FC 18/08/94
 * approximate BLOCK DATA / SUBROUTINE distinction also added. FC 09/97
 */
sentence sentence_head(entity e, list * ppdl)
{
  list pc = NIL;
  type te = entity_type(e);
  functional fe;
  type tr;
  list args = words_parameters(e, ppdl);

  pips_assert("is functionnal", type_functional_p(te));

  if (static_module_p(e))
    pc = CHAIN_SWORD(pc,"static ");

  fe = type_functional(te);
  tr = functional_result(fe);

  switch(type_tag(tr)) {
    case is_type_void:
      switch(get_prettyprint_language_tag()) {
        case is_language_fortran:
        case is_language_fortran95:
          if (entity_main_module_p(e))
            pc = CHAIN_SWORD(pc,"PROGRAM ");
          else {
            if (entity_blockdata_p(e))
              pc = CHAIN_SWORD(pc, "BLOCKDATA ");
            else if (entity_f95module_p(e))
              pc = CHAIN_SWORD(pc, "MODULE ");
            else
              pc = CHAIN_SWORD(pc,"SUBROUTINE ");
          }
          break;
        case is_language_c:
          pc = CHAIN_SWORD(pc,"void ");
          break;
        default:
          pips_internal_error("Language unknown !");
          break;
      }
      break;
    case is_type_variable: {
      list pdl = NIL;
      // FI: the qualifiers are dropped...
      variable var = type_variable(tr);
      basic b = variable_basic(var);
      list ql = variable_qualifiers(var);
      pc = gen_nconc(pc, words_basic(b, &pdl));
      pc = gen_nconc(words_qualifiers(ql), pc);
      switch(get_prettyprint_language_tag()) {
        case is_language_fortran:
        case is_language_fortran95:
          pc = CHAIN_SWORD(pc," FUNCTION ");
          break;
        case is_language_c:
          pc = CHAIN_SWORD(pc," ");
          break;
        default:
          pips_internal_error("Language unknown !");
          break;
      }
      break;
    }
    case is_type_unknown:
      /*
       * For C functions with no return type.
       * It can be treated as of type int, but we keep it unknown
       * for the moment, to make the differences and to regenerate initial code
       */
      break;
    default:
      pips_internal_error("unexpected type for result");
  }

  pc = CHAIN_SWORD(pc, entity_user_name(e));

  if (!ENDP(args)) {
    pc = CHAIN_SWORD(pc, "(");
    pc = gen_nconc(pc, args);
    pc = CHAIN_SWORD(pc, ")");
  } else if (type_variable_p(tr)
              || (prettyprint_language_is_c_p()
                  && (type_unknown_p(tr) || type_void_p(tr)))) {
    pc = CHAIN_SWORD(pc, "()");
  }

  return (make_sentence(is_sentence_unformatted, make_unformatted(NULL,
                                                                  0,
                                                                  0,
                                                                  pc)));
}

/* ================C prettyprinter functions================= */

/* returns a list of words corresponding to a list of qualifiers...
 *
 * obj is a list of qualifiers.
 *
 * initial_p :
 *
 * late_p:
 *
 * Space management?
 */
static list generic_words_qualifiers(list obj, bool initial_p, bool late_p)
{
  list pc = NIL;
  FOREACH(QUALIFIER, q, obj) {
    switch (qualifier_tag(q)) {
    case is_qualifier_register:
      if(initial_p)
        pc = CHAIN_SWORD(pc, "register ");
      break;
    case is_qualifier_thread:
      if(initial_p)
        pc = CHAIN_SWORD(pc, "__thread ");
      break;
    case is_qualifier_const:
      if(late_p)
        pc = CHAIN_SWORD(pc, "const ");
      break;
    case is_qualifier_restrict:
      /* FI: might not be an initial qualifier either */
      if(late_p)
        pc = CHAIN_SWORD(pc, "restrict ");
      break;
    case is_qualifier_volatile:
      if(initial_p)
        pc = CHAIN_SWORD(pc, "volatile ");
      break;
    case is_qualifier_auto:
      /* FI: the auto case was missing; I have no idea why. */
      if(initial_p)
        pc = CHAIN_SWORD(pc, "auto ");
      break;
    case is_qualifier_asm: {
      /* asm qualifiers a reprinted in the end ... */
      } break;
    case is_qualifier_static_dimension:
      /* FI: I have no idea about initial_p and late_p... */
      if (initial_p)
        pc = CHAIN_SWORD(pc,"static ");
      break;
    case is_qualifier_local:
    {
      const char * q = get_string_property("PRETTYPRINT_LOCAL_QUALIFIER");
      if (! same_string_p(q, ""))
      {
        pc = CHAIN_SWORD(pc, q);
        pc = CHAIN_SWORD(pc, " ");
      }
      break;
    }
    case is_qualifier_global:
    {
      const char * q = get_string_property("PRETTYPRINT_GLOBAL_QUALIFIER");
      if (! same_string_p(q, ""))
      {
        pc = CHAIN_SWORD(pc, q);
        pc = CHAIN_SWORD(pc, " ");
      }
      break;
    }
    case is_qualifier_constant:
    {
      const char * q = get_string_property("PRETTYPRINT_CONSTANT_QUALIFIER");
      if (! same_string_p(q, ""))
      {
        pc = CHAIN_SWORD(pc, q);
        pc = CHAIN_SWORD(pc, " ");
      }
      break;
    }
    case is_qualifier_private:
    {
      const char * q = get_string_property("PRETTYPRINT_PRIVATE_QUALIFIER");
      if (! same_string_p(q, ""))
      {
        pc = CHAIN_SWORD(pc, q);
        pc = CHAIN_SWORD(pc, " ");
      }
      break;
    }
    default:
      pips_internal_error("Unexpected qualifier tag.\n");
    }
  }

  if(!initial_p && late_p && !ENDP(pc))
    pc = gen_nconc(CHAIN_SWORD(NIL, " "), pc);

  return pc;
}

// Needed by prettyrint/print.c
list words_qualifiers(list obj)
{
  return generic_words_qualifiers(obj, true, true);
}

static list words_initial_qualifiers(list obj)
{
  return generic_words_qualifiers(obj, true, false);
}

static list words_late_qualifiers(list obj)
{
  return generic_words_qualifiers(obj, false, true);
}

/* obj is the type to describe
*
* pdl is a list of already/previously declared data structures (not
* 100 % sure)
*
* argument_p: the type is used as an argument type in a function
* declaration; if an argument appears with the "unknown" type it is
* explicitly declared "int"
*
* returns a list of strings, called "words".
*/
list words_type(type obj, list * ppdl, bool argument_p)
{
  list pc = NIL;
  switch (type_tag(obj))
    {
    case is_type_variable:
      {
	// FI: the qualifiers are dropped
	variable var = type_variable(obj);
	basic b = variable_basic(var);
	list ql = variable_qualifiers(var);
	list dl = variable_dimensions(var);
	pc = words_basic(b, ppdl);
	pc = gen_nconc(pc, words_dimensions(dl, ppdl));
	pc = gen_nconc(words_qualifiers(ql), pc);
	break;
      }
    case is_type_void:
      {
	list ql = type_void(obj);
	pc = CHAIN_SWORD(pc,"void");
	pc = gen_nconc(words_qualifiers(ql), pc);
	break;
      }
    case is_type_unknown:
      {
	/* The default type is int. It can be skipped in direct
	   declarations, but not as type of an argument in a function
	   declaration */
	if(argument_p)
	  pc = CHAIN_SWORD(pc,"int");
	break;
      }
    case is_type_struct:
      {
	pc = CHAIN_SWORD(pc,"struct");
	break;
      }
    case is_type_union:
      {
	pc = CHAIN_SWORD(pc,"union");
	break;
      }
    case is_type_enum:
      {
	pc = CHAIN_SWORD(pc,"enum");
	break;
      }
    case is_type_functional:
      {
	string_buffer result = string_buffer_make(true);
	string rs = string_undefined;
	dump_functional(type_functional(obj), result);
	rs = string_buffer_to_string(result);
	pc = gen_nconc(pc, CONS(STRING, rs, NIL));
	string_buffer_free(&result);
	break;
      }
    case is_type_varargs:
      {
	pc = CHAIN_SWORD(pc,"...");
	break;
      }
    default:
      pips_internal_error("unexpected tag %d", type_tag(obj));
    }
  pips_debug(8, "End: \"\%s\"\n", list_to_string(pc));
  return pc;
}

list Words_Type(type obj)
{
  list pdl = NIL;
  list pc =  words_type(obj, &pdl, false);
  return pc;
}

bool c_brace_expression_p(expression e)
{
  if (expression_call_p(e))
    {
      entity f = call_function(syntax_call(expression_syntax(e)));
      if (ENTITY_BRACE_INTRINSIC_P(f))
	return true;
    }
  return false;
}


list words_brace_expression(expression exp, list * ppdl)
{
  list pc = NIL;
  list args = call_arguments(syntax_call(expression_syntax(exp)));
  bool first = true;
  bool space_p = get_bool_property("PRETTYPRINT_LISTS_WITH_SPACES");

  pc = CHAIN_SWORD(pc,"{");
  MAP(EXPRESSION,e,
  {
    if (!first)
      pc = CHAIN_SWORD(pc, space_p? ", " : ",");
    if (c_brace_expression_p(e))
      pc = gen_nconc(pc,words_brace_expression(e, ppdl));
    else
      pc = gen_nconc(pc,words_expression(e, ppdl));
    first = false;
  },args);
  pc = CHAIN_SWORD(pc,"}");
  return pc;
}

list words_dimensions(list dims, list * ppdl)
{
  list pc = NIL;
  bool space_p = get_bool_property("PRETTYPRINT_LISTS_WITH_SPACES");

  switch(get_prettyprint_language_tag()) {
    case is_language_fortran:
    case is_language_fortran95: {
      pc = CHAIN_SWORD(pc, "(");
      string spacer = "";
      FOREACH(dimension,d,dims) {
        pc = CHAIN_SWORD(pc, spacer);
        pc = gen_nconc(pc, words_dimension(d, ppdl));
        spacer = space_p ? ", " : ",";
      }
      pc = CHAIN_SWORD(pc, ")");
      break;
    }
    case is_language_c: {
      FOREACH(dimension,d,dims) {
        pc = CHAIN_SWORD(pc, "[");
        pc = gen_nconc(pc, words_dimension(d, ppdl));
        pc = CHAIN_SWORD(pc, "]");
      }
      break;
    }
    default:
      pips_internal_error("Language unknown !");
      break;
  }
  return pc;
}

/* This recursive function prints a C variable with its type.
 * It can be a simple variable declaration such as "int a"
 * or complicated one such as "int (* forces[10])()" (an array of
 * 10 pointers, each pointer points to a function
 * with no parameter and the return type is int).
 *
 * Type "t" is recursively traversed and the obtained attribute are
 * accumulated in the list "name" (name of the type, not name of the
 * variable).
 *
 * Purpose of "is_safe"? Seems to be passed down recursively but never
 * to be used...
 *
 * In C, functional type can be decorated by optional dummy parameter names.
 */
list generic_c_words_entity(type t, list name, bool is_safe, bool add_dummy_parameter_name_p, list * ppdl)
{
// If this function is still used, NIL should be replaced by the
// module declaration list
  return generic_c_words_simplified_entity(t, name, is_safe,
					   add_dummy_parameter_name_p,
					   true, false, false, ppdl);
}

/* Same as above, but the bool is_first is used to skip a type
 * specifier which is useful when several variables or types are
 * defined in a unique statement such as "int i, *pi, ai[10],...;"
 *
 * type t: new type to add in front of the word list name
 *
 * list name: later part of the declaration being built
 *
 * bool is_safe: does not seem to be used anymore
 *
 * bool add_dummy_parameter_name_p: for function declarations, add
 * a dummy parameter name to the type of each formal parameter
 *
 * bool is_first: prettyprint the qualifiers or not; they should be
 * printed only once when they apply to several declarations as in:
 *
 * "register int i, j;"
 *
 * in_type_declaration is set to true when a variable is declared at
 * the same time as its type
 *
 * argument_p: the type is used as argument type in a function declaration
 *
 * list ppdl: pointer to the declaration list to decide if data
 * structures appearing in another data structure must be declared
 * independently or not. See validation cases struct03.c, struct04.c
 * and struct05.c.
 */
list generic_c_words_simplified_entity(type t, list name, bool is_safe, bool add_dummy_parameter_name_p, bool is_first, bool in_type_declaration, bool argument_p, list * ppdl)
{
  list pc = NIL;
  bool space_p = get_bool_property("PRETTYPRINT_LISTS_WITH_SPACES");

  if(type_undefined_p(t)) {
    pc = CHAIN_SWORD(NIL, "type_undefined");
    pc = gen_nconc(pc,name);
    return pc;
  }

  if (type_functional_p(t))
    {
      functional f = type_functional(t);
      type t2 = functional_result(f);
      list lparams = functional_parameters(f);
      list cparam = list_undefined;
      bool first = true;
      int pnum;

      pips_debug(9,"Function type with name = \"%s\" and length %zd\n",
		 list_to_string(name), gen_length(name));

      if ((gen_length(name) > 1)
	  || ((gen_length(name) == 1) && (strcmp(STRING(CAR(name)),"*")==0)))
	{
	  /* Function name is an expression like *vfs[] in (*vfs[])()
	     (syntax = application), or an abstract function type, so
	     parentheses must be added */
	  pc = CHAIN_SWORD(NIL,"(");
	  pc = gen_nconc(pc,name);
	  pc = CHAIN_SWORD(pc,")(");

	}
      else
	{
	  /* Function name is a simple reference */
	  pc = CHAIN_SWORD(name,"(");
	}

      if(!overloaded_parameters_p(lparams)) {
	for(cparam = lparams, pnum = 1; !ENDP(cparam); POP(cparam), pnum++) {
	  parameter p = PARAMETER(CAR(cparam));
	  type t1 = parameter_type(p);
	  string pn = dummy_unknown_p(parameter_dummy(p))?
	    string_undefined
	    : strdup(entity_local_name(dummy_identifier(parameter_dummy(p))));

	  if(add_dummy_parameter_name_p
	     && string_undefined_p(pn)
	     && !type_varargs_p(t1)
	     && !type_void_p(t1)) {
	    /* RK wants us to use another better function than i2a, but
	       its name is not documented next to i2a() source code and
	       here the string is going to be strduped, which makes
	       i2a() a better choice. */
	    pn = concatenate("f", i2a(pnum), NULL);
	  }

	  /*pips_debug(3,"Parameter type %s\n ",
	    type_undefined_p(t1)? "type_undefined" :
	    words_to_string(words_type(t1, ppdl, true))); */
	  if (!first)
	    pc = gen_nconc(pc,CHAIN_SWORD(NIL, space_p? ", " : ","));
	  /* c_words_entity(t1,NIL) should be replaced by c_words_entity(t1,name_of_corresponding_parameter) */
	  pc = gen_nconc(pc,
			 generic_c_words_simplified_entity(t1,
							   string_undefined_p(pn)? NIL : CONS(STRING, strdup(pn), NIL),
							   is_safe, false, true,in_type_declaration, true, ppdl));
	  pips_debug(9,"List of parameters \"%s\"\n ",list_to_string(pc));
	  first = false;
	}
      }

      pc = CHAIN_SWORD(pc,")");
      return generic_c_words_simplified_entity(t2, pc, is_safe, false,
					       is_first, in_type_declaration,
					       argument_p, ppdl);
    }

  if (pointer_type_p(t))
    {
      type t1 = basic_pointer(variable_basic(type_variable(t)));
      pips_debug(9,"Pointer type with name = %s\n", list_to_string(name));

      /*
       *  No space : it's only "after a comma to separate items in lists such as
       *  declaration lists or parameter lists in order to improve readability"
       *
       * FI: a space would be useful sometimes to separate "*" from an
       * identifier in "char *foo(void)" to obtain "char * foo(void)"
       * instead, but not "char * * foo(void)" nor "void foo(char * )".
       */
      // pc = CHAIN_SWORD(NIL, space_p? "*":"*");
      pc = CHAIN_SWORD(NIL, "*");
      // FI: qualifiers for type t1 are dealt with at a lower level,
      // qualifiers for type t are dealt here
      variable var = type_variable(t);
      list ql = variable_qualifiers(var);
      if (qualifiers_const_p(ql) || qualifiers_restrict_p(ql)) {
	pc = gen_nconc(pc, words_late_qualifiers(variable_qualifiers(type_variable(t))) );
	// We may have other qualifiers which must be output somewhere
	// else, for instance "register"
	/*
	pc = gen_nconc(pc,
		       words_qualifiers(variable_qualifiers(type_variable(t))));
	*/
      }
      pc = gen_nconc(pc,name);
      pc = generic_c_words_simplified_entity(t1, pc, is_safe, false,
					     is_first, in_type_declaration,
					     argument_p, ppdl);
      pc = gen_nconc(words_initial_qualifiers(ql), pc);
      return pc;
    }

  /* Add type qualifiers if there are */
  bool qualifiers_p = false;
  if (false && ( is_first || in_type_declaration )
      && type_variable_p(t)
      && variable_qualifiers(type_variable(t)) != NIL) {
    pc = words_qualifiers(variable_qualifiers(type_variable(t)));
    qualifiers_p = true;
  }
  else if (false && ( is_first || in_type_declaration )
      && type_void_p(t)
      && type_void(t) != NIL)
    pc = words_qualifiers(type_void(t));

  if (basic_type_p(t)) {
      string sname = list_to_string(name);
      pips_debug(9,"Basic type with name = \"%s\"\n", sname);

      if(is_first) {
	pc = gen_nconc(pc,words_type(t, ppdl, argument_p));
      }
      if (string_type_p(t)) {
	// pc = CHAIN_SWORD(pc," *");
	;
      }
      /* FI: left out of the previous declaration internal representation */
      if(strlen(sname)!=0 && is_first/* && !qualifiers_p*/)
	pc = CHAIN_SWORD(pc," ");
      if(!bit_type_p(t) || (strstr(sname,DUMMY_MEMBER_PREFIX)==NULL)) {
	pc = gen_nconc(pc,name);
	}
      free(sname);
      if (bit_type_p(t)) {
	  symbolic s = basic_bit(variable_basic(type_variable(t)));
	  expression ie = symbolic_expression(s);
	  list iew = words_expression(ie, ppdl);
	  pc = CHAIN_SWORD(pc,":");
	  pc = gen_nconc(pc, iew);
      }
      return pc;
    }
  if (array_type_p(t)) {
    variable var = type_variable(t);
    list dims = variable_dimensions(var);
    list ql = variable_qualifiers(var);
    type t1 = copy_type(t);
    list tmp = NIL;
    pips_debug(9,"Array type with name = %s\n", list_to_string(name));

    if ((gen_length(name) > 1) || ((gen_length(name) == 1) && (strcmp(STRING(CAR(name)),"*")==0)))
      {
	/* Array name is an expression like __ctype+1 in (__ctype+1)[*np]
	   (syntax = subscript), or abstract type, parentheses must be added */
	tmp = CHAIN_SWORD(tmp,"(");
	tmp = gen_nconc(tmp,name);
	tmp = CHAIN_SWORD(tmp,")");
      }
    else
      {
	/* Array name is a simple reference  */
	tmp = name;
      }
    gen_full_free_list(variable_dimensions(type_variable(t1)));
    variable_dimensions(type_variable(t1)) = NIL;
    // FI: I understand why the dimension information has to be
    // removed, I so not understand why the qualifiers have to be
    // removed too
    gen_full_free_list(variable_qualifiers(type_variable(t1)));
    variable_qualifiers(type_variable(t1)) = NIL;
    pips_debug(8, "Before concatenation, pc=\"\%s\"\n", list_to_string(pc));
    if(pc!=NIL && !qualifiers_p)
      pc = CHAIN_SWORD(pc, " ");
    list ret =
      gen_nconc(pc,
		generic_c_words_simplified_entity(t1,gen_nconc(tmp,words_dimensions(dims, ppdl)),
						  is_safe, false, is_first,
						  in_type_declaration,
						  argument_p,
						  ppdl));
    ret = gen_nconc(words_qualifiers(ql), ret);
    free_type(t1);
    return ret;
  }

  if (derived_type_p(t))
    {
      variable v = type_variable(t);
      basic b = variable_basic(v);
      list ql = variable_qualifiers(v);
      entity ent = basic_derived(b);
      if(is_first) {
	type t1 = entity_type(ent);
	string n = entity_name(ent);
	pips_debug(9,"Derived type with name = %s\n", list_to_string(name));
	if((strstr(n,ENUM_PREFIX DUMMY_ENUM_PREFIX)==NULL)
	   &&(strstr(n,STRUCT_PREFIX DUMMY_STRUCT_PREFIX)==NULL)
	   &&(strstr(n,UNION_PREFIX DUMMY_UNION_PREFIX)==NULL)) {
	  if(gen_in_list_p((void *) ent, *ppdl) // previously defined
	     || !declarable_type_p(t1, *ppdl) // not definable yet
	     // FI: it might be better to pass down an extra parameter
	     // rather than deduce this from name
	     || (!ENDP(name) && same_string_p(STRING(CAR(name)), ""))) { // "struct s;" case
	    /* The derived type has been declared explicitly
	       elsewhere: see struct05.c */
	    pc = gen_nconc(pc,words_type(t1, ppdl, argument_p));
	    pc = CHAIN_SWORD(pc," ");
	    pc = CHAIN_SWORD(pc,entity_user_name(ent));
	  }
	  else {
	    /* The derived type is declared by itself*/
	    const char* name = entity_user_name(ent);
	    list epc = NIL;
	    /* Do not recurse down if the derived type reference
	       itself */
	    *ppdl = gen_once((void *) ent, *ppdl);
	    epc =
	      generic_c_words_simplified_entity(t1,
						CHAIN_SWORD(NIL,name),
						is_safe,
						add_dummy_parameter_name_p,
						is_first, in_type_declaration,
						argument_p, ppdl);
	    pc = gen_nconc(pc, epc);
	    //gen_free_list(npdl);
	  }
	  if(!ENDP(ql))
	    pc = gen_nconc(words_qualifiers(ql), pc);
	}
	else {
	  //pc = CHAIN_SWORD(pc,"problem!");
	  pc = c_words_entity(t1, pc, ppdl);
	}
	/* A place holder variable has no name and require no space */
	if(gen_length(name)==1 && same_string_p(STRING(CAR(name)),""))
	  ;
	else
	  pc = CHAIN_SWORD(pc," ");
      }
      return gen_nconc(pc,name);
    }
  if (typedef_type_p(t))
    {
      if(is_first) {
	// FI: type_variable_p() is always true?
	variable var = type_variable(t);
	list ql = variable_qualifiers(var);
	basic b = variable_basic(var);
	entity ent = basic_typedef(b);
	pips_debug(9,"Typedef type with name = \"\%s\"\n",
		   list_to_string(name));
	pc = CHAIN_SWORD(pc, entity_user_name(ent));
	pc = gen_nconc(words_qualifiers(ql), pc);
	if(name!=NIL)
	  pc = CHAIN_SWORD(pc," ");
      }
      return gen_nconc(pc,name);
    }
  if (type_varargs_p(t))
    {
      pips_debug(9,"Varargs type ... with name = %s\n", list_to_string(name));
      pc = CHAIN_SWORD(pc,"...");
      return gen_nconc(pc,name);
    }
  /* This section is derived from c_text_entity() */
  /* it is used for structures, unions and enums which have no names
     because they are part of a more global declaration such as
     typedef s*/
  /* FI: The union and the struct cases could be merged. */
  if(type_struct_p(t))
    {
      list l = type_struct(t);
      string sname = list_to_string(name);
      list cl = list_undefined;

      pips_debug(9,"Struct type ... with name = %s\n", sname);

      pc = CHAIN_SWORD(pc,"struct ");
      // hmmm... name may be an empty list... and the sname test seems true
      if(name && strstr(sname,DUMMY_STRUCT_PREFIX)==NULL) {
	pc = gen_nconc(pc,name);
	if(!ENDP(l))
	  pc = CHAIN_SWORD(pc," ");
      }
      free(sname);
      if(!ENDP(l)) {
	pc = CHAIN_SWORD(pc,"{");

	for(cl = l; !ENDP(cl); POP(cl)) {
	  entity sm = ENTITY(CAR(cl));
	  type tsm = entity_type(sm);
	  pc = gen_nconc(pc,c_words_entity(tsm,CHAIN_SWORD(NIL,entity_user_name(sm)), ppdl));
	  if(ENDP(CDR(cl)))
	    pc = CHAIN_SWORD(pc,";");
	  else
	    pc = CHAIN_SWORD(pc,"; ");
	}
	pc = CHAIN_SWORD(pc,"}");
      }
      return pc;
    }
  if(type_union_p(t))
    {
      list l = type_union(t);
      string sname = list_to_string(name);
      list cl = list_undefined;

      pips_debug(9,"Union type ... with name = %s\n", sname);

      pc = CHAIN_SWORD(pc,"union ");
      //if(strstr(sname,DUMMY_UNION_PREFIX)==NULL) {
      //	pc = gen_nconc(pc,name);
      //	pc = CHAIN_SWORD(pc," ");
      //}
      free(sname);
      pc = CHAIN_SWORD(pc,"{");

      for(cl = l; !ENDP(cl); POP(cl)) {
	entity eu = ENTITY(CAR(cl));
	type tu = entity_type(eu);
	pc = gen_nconc(pc,c_words_entity(tu,CHAIN_SWORD(NIL,entity_user_name(eu)), ppdl));
	if(ENDP(CDR(cl)))
	  pc = CHAIN_SWORD(pc,";");
	else
	  pc = CHAIN_SWORD(pc,"; ");
     }
      pc = CHAIN_SWORD(pc,"}");
      return pc;
    }
  if(type_enum_p(t))
    {
      list l = type_enum(t);
      bool first = true;
      string sname = list_to_string(name);
      list cl = list_undefined;
      int cv = 0;

      pips_debug(9,"Enum type ... with name = %s\n", sname);

      pc = CHAIN_SWORD(pc,"enum ");
      if(strstr(sname,DUMMY_ENUM_PREFIX)==NULL && !same_string_p(sname,"")) {
      	pc = gen_nconc(pc,name);
      	pc = CHAIN_SWORD(pc," ");
      }
      free(sname);
      pc = CHAIN_SWORD(pc,"{");

      for(cl = l; !ENDP(cl); POP(cl)) {
	entity em = ENTITY(CAR(cl));
	value emv = entity_initial(em);
	symbolic ems = value_symbolic(emv);
	expression eme = symbolic_expression(ems);
	constant emc = symbolic_constant(value_symbolic(emv));
	int n = constant_int(emc);

	if (!first)
	  pc = CHAIN_SWORD(pc, space_p? ", " : ",");
	pc = CHAIN_SWORD(pc, entity_user_name(em));
	if(n!=cv || !constant_int_p(emc)) {
	  pc = CHAIN_SWORD(pc, "=");
	  pc = gen_nconc(pc, words_expression(eme, ppdl));
	  cv = n;
	}
	cv++;
	first = false;
      };
      pc = CHAIN_SWORD(pc,"}");
      return pc;
    }
  pips_internal_error("unexpected case");
  return NIL;
}

/* The declaration list pointer ppdl is passed down to determine if an internal
   derived type must be fully expanded within another declaration or
   not. If it is declared by itself, there is no need to expand its
   declaration again. */
list c_words_simplified_entity(type t, list name, bool is_first, bool in_type_declaration, list * ppdl)
{
  list pc = generic_c_words_simplified_entity(t, name, false, false, is_first,
					      in_type_declaration, false, ppdl);

  ifdebug(8) {
    string s = list_to_string(pc);
    pips_debug(8, "End with \"\%s\"\n", s);
  }

  return pc;
}

list c_words_entity(type t, list name, list * ppdl)
{
  list pc = generic_c_words_entity(t, name, false, false, ppdl);

  ifdebug(8) {
    string s = list_to_string(pc);
    pips_debug(8, "End with \"\%s\"\n", s);
  }

  return pc;
}

list safe_c_words_entity(type t, list name)
{
  /* Ignore the parser declared entities? */
  list pdl = NIL;
  list l = generic_c_words_entity(t, name, true, false, &pdl);
  gen_free_list(pdl);
  return l;
}

/* Generate declarations for a list of entities belonging to the same
   statement declaration

   ppdl: derived from the parser declared entity; used to decide if a
   derived type entity de must be declared as a reference to de
   (e.g. "struct s") or as the type definition of de (e.g. "struct s
   {}"). Of course, the type can be defined only once, even if it is
   referenced several times. Hence, pdl, the list pointed to by ppdl
   is updated in the loop to avoid redeclarations.
 */
text c_text_entities(entity module, list ldecl, int margin, list * ppdl)
{
  text r = make_text(NIL);
  //list npdl = gen_copy_seq(pdl); // new parser declaration list

  FOREACH(ENTITY, e, ldecl) {
    text tmp = text_undefined;
    type t = entity_type(e);

    if(!type_area_p(t)
       && ! type_statement_p(t)
       && !type_unknown_p(t)
       && !storage_formal_p(entity_storage(e))
       && !implicit_c_variable_p(e)) {
      string n = entity_name(e);

      /* Dummy enum must be printed sometimes because their members
	 are exposed directly. */
      if(((strstr(n,DUMMY_ENUM_PREFIX)==NULL)
	  || !type_used_in_type_declarations_p(e, ldecl))
	 && (strstr(n,STRUCT_PREFIX DUMMY_STRUCT_PREFIX)==NULL
	     ||strstr(n,MEMBER_SEP_STRING)!=NULL)
	 && (strstr(n,UNION_PREFIX DUMMY_UNION_PREFIX)==NULL
	     ||strstr(n,MEMBER_SEP_STRING)!=NULL) ) {
	type et = ultimate_type(entity_type(e));
	bool init_p = true; // So as not to modify the behavior although no initializations are expected here
	// FI: I do not understand the copies of pdl in npdl
	tmp = c_text_entity(module, e, margin, ppdl, init_p);
	MERGE_TEXTS(r,tmp);

	if(derived_type_p(et)) {
	  entity de = basic_derived(variable_basic(type_variable(et)));
	  //gen_remove(&npdl, (void *) de);
	  *ppdl = gen_once((void *) de, *ppdl);
	}
      }
    }
  }

  //gen_free_list(npdl);

  return r;
}

/* To print out a struct reference, such as "struct s"*/
static list words_struct_reference(const char* name1, list pc, bool init_p)
{
  pc = CHAIN_SWORD(pc,"struct ");
  if(strstr(name1,DUMMY_STRUCT_PREFIX)==NULL) {
    pc = CHAIN_SWORD(pc,name1);
    if(init_p)
      pc = CHAIN_SWORD(pc," ");
    else {
      // The semicolon is added somewhere else
      // pc = CHAIN_SWORD(pc,";");
      ;
    }
  }
  return pc;
}

/* Prolog to print out a struct definition, such as "struct s { int a;
   int b;}"; for the time being, only the previous function is used. */
/*
static list words_struct(string name1, list pc)
{
  pc = words_struct_reference(name1, pc, true);
  pc = CHAIN_SWORD(pc,"{");
  return pc;
}
*/

static list words_enum_reference(const char * name1, list pc, bool init_p)
{
  pc = CHAIN_SWORD(pc,"enum ");
  if(strstr(name1,DUMMY_ENUM_PREFIX)==NULL) {
    pc = CHAIN_SWORD(pc,name1);
    if(init_p)
      pc = CHAIN_SWORD(pc," ");
  }
  return pc;
}

static list words_enum(const char * name1, list l, bool space_p, list pc, list * ppdl)
{
  bool first = true;
  pc = CHAIN_SWORD(pc,"enum ");
  if(strstr(name1,DUMMY_ENUM_PREFIX)==NULL) {
    pc = CHAIN_SWORD(pc,name1);
    pc = CHAIN_SWORD(pc," ");
  }
  pc = CHAIN_SWORD(pc,"{");
  list cl = list_undefined;
  int cv = 0;

  for(cl = l; !ENDP(cl); POP(cl)) {
    entity em = ENTITY(CAR(cl));
    value emv = entity_initial(em);
    symbolic ems = value_symbolic(emv);
    expression eme = symbolic_expression(ems);
    constant emc = symbolic_constant(value_symbolic(emv));
    int n = constant_int(emc);

    // SG has decided not to evaluate expressions containins a sizeof
    // operator because the result is architecture dependent and
    // because the PIPS user has not specified which architecture
    // should be used.
    //
    // Serge has no idea how many things he has broken in PIPS!!!
    // constant integer expressions are used in many declarations and
    // expected by PIPS components. Unexpected results are going to
    // occur as the blind interpretation of an unknown constant
    // returns 0!
    //
    //if(!constant_int_p(emc))
    //  pips_internal_error("constant expression not evaluated by parser");

    if (!first)
      pc = CHAIN_SWORD(pc, space_p? ", " : ",");
    pc = CHAIN_SWORD(pc, entity_user_name(em));
    if(n!=cv || !constant_int_p(emc)) {
      pc = CHAIN_SWORD(pc, "=");
      pc = gen_nconc(pc, words_expression(eme, ppdl));
      cv = n;
    }
    cv++;
    first = false;
  };
  pc = CHAIN_SWORD(pc,"}");
  return pc;
}

static list words_union(const char* name1, list pc, bool init_p)
{
  pc = CHAIN_SWORD(pc,"union ");
  if(strstr(name1,DUMMY_UNION_PREFIX)==NULL) {
    pc = CHAIN_SWORD(pc,name1);
    if(init_p)
      pc = CHAIN_SWORD(pc," ");
  }
  //pc = CHAIN_SWORD(pc,"{");
  return pc;
}

static list words_variable_or_function(entity module, entity e, bool is_first, list pc, bool in_type_declaration, list * ppdl, bool init_p)
{
  const char* name = place_holder_variable_p(e)? "" : entity_user_name(e);
  type t = entity_type(e);
  //storage s = entity_storage(e);
  value val = entity_initial(e);

  pc = gen_nconc(pc,c_words_simplified_entity(t,CHAIN_SWORD(NIL,name),
					      is_first, in_type_declaration, ppdl));
  /* This part is for declarator initialization if there is. If the
     entity is declared extern wrt current module, do not add this
     initialization */
  if (/* normal mode: module is defined */
      (!entity_undefined_p(module)
       /* init_p is much more reliable */
       /* && !extern_entity_p(module,e) */
       && !value_undefined_p(val)
       && init_p)
      /* debugging mode: module is often undefined */
      || (entity_undefined_p(module) && !value_undefined_p(val))) {
    if (value_expression_p(val)) {
      expression exp = value_expression(val);
      pc = CHAIN_SWORD(pc," = ");
      if (brace_expression_p(exp))
	pc = gen_nconc(pc,words_brace_expression(exp, ppdl));
      else {
	/* */
	pc = gen_nconc(pc,words_subexpression(exp, ASSIGN_OPERATOR_PRECEDENCE, true, ppdl));
      }
    }
    else if(value_code_p(val)) {
      if(type_variable_p(t)) {
	/* it must be a pointer to a function. See encoding in
	 * set_entity_initial: how could this work with several
	 * pointers or pointer arrays to initialize?
	 */
	list il = sequence_statements(code_initializations(value_code(val)));
	if(!ENDP(il)) {
	  statement is = STATEMENT(CAR(il));
	  expression exp =
	    instruction_expression(statement_instruction(is));
	  pc = CHAIN_SWORD(pc," = ");
	  pc = gen_nconc(pc,words_expression(exp, ppdl));
	}
      }
    }
  }
  return pc;
}

/* Fix the declaration list produced by the parser, which includes
   declared program variables but also derived types used in the
   declaration or the initialization, to accomodate the
   prettyprinter, which must decide which derived types appearing in
   the declaration must be defined, and which one must be referenced:

    - first option: get rid of all derived entities; pro: safe; cons:
      all declarations become one liners

    - second option: get rid of all derived entities but the last
      one, assuming they appear in the right order. Sometimes, you may
      even have to get rid of all derived entities.

   All entities in del are useful to regenerate the corresponding
   declaration, but the key entities are the type used for the
   variables, and the variables. Nested types should not appear in the
   return list.

   FI: I wonder what the parser generates for something like

   int foo[sizeof(struct {int a; int b;})] = {...};

   No new list is allocated, just a pointer to the first relevant chunk
   of del.
*/
static list filtered_declaration_list(list del, list * pcl)
{
  /* Filter out secondary types */
  list el = del;
  /* Filter out initialization flags */
  bool foif_p = !ENDP(*pcl);

  ifdebug(8) {
    pips_debug(8, "Input declaration list: ");
    print_entities(del);
    fprintf(stderr, "\n");
  }

  /* FI: initially I assumed > 2 for pattern such as

     struct {struct ..} x;

     but you can also have a struct declaration:

     struct {struct ..};

     with no variable declaration. Or a declaration in the rhs via a
     sizeof or a cast... See below, after the intermediate list.

  */
  if(gen_length(del)>=2) {
    /* Maybe, some type related entities such as substructure should
       not be printed out. Only the last one is useful. */
    entity e_previous = ENTITY(CAR(del));

    if(entity_struct_p(e_previous)
       ||entity_union_p(e_previous)
       ||entity_enum_p(e_previous)) {
      FOREACH(ENTITY, e, CDR(del)) {
	if(entity_struct_p(e)
	   ||entity_union_p(e)
	   ||entity_enum_p(e)) {
	  POP(el);
	  if(foif_p)
	    POP(*pcl);
	}
	else {
	  break;
	}
      }
    }
  }

  ifdebug(8) {
    pips_debug(8, "Intermediate declaration list: ");
    print_entities(el);
    fprintf(stderr, "\n");
  }

  /* Now we still have to deal with "void * p = ... derived type
     definition(s)..."  Maybe, we simply want to make sure that e1
     belongs to type supporting entities of t2... but this is not
     strong enough because it includes types of formal arguments which
     are not relevant
  */
  if(gen_length(el)>=2) {
    entity e1 = ENTITY(CAR(el));

    if(derived_entity_p(e1)) {
      bool match_p = false;
      //type t1 = entity_type(e1);
      entity e2 = ENTITY(CAR(CDR(el)));
      type t2 = entity_type(e2);
      type nt2 = type_undefined;

      /* If t2 is a pointer, get to the final pointed type. */
      nt2 = type_to_final_pointed_type(t2);

      /* If nt2 is a functional type, what is the final pointed type
	 returned? */
      if(type_functional_p(nt2)) {
	functional f2 = type_functional(nt2);
	type rt2 = functional_result(f2);
	nt2 = type_to_final_pointed_type(rt2);
      }

      if(type_variable_p(nt2)) {
	basic b2 = variable_basic(type_variable(nt2));
	if(basic_derived_p(b2) && basic_derived(b2)==e1)
	  match_p = true;
      }
      if(!match_p) {
	POP(el);
	if(foif_p)
	  POP(*pcl);
      }
    }
  }

  ifdebug(8) {
    pips_debug(8, "Output declaration list: ");
    print_entities(el);
    fprintf(stderr, "\n");
  }

  if(!(ENDP(*pcl) || gen_length(el)==gen_length(*pcl))) {
    entity m = get_current_module_entity();
    if(!compilation_unit_entity_p(m)) {
      /* program transformations do not know yet about the prettyprint
	 control list. Let's keep the first element for extern and
	 truncate what's behind, the initialization control list. */
      gen_free_list(CDR(*pcl));
      CDR(*pcl) = NIL;
    }
    else {
      pips_assert("The control list is empty or the two lists have the same "
		  "number of elements",
		  ENDP(*pcl) || gen_length(el)==gen_length(*pcl));
    }
  }

  return el;
}

/* It is assumed that all entities in list el can be declared by an
 * unique statement, i.e. their types must be closely related, as in
 *
 * "int i, *pj, foo();".
 *
 * But you can also have:
 *
 * "struct one { struct too {int a;};};"
 *
 * where no variable is declared. And the parser generate a
 * declaration list stating that "struct two" and "struct one"
 * are declared in this statement.
 *
 * In other words, this function prints out a C declaration statement,
 * taking into account the derived entities that have to be defined
 * exactly once, pdl. Of course, pdl can be updated by the caller when
 * a derived entity is declared so as to avoid a redeclaration.
 *
 * At this first level, the declarations of derived types use several
 * lines. If a nested declaration occurs, the nested declaration is
 * packed on a unique line.
 *
 * List icl indicates for each entity if it should be initialized or
 * not. This is useful for global variable initializations.
 */
text c_text_related_entities(entity module, list del, int margin, int sn, list * ppdl, list cl)
{
  /* If we are not in a compilation unit, the initialization control
   * list is useless and may be wrong because of program
   * transformations such as scalar renaming.
   */
  bool cu_p = entity_undefined_p(module)?
    false :
    compilation_unit_entity_p(module);
  list icl = ENDP(cl)? NIL : (cu_p? CDR(cl) : NIL);
  list el = filtered_declaration_list(del, &icl);
  text r = make_text(NIL);
  entity e1 = ENTITY(CAR(el)); // Let's use the first declared entity.
  const char* name1 = entity_user_name(e1);
  type t1 = entity_type(e1);
  entity e_last = ENTITY(CAR(gen_last(el))); // Let's also use the last declared entity.
  //type t_last = entity_type(e_last);
  //storage s1 = entity_storage(e1);
  storage s_last = entity_storage(e_last);
  //value val1 = entity_initial(e1);
  list pc = NIL;
  bool space_p = get_bool_property("PRETTYPRINT_LISTS_WITH_SPACES");
  bool skip_first_comma_p = true;

  bool place_holder_p = false;
  if(gen_length(el)==2) {
    /* The last entity may be a place holder */
    entity e2 = ENTITY(CAR(CDR(el)));
    if(place_holder_variable_p(e2)) {
      place_holder_p = true;
    }
  }

  /* overwrite the parser declaration list pdl with del */
  //pdl = del;
  // Not a good idea with recursive calls to this function

  pips_assert("the entity list is not empty", gen_length(el)>0);

  pips_debug(5,"Print declaration for first entity %s in module %s\n",
	     entity_name(e1),
	     entity_undefined_p(module)? "UNDEFINED" : entity_name(module));

  /* A declaration has two parts: declaration specifiers and declarator (even with initializer)
     In declaration specifiers, we can have:
     - storage specifiers : typedef, extern, static, auto, register
     - type specifiers : void, char, short, int, long, float, double, signed, unsigned,
                         struct-or-union specifiers, enum specifier, typedef name
     - type qualifiers : const, restrict, volatile
     - function specifiers : inline */

  /* This part is for storage specifiers */
  bool extern_p = false; // so as not to change the default behavior
  bool dummy_p = false;
  if(!ENDP(cl)) {
    expression first = EXPRESSION(CAR(cl));
    int ic = integer_constant_expression_value(first);
    extern_p = (ic==1 || ic==3)? true : false;
    //dummy_p = (ic==2 || ic==3)? true : false;
    // FI: the information about dummy_p is not reliable
    // several derived entities may be used or declared within one declaration
    // statement, but only one flag is stored by the parser...
    dummy_p = false;
  }
  if (!entity_undefined_p(module) && extern_p) {
      /* && (extern_p || explicit_extern_entity_p(module, e_last) */
      /* 	  || (extern_entity_p(module, e_last) && !type_functional_p(t_last)))) */
    pc = CHAIN_SWORD(pc,"extern ");
  }

  if (strstr(entity_name(e_last),TYPEDEF_PREFIX) != NULL) {
    pc = CHAIN_SWORD(pc,"typedef ");
    // FI: too early for typedef17.c
    //*ppdl = CONS(ENTITY, e_last, *ppdl);
    //if(same_string_p(entity_user_name(e_last), "__gconv_t")) {
    //  fprintf(stderr, "Entity \"%s\" found.\n", entity_user_name(e_last));
    //}
  }

  /* The global variables stored in static area and in ram but they
     are not static so a condition is needed, which checks if it is not a
     global variable*/
  // entity m = get_current_module_entity();
  if ((storage_ram_p(s_last)
       && static_area_p(ram_section(storage_ram(s_last)))
       && !strstr(entity_name(e_last),TOP_LEVEL_MODULE_NAME))
      || (entity_module_p(e_last) && static_module_p(e_last)))
    pc = CHAIN_SWORD(pc,"static ");

  /* If a derived type is declared first, the qualifiers are carried
   * by the type of the second entity
   */
  if(derived_entity_p(e1) && gen_length(el)>1) {
    entity e2 = ENTITY(CAR(CDR(el)));
    type t2 = entity_type(e2);
    if(type_variable_p(t2)) {
      variable v2 = type_variable(t2);
      list ql2 = variable_qualifiers(v2);
      pc = gen_nconc(pc, words_qualifiers(ql2));
    }
  }


  /* This part is for type specifiers, type qualifiers, function specifiers and declarator
     Three special cases for struct/union/enum definitions are treated here.
     Variable (scalar, array), pointer, function, variables of type struct/union/enum and typedef
     are treated by function c_words_entity */

  bool in_type_declaration = true;
  switch (type_tag(t1)) {
  case is_type_struct:
    {
      list l = type_struct(t1);
      const char * lname = entity_local_name(e1);
      bool init_p = strstr(lname, STRUCT_PREFIX DUMMY_STRUCT_PREFIX ) != NULL;
      if(!init_p)
	init_p = !dummy_p && !ENDP(l) && !gen_in_list_p(e1, *ppdl)
	  && declarable_type_p(t1, *ppdl) && !place_holder_p;
      pc = words_struct_reference(name1, pc, init_p);
      ADD_SENTENCE_TO_TEXT(r, make_sentence(is_sentence_unformatted,
					    make_unformatted(NULL,sn,margin,pc)));
      if(init_p) {
	*ppdl = gen_once(e1, *ppdl);
	text fields = c_text_entities(module, l, margin+INDENTATION, ppdl);
	pc = CHAIN_SWORD(NIL, "{");
	add_words_to_text(r, pc);
	MERGE_TEXTS(r, fields);
	ADD_SENTENCE_TO_TEXT(r, MAKE_ONE_WORD_SENTENCE(margin, "}"));
      }
      break;
    }
  case is_type_union:
    {
      list l = type_union(t1);
      const char * lname = entity_local_name(e1);
      bool init_p = strstr(lname, UNION_PREFIX DUMMY_UNION_PREFIX ) != NULL;
      if(!init_p)
	init_p = !dummy_p && !ENDP(l) && !gen_in_list_p(e1, *ppdl)
	  && declarable_type_p(t1, *ppdl) && !place_holder_p;
      pc = words_union(name1, pc, init_p);
      ADD_SENTENCE_TO_TEXT(r, make_sentence(is_sentence_unformatted,
					    make_unformatted(NULL,sn,margin,pc)));
      if(init_p) {
	*ppdl = gen_once(e1, *ppdl);
	text fields = c_text_entities(module,l,margin+INDENTATION, ppdl);
	pc = CHAIN_SWORD(NIL, "{");
	add_words_to_text(r, pc);
	MERGE_TEXTS(r,fields);
	ADD_SENTENCE_TO_TEXT(r, MAKE_ONE_WORD_SENTENCE(margin,"}"));
      }
      break;
    }
  case is_type_enum:
    {
      list l = type_enum(t1);
      const char * lname = entity_local_name(e1);
      bool init_p = strstr( lname, ENUM_PREFIX DUMMY_ENUM_PREFIX ) != NULL;
      if(!init_p)
	init_p = !dummy_p && !ENDP(l) && !gen_in_list_p(e1, *ppdl)
	  && declarable_type_p(t1, *ppdl) && !place_holder_p;
      if(init_p) {
	*ppdl = gen_once((void *) e1, *ppdl);
	pc = words_enum(name1, l, space_p, pc, ppdl);
	ADD_SENTENCE_TO_TEXT(r, make_sentence(is_sentence_unformatted,
					      make_unformatted(NULL,sn,margin,pc)));
      }
      else {
	pc = words_enum_reference(name1, pc, init_p);
	ADD_SENTENCE_TO_TEXT(r, make_sentence(is_sentence_unformatted,
					      make_unformatted(NULL,sn,margin,pc)));
      }
      break;
    }
  case is_type_variable:
  case is_type_functional:
  case is_type_void:
  case is_type_unknown:
    {
      /*pc = words_variable_or_function(module, e1, true, pc,
	in_type_declaration, pdl);*/
      in_type_declaration=false;

      bool init_p = extern_p? false : true;
      if(!ENDP(icl)) {
	expression ice = EXPRESSION(CAR(icl)); // Initialization control expression
	int ic = integer_constant_expression_value(ice);
	init_p = ic==1? true : false;
      }

      pc = words_variable_or_function(module, e1, true, pc,
				      in_type_declaration, ppdl, init_p);
      ADD_SENTENCE_TO_TEXT(r, make_sentence(is_sentence_unformatted,
					    make_unformatted(NULL,sn,margin,pc)));
      skip_first_comma_p = false;
      break;
    }
  case is_type_varargs:
  case is_type_statement:
  case is_type_area:
  default:
    pips_internal_error("unexpected type tag");
  }

  /* the word list pc must have been inserted in text r*/
  pc = NIL;



  /* Add the declared variables or more declared variables. */
  list oel = list_undefined; // other entities after e1
  if(place_holder_p)
    oel = CDR(CDR(el)); // skip the place holder variable
  else
    oel = CDR(el);
  //print_entities(oel);
  list oicl = ENDP(icl) ? NIL : CDR(icl);
  FOREACH(ENTITY, e, oel) {
    if(skip_first_comma_p) {
      skip_first_comma_p = false;
      pc = gen_nconc(pc,CHAIN_SWORD(NIL, " "));
    }
    else
      pc = gen_nconc(pc,CHAIN_SWORD(NIL,space_p? ", " : ","));
    bool init_p = true;
    if(!ENDP(oicl)) {
      expression ice = EXPRESSION(CAR(oicl)); // Initialization control expression
      int ic = integer_constant_expression_value(ice);
      init_p = ic==1? true : false;
      POP(oicl);
    }
    pc = words_variable_or_function(module, e, false, pc, in_type_declaration,
				    ppdl, init_p);
  }
  /* add the asm qualifier if needed */
  string asm_qual = strdup("");
  FOREACH(QUALIFIER, q, entity_qualifiers(e1)) {
    if(qualifier_asm_p(q)) {
            asprintf(&asm_qual,"%s __asm(%s)", asm_qual, qualifier_asm(q));
    }
  }
  pc = CHAIN_SWORD(pc,asm_qual);
  free(asm_qual);
  /* the final semi column,*/
  pc = CHAIN_SWORD(pc,";");

  /* the word list pc must be added to the last sentence of text r */
  if(ENDP(text_sentences(r))) {
    pips_internal_error("Unexpected empty text");
  }
  else {
    add_words_to_text(r, pc);
  }

  if (strstr(entity_name(e_last),TYPEDEF_PREFIX) != NULL) {
    *ppdl = CONS(ENTITY, e_last, *ppdl);
  }

  return r;
}

/* FI: strange recursion, probably due to Francois...
   c_text_related_entities calls
   c_text_entities calls
   c_text_entity calls back
   c_text_related_entities (!) but with only one element... may call
   words_variable_or_function calls
   c_words_simplified_entity calls
   generic_c_words_simplified_entity

   Note: text when newline are involved, words when everything fits on
   one line.
*/
text c_text_entity(entity module, entity e, int margin, list * ppdl, bool init_p)
{
  list el = CONS(ENTITY, e, NIL);
  list il = CONS(EXPRESSION, int_to_expression(init_p? 1 : 0), NIL);
  // No implicit "extern" keyword
  il = CONS(EXPRESSION, int_to_expression(0), NIL);
  text t =  c_text_related_entities(module, el, margin, 0, ppdl, il);
  gen_free_list(el);
  gen_full_free_list(il);

  return t;
}

text c_text_entity_simple(entity module, entity e, int margin)
{
  list pdl = NIL; // pdl is useless in Fortran or in some debugging situations
  bool init_p = true;
  text t = c_text_entity(module, e, margin, &pdl, init_p);
  gen_free_list(pdl);

  return t;
}
