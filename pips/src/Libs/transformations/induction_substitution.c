/*

 $Id: induction_substitution.c 23495 2018-10-24 09:19:47Z coelho $

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
#ifdef BUILDER_INDUCTION_SUBSTITUTION

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
#include "prettyprint.h" // for debugging
#include "text-util.h" // dump_text

#include "control.h" // clean_up_sequences, module_reorder

#include "transformer.h"     // used
#include "semantics.h"       // used
#include "effects-generic.h" // used

/* Context used for substitution with gen_context_recurse */
typedef struct {
  entity to_substitute; /* The induction variable */
  expression substitute_by; /* The substitution expression */
  bool substitution_occured_p; /* flag to detect a substitution */
  instruction root_instruction; /* instruction holding all the stuff we're working on */
} substitute_ctx;

/** \fn static bool is_modified_entity_in_transformer( transformer T, entity ent )
 *  \brief Check in transformer if the entity ent is not (potentially) modified
 *  \param T the transformer that will be checked
 *  \param ent the entity we are looking for
 *  \return true if entity ent has been found in the transformer T
 */
static bool is_modified_entity_in_transformer( transformer T, entity ent ) {
    bool is_modified = false;

    list entities = transformer_arguments( T );

    for ( list el = entities; !ENDP( el ); POP( el ) ) {
        if ( ENTITY( CAR( el ) ) == ent ) {
            is_modified = true;
            break;
        }
    }
    return is_modified;
}


/**
 * Use transformer associated to the loop to check that variable v is invariant
 */
static bool loop_invariant_p( Variable v, list /* of statements */ loops ) {
  bool result = true;
  FOREACH(statement, s, loops) {
    transformer t = load_statement_transformer( s );
    if( is_modified_entity_in_transformer(t,(entity)v ) ) {
      result = false;
    }
  }

  if(result) pips_debug(4,"%s is a loop invariant !\n",entity_name((entity)v));
  else pips_debug(4,"%s is not a loop invariant !\n",entity_name((entity)v));

  return result;
}

/**
 * \brief check if the instruction is a --
 */
static bool decrement_call_p( call c ) {
  return  native_call_p( c, POST_DECREMENT_OPERATOR_NAME ) //
       || native_call_p( c, PRE_DECREMENT_OPERATOR_NAME )  //
       ;
}

/**
 * \brief check if the call is a ++
 */
static bool increment_call_p( call c ) {
  return  native_call_p( c, POST_INCREMENT_OPERATOR_NAME ) //
       || native_call_p( c, PRE_INCREMENT_OPERATOR_NAME )  //
       ;
}


/**
 * \brief check if the call is a post operator ; like in i++ or i--
 */
static bool post_inc_or_de_crement_call_p(call c) {
  return  native_call_p( c, POST_INCREMENT_OPERATOR_NAME ) //
       || native_call_p( c, POST_DECREMENT_OPERATOR_NAME )  //
       ;
}


/** \fn static bool reference_substitute( expression e, substitute_ctx *ctx )
 *  \brief callback for gen_recurse
 *  called during bottom-up phase on expression,
 *  in fact we aim to filter reference expressions only
 *  It will used context ctx to substitute references
 *  to ctx->to_substitute by the expression ctx->substitute_by
 *  \param e the expression that may contain a reference to the induction variable
 *  \param ctx the context contains the induction variable, and the substitute expression.
 */
static void reference_substitute( expression e, substitute_ctx *ctx ) {
    /* We filter expression that are references */
    if ( syntax_reference_p( expression_syntax( e ) ) ) {
        /* Check if the reference is the variable we aim to substitute */
        if ( reference_variable( syntax_reference ( expression_syntax( e ) ) ) == ctx->to_substitute ) {

            ifdebug(6) {
                pips_debug( 6, "Find substitution :" );
                print_expression( e );
                pips_debug( 6, "Will replace by :" );
                print_expression( ctx->substitute_by );
            }

            /* Delete the old syntax (no leak ;-))*/
            free_syntax( expression_syntax( e ) );
            /* Substitute by new one */
            expression_syntax( e ) = copy_syntax( expression_syntax( ctx->substitute_by ) );
            expression_normalized( e ) = normalized_undefined;
        }
    }
}


/**
 *  \brief Return an expression corresponding to the right part of an assignment
 *  \param c the call from which we want the right part
 *  \return the expression corresponding to right part of an assignment,
 *  or expression_undefined if instruction i is not an assignment.
 */
static expression get_right_part_of_assignment( call c ) {
    expression e = expression_undefined;
    /* call must be an assignment or a self modifying operator : += /= *= -= */
    if ( native_call_p( c, ASSIGN_OPERATOR_NAME ) //
            || native_call_p( c, MULTIPLY_UPDATE_OPERATOR_NAME ) //
            || native_call_p( c, DIVIDE_UPDATE_OPERATOR_NAME ) //
            || native_call_p( c, PLUS_UPDATE_OPERATOR_NAME ) //
            || native_call_p( c, MINUS_UPDATE_OPERATOR_NAME ) ) {

      /* Right part of assignment is the arguments of the call but the first
       * one (CDR jump it) */
      e = EXPRESSION( CAR( CDR( call_arguments( c ) ) ) );
    }
    return e;
}


/**
 * Substitute in an expression, this is a callback for gen_context_recurse
 * It'll find all call and when the induction variable is on the left side,
 * it'll replace the call with an equivalent expression using the substitute
 * expression
 */
static bool substitute_in_call( call c, substitute_ctx *ctx) {
  entity induction_variable_candidate = ctx->to_substitute;
  expression substitute = ctx->substitute_by;

  /* Sanity check */
  if ( call_undefined_p(c) ) {
    pips_user_error("call is undefined (and shouldn't be) !\n");
  }

  /* Sanity check : we need at least an argument :) */
  if( !call_arguments(c)) {
    return true;
  }

  //
  expression unsugarized = expression_undefined;

  /* We want induction_variable_candidate to be the left part of the call */
  expression e = EXPRESSION( CAR( call_arguments( c ) ) );
  if (expression_reference_p( e )
      && is_expression_reference_to_entity_p(e, induction_variable_candidate)){

    /* This call is candidate to a replacement, check if we can handled it ! */


    /* In the case of unary operator, prepare the assignment
     */
    bool increment_p = increment_call_p( c );
    bool decrement_p = decrement_call_p( c );

    if(increment_p || decrement_p ) {
      if( increment_call_p( c ) ) {
        unsugarized = make_op_exp(  PLUS_OPERATOR_NAME , //
                                      substitute, //
                                      int_to_expression(1) );
      } else if( decrement_call_p( c ) ) {
        unsugarized = make_op_exp(  MINUS_OPERATOR_NAME , //
                                      substitute, //
                                      int_to_expression(1) );
      }

    } else {
      /* We'll assume i isn't modified on the right hand side !
       * There might be some weird "valid" statement like i = i++ && ... as &&
       * is a synchronization point. More work required on the standard here :-(
       */
      expression substitute_on = get_right_part_of_assignment( c );
      if(!expression_undefined_p(substitute_on)) {

        // We have a right part of an assignment, we can replace :)
        gen_context_recurse ( substitute_on, ctx,
                              expression_domain,
                              gen_true2,
                              reference_substitute );

        /* Force to generate again the normalized field of the expression */
        expression_normalized(substitute_on) = NormalizeExpression( substitute_on );

        /* Handle "update" affection (+=, -= , ...)
         * Transform z += 1 in z = induction + 1
         */
        if ( native_call_p( c, MULTIPLY_UPDATE_OPERATOR_NAME ) ) {
          unsugarized = make_op_exp( ( MULTIPLY_OPERATOR_NAME ), //
                                        substitute, //
                                        copy_expression( substitute_on ) );
        } else if ( native_call_p( c, DIVIDE_UPDATE_OPERATOR_NAME ) ) {
          unsugarized = make_op_exp( ( DIVIDE_OPERATOR_NAME ), //
                                        substitute, //
                                        copy_expression( substitute_on ) );
        } else if ( native_call_p( c, PLUS_UPDATE_OPERATOR_NAME ) ) {
          unsugarized = make_op_exp( ( PLUS_OPERATOR_NAME ), //
                                        substitute, //
                                        copy_expression( substitute_on ) );
        } else if ( native_call_p( c, MINUS_UPDATE_OPERATOR_NAME ) ) {
          unsugarized = make_op_exp( ( MINUS_OPERATOR_NAME ), //
                                        substitute, //
                                        copy_expression( substitute_on ) );
        }
      }
    }
  }

  if ( !expression_undefined_p( unsugarized ) ) {

      ifdebug( 1 ) {
          pips_debug( 1, "Before update assignment : " );
          print_expression( call_to_expression(c) );
          fprintf(stderr,"\n");
      }

      /* Force to generate again the normalized field of the expression */
      expression_normalized(unsugarized) = NormalizeExpression( unsugarized );

      /* FIXME : free argument list for the call */
      // ...

      /* Construct the unsugarized call */
      call new_call = make_call(entity_intrinsic( ASSIGN_OPERATOR_NAME ), //
                                CONS( EXPRESSION, //
                                      entity_to_expression( induction_variable_candidate ), //
                                      CONS(EXPRESSION, unsugarized, NIL ) ) );


      if(post_inc_or_de_crement_call_p(c)) {
        /* It's a separate case since there's no right hand side and we have to
         * be sioux enough if it's a post increment :
         * i++ has to be replaced by (i=i+1,i-1) so that the old value is returned
         */

        /* if we have only k++; then no return value is needed. This occurs
         * when ancestor is an instruction
         */
        instruction owner = ctx->root_instruction;
        if(!(instruction_call_p(owner) && instruction_call(owner)==c)) {
          expression minus;
          minus = make_op_exp( ( MINUS_OPERATOR_NAME ), //
                                  entity_to_expression( induction_variable_candidate), //
                                  int_to_expression(1) );
          new_call = make_call(entity_intrinsic( COMMA_OPERATOR_NAME ),
                               CONS(EXPRESSION,
                                    call_to_expression(new_call),
                                    CONS(EXPRESSION, minus, NIL)));
        }
      }


//call_assign_contents(c,new_call); // Fails badly :-(
      *c = *new_call;

      ctx->substitution_occured_p = true;

      ifdebug( 1 ) {
          pips_debug( 1, "Unsugar update assignment : " );
          print_expression( call_to_expression(c) );
      }
  }


  return true;
}

/**
 * This function replace the variable induction_variable_candidate by expression
 * substitute in call c.
 * @param substitute is the replacement expression
 * @param induction_variable_candidate is the variable to replace
 * @param c is the call on which the substitution will occur. It'll be
 * modified by side effect
 */
static bool expression_subtitution_on_call( expression substitute,
                                            entity induction_variable_candidate,
                                            call c,
                                            instruction root_instruction) {
  ifdebug( 1 ) {
      pips_debug(1, "Induction substitution : %s => ", //
              entity_local_name( induction_variable_candidate ) );
      print_syntax( expression_syntax( substitute ) );
      fprintf(stderr, " on call : " );
      print_expression(call_to_expression(c)); // Leak...
      fprintf( stderr, "\n" );
  }

  substitute_ctx ctx;
  ctx.to_substitute = induction_variable_candidate;
  ctx.substitute_by = substitute;
  ctx.substitution_occured_p = false;
  ctx.root_instruction = root_instruction;

  gen_context_recurse(c, &ctx, call_domain, substitute_in_call, gen_null2);

  return ctx.substitution_occured_p;
}


/** \fn static bool subtitute_induction_statement_in( statement s )
 *  \brief Call during top-down phase while recursing on statements
 *  Will use precondition on each assignment statement to construct
 *  substitution expression when possible
 *  \param s the statement that will be checked
 *  \return always true
 */
static bool subtitute_induction_statement_in( statement s ) {
  bool result = true;

  ifdebug( 1 ) {
    pips_debug( 1, "Statement:\n" );
    print_statement( s );
  }

  // Get enclosing loops
  list loops = load_statement_enclosing_loops(s);
  if ( !ENDP( loops ) && !statement_loop_p(s) ) {
    /* s is not a loop, but we must be somewhere inside a loop since we have some (useful) loop_indices */

    /* We'll evaluate now the instruction */
    instruction stmt_instr = statement_instruction( s );
    
    call the_call = call_undefined;

    if( instruction_call_p( stmt_instr ) ) {
      the_call = instruction_call( stmt_instr );
    } else if(instruction_test_p(stmt_instr)) {
      expression cond = test_condition(instruction_test(stmt_instr));
      if(expression_call_p(cond)) {
        the_call = expression_call(cond);
      }
    }

    if(!call_undefined_p(the_call)) {
      /* The precondition will be used for building a substitution expression */
      transformer prec = load_statement_precondition( s );

      ifdebug( 5 ) {
        pips_debug( 5, "Preconditions:\n" );
        text tmp = text_transformer( prec );
        dump_text( tmp );
        free_text( tmp );
        pips_debug( 5, "Transformers:\n" );
        tmp = text_transformer( load_statement_transformer( s ) );
        dump_text( tmp );
        free_text( tmp );
        print_statement( s );
        pips_debug( 5, "Nb of enclosing loops : %d\n", (int)gen_length(loops) );
      }

      /* Get the set of preconditions equations from which we'll build substitution expressions  */
      transformer trans_range = transformer_range( prec );
      Psysteme D = predicate_system( transformer_relation( transformer_range( prec ) ) );
      Pcontrainte eqs = sc_egalites( D );
      Pcontrainte c;

      /* Loop over equations
         for each one we will evaluate if it can be used to produce a substitution expression,
         and if applicable, we'll use this expression to make the substitution. */
      for ( c = eqs; !CONTRAINTE_UNDEFINED_P( c ); c = contrainte_succ( c ) ) {
        Pvecteur vec = contrainte_vecteur( c );
        Pvecteur p;

        /* Loop over variable in this equation
           simple induction variables are detected
           The condition is that the equation has to involve only loop
           indices, a constant, and the variable itself */

        bool found_loop_index = false; /* flag to keep track if we have find at least one loop index */
        expression substitute = expression_undefined; /* the substitution expression */
        Variable induction_variable_candidate = entity_undefined; /* the variable to substitute */
        int induction_variable_candidate_coeff = 0; /* the coefficient associated to the variable */

        for ( p = vec; !VECTEUR_NUL_P( p ); p = vecteur_succ( p ) ) {
          Variable v = vecteur_var( p ); /* Current variable */
          Value coeff = vecteur_val( p ); /* Associate coefficient */
          expression local_expr = expression_undefined; /* will be used to compute "coeff*v" */

          if ( v == TCST ) {
            /* This is the constant term in the equation */
            local_expr = int_to_expression( coeff );
          } else {
            /* We have a variable */

            if(index_of_a_loop_p(v, loops) || loop_invariant_p(v, loops)) {
              /* We have found a loop index */
              found_loop_index = true;
              /* We build an expression "coeff*v" */
              if ( coeff == -1 ) {
                /* Coeff is -1, we want "-v" instead of "-1 * v" */
                local_expr = MakeUnaryCall( entity_intrinsic( UNARY_MINUS_OPERATOR_NAME ), //
                                            entity_to_expression( v ) );
              } else if ( coeff == 1 ) {
                /* Coeff is 1, we want "v" instead of "1 * v" */
                local_expr = entity_to_expression( v );
              } else {
                /* General case : produce "coeff*v" */
                local_expr = make_op_exp( ( MULTIPLY_OPERATOR_NAME ), //
                                             int_to_expression( coeff ), //
                                             entity_to_expression( v ) );
              }
            } else if ( !entity_undefined_p( induction_variable_candidate ) ) {
              /* We have a variable that is not a loop index,
               * but we already have one, so we abort substitution */
              pips_debug(5,"We already have an induction candidate for this"
                         "equation (%s) and encounter a new one (%s), so skip "
                         "this equation...",
                         entity_local_name(induction_variable_candidate ),
                         entity_local_name(v));
              induction_variable_candidate = entity_undefined;
              break;
            } else {
              /* We have a variable that is not a loop index,
               * and it's the first one, so record it */
              induction_variable_candidate = v;
              /* we have to take the opposite (-coeff) because we want
               * to go from coeff*x+b=0 to x=b/(-coeff) */
              induction_variable_candidate_coeff = -coeff;
            }
          }

          if ( !expression_undefined_p( local_expr ) ) {
            /* we have a local_expr (loop index or constant) */
            if ( expression_undefined_p( substitute ) ) {
              /* it's the first one */
              substitute = local_expr;
            } else {
              /* it's not the first one, we chain it with a "+" operation */
              substitute = make_op_exp(  PLUS_OPERATOR_NAME , //
                                           local_expr, //
                                           substitute );
            }
          }

          ifdebug( 5 ) {
            if ( !expression_undefined_p( substitute ) ) {
              pips_debug( 5, "Expression : " );
              print_syntax( expression_syntax( substitute ) );
              fprintf( stderr, "\n" );
            }
          }
        }


        ifdebug(4) {
          if ( found_loop_index ) {
            pips_debug(4,"Loop index found !\n");
          } else {
            pips_debug(4,"No loop index found !\n");
          }
          if ( !entity_undefined_p( induction_variable_candidate )) {
            pips_debug(4,"Induction variable candidate found : %s\n",
                       entity_local_name(induction_variable_candidate));
          } else {
            pips_debug(4,"No Induction variable candidate found !\n");
          }
          if ( induction_variable_candidate_coeff != 0) {
            pips_debug(4,"Variable is active !\n");
          } else {
            pips_debug(4,"Variable is not active !\n");
          }
          if ( !expression_undefined_p( substitute )) {
            pips_debug(4,"The substitute expression is ");
            print_syntax( expression_syntax( substitute ) );
            fprintf( stderr, "\n" );
          } else {
            pips_debug(4,"The substitute expression is undefined.\n");
          }
          if( is_modified_entity_in_transformer(
              load_statement_transformer( s ), //
              induction_variable_candidate ) ) {
            pips_debug(4,"Variable is modified by this statement\n");
          } else {
            pips_debug(4,"Variable is not modified by this statement\n");
          }
        }

        if ( found_loop_index // The expression depends on loop index
            // We have found an induction variable
            && !entity_undefined_p( induction_variable_candidate ) //
            // The variable is really active (this check shouldn't be useful ?)
            && induction_variable_candidate_coeff != 0 //
            // We have a substitution expression to use :-)
            && !expression_undefined_p( substitute ) //
           ) {

          /* Add final division using the coeff */
          if ( induction_variable_candidate_coeff == -1 ) {
            /* Instead of dividing by -1, we rather use
             * unary minus in front of expression */
            substitute = make_op_exp(  MINUS_OPERATOR_NAME ,
                    int_to_expression(0),
                                        substitute );
          } else if ( induction_variable_candidate_coeff != 1 ) {
            /* General case */
            substitute = make_op_exp(  DIVIDE_OPERATOR_NAME , //
                                         substitute, //
                                         int_to_expression( induction_variable_candidate_coeff ) );
          }

          if(is_modified_entity_in_transformer(load_statement_transformer( s ),
                                               induction_variable_candidate )) {
            // Variable is modified by this statement
            expression_subtitution_on_call(substitute,
                                           induction_variable_candidate,
                                           the_call,
                                           stmt_instr);
          } else {
            // Variable is not modified by this statement
            substitute_ctx ctx;
            ctx.to_substitute = induction_variable_candidate;
            ctx.substitute_by = substitute;
            ctx.substitution_occured_p = false;

            gen_context_recurse ( the_call, &ctx,
              expression_domain, gen_true2, reference_substitute );

          }
        }

        /* Free substitute expression */
        if ( !expression_undefined_p( substitute ) ) {
          // FIXME free_expression( substitute );
        }
      }
      /* Try to avoid memory leak */
      empty_transformer( trans_range );
      transformer_free( trans_range );
    }
  }
  return result;
}

/** \fn bool induction_substitution( char * module_name )
 *  \brief This pass implement the detection and the substitution
 *  of induction variable in loop
 *  \param module_name the name of the module to work on
 *  \return currently always true
 */
bool induction_substitution(const string module_name)
{
    entity module;
    statement module_stat;

    set_current_module_entity( module_name_to_entity( module_name ) );
    module = get_current_module_entity( );

    set_current_module_statement( (statement) db_get_memory_resource( DBR_CODE, module_name, true ) );
    module_stat = get_current_module_statement( );

    set_cumulated_rw_effects( (statement_effects) db_get_memory_resource( DBR_CUMULATED_EFFECTS, module_name, true ) );
    set_proper_rw_effects( (statement_effects) db_get_memory_resource( DBR_PROPER_EFFECTS, module_name, true ) );
    module_to_value_mappings( module );

    set_precondition_map( (statement_mapping) db_get_memory_resource( DBR_PRECONDITIONS, module_name, true ) );

    set_transformer_map( (statement_mapping) db_get_memory_resource( DBR_TRANSFORMERS, module_name, true ) );

    debug_on( "INDUCTION_SUBSTITUTION_DEBUG_LEVEL" );
    pips_debug( 1, "begin\n" );


    pips_debug(6, "finding enclosing loops ...\n");
    set_enclosing_loops_map( loops_mapping_of_statement( module_stat ) );

    /* We now traverse our module's statements. */
    gen_recurse( module_stat,
      statement_domain, subtitute_induction_statement_in, gen_null );

    /* Sanity checks */
    pips_assert( "Consistent final check\n", gen_consistent_p( (gen_chunk *)module_stat ) );

    pips_debug( 1, "end\n" );
    debug_off();

    /* Save modified code to database */
    module_reorder( module_stat );
    DB_PUT_MEMORY_RESOURCE( DBR_CODE, strdup( module_name ), module_stat );

    clean_enclosing_loops( );

    reset_current_module_entity( );
    reset_current_module_statement( );

    reset_cumulated_rw_effects( );
    reset_proper_rw_effects( );
    reset_precondition_map( );
    reset_transformer_map( );

    free_value_mappings( );

    /* Return value */
    bool good_result_p = true;

    return ( good_result_p );

}

#endif // BUILDER_INDUCTION_SUBSTITUTION
