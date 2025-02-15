/*

  $Id: interprocedural.c 23412 2017-08-09 15:07:09Z irigoin $

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
/* package generic effects :  Be'atrice Creusillet 5/97
 *
 * File: interprocedural.c
 * ~~~~~~~~~~~~~~~~~~~~~~~
 *
 * This File contains the generic functions necessary for the interprocedural
 * computation of all types of in effects.
 *
 */

#include <stdio.h>
#include <string.h>

#include "genC.h"
#include "linear.h"
#include "ri.h"
#include "effects.h"
#include "text.h"

#include "misc.h"
#include "text-util.h"
#include "ri-util.h"
#include "prettyprint.h"
#include "effects-util.h"

#include "effects-generic.h"

#include "semantics.h"

#define min(a,b) (((a)<(b))?(a):(b))
#define max(a,b) (((a)>(b))?(a):(b))


extern string compilation_unit_of_module(const char *);

/**************************************************** FORTRAN */

/**

 This function translates the list of effects l_sum_eff summarizing the
 effects of module callee from its name space to the name space of the
 caller, that is to say the current module being analyzed.
 It is generic, which means that it does not depend on the representation
 of effects. There is another similar function for C modules.

 @param callee is the called module
 @param real_args is the list of actual arguments
 @param l_sum_eff is the list of summary effects for function func
 @return a list of effects in the caller name space

 */
list generic_fortran_effects_backward_translation(
    entity callee,
    list /* of expression */ real_args,
    list /* of effect */ l_sum_eff,
    transformer context)
{
  list le;
  // functions that can be pointed by fortran_effects_backward_translation_op:
  // simple_effects_backward_translation
  // convex_regions_backward_translation
  le = (*fortran_effects_backward_translation_op)(callee, real_args, l_sum_eff,
      context);
  return le;

}

/************************************************************ C */

static list 
c_address_of_actual_argument_to_may_summary_effects(expression arg1,
						    tag act)
{
  list l_res = NIL, l_tmp = NIL;

  pips_debug(5, "address_of case \n");
  list l_real_arg_eff = NIL;
  l_tmp = generic_proper_effects_of_complex_address_expression
    (arg1, &l_real_arg_eff, true);
  effects_free(l_tmp);

  FOREACH(EFFECT, real_arg_eff, l_real_arg_eff) {
    if (anywhere_effect_p(real_arg_eff)) {
      pips_debug(6, "anywhere effects \n");
      l_res = gen_nconc
	(l_res,
	 effect_to_effects_with_given_tag(real_arg_eff, act));
    }
    else {
      type eff_type =  expression_to_type(arg1);
      reference eff_ref = effect_any_reference(real_arg_eff);
      list last_ind = gen_last(reference_indices(eff_ref));
      if(!ENDP(last_ind)) {
	/* The operand of & is subcripted */
	/* the effect last index must be changed to '*' if it's
	 * not already the case and if it is not a structure or
	 * union field.
	 */
	expression n_exp;
	expression last_eff_ind = EXPRESSION(CAR(last_ind));
	bool field_p = false;
	/* first check if the last index is a structure field */
	if (expression_reference_p(last_eff_ind)) {
	  field_p = entity_field_p(reference_variable(expression_reference(last_eff_ind)));
	}
	if(!field_p && !unbounded_expression_p(last_eff_ind)) {
	  n_exp = make_unbounded_expression();
	  // functions that can be pointed by effect_change_ith_dimension_expression_func:
	  // simple_effect_change_ith_dimension_expression
	  // convex_region_change_ith_dimension_expression
	  (*effect_change_ith_dimension_expression_func)
	    (real_arg_eff, n_exp,
	     gen_length(reference_indices(eff_ref)));
	  free_expression(n_exp);
	}
      }

      l_res = gen_nconc
	(l_res,
	 generic_effect_generate_all_accessible_paths_effects_with_level
	 (real_arg_eff,
	  eff_type,
	  act,
	  true,
	  10, /* to avoid too long paths until GAPS are handled */
	  false));
    }
    gen_free_list(l_real_arg_eff);
  }
  return l_res;
}

/**

 @param real_arg the real argument expression
 @param act is a tag to choose the action of the main effect :
        'r' for read, 'w' for write, and 'x' for read and write.
 @return a list of effects corresponding to the possible effects
         the function could do on the actual argument

 */
list c_actual_argument_to_may_summary_effects(expression real_arg, tag act)
{
  list l_res = NIL, l_tmp;

  // type real_arg_t = expression_to_type(real_arg);
  type real_arg_t = points_to_expression_to_concrete_type(real_arg);
  int real_arg_t_d = effect_type_depth(real_arg_t);
  transformer context;

  if (!effects_private_current_context_stack_initialized_p()
      || effects_private_current_context_empty_p())
    context = transformer_undefined;
  else
    context = effects_private_current_context_head();

  pips_debug(6,"actual argument %s, with type %s, and type depth %d\n",
      expression_to_string(real_arg),
      type_to_string(real_arg_t), real_arg_t_d);

  if (real_arg_t_d == 0)
  {
    pips_debug(6, "actual argument is a constant expression -> NIL\n");
  }
  else
  {
    syntax s = expression_syntax(real_arg);

    switch(syntax_tag(s))
    {
    case is_syntax_call:
      /*
       * Two special call cases for :
       * - the assignment
       * - and the ADDRESS_OF operator to avoid
       * losing to musch information because we don't know how to
       * represent &p access path in the general case.
       */
    {
      call real_call = syntax_call(s);
      entity real_op = call_function(real_call);
      list args = call_arguments(real_call);

      if (ENTITY_ASSIGN_P(real_op)) {
        pips_debug(5, "assignment case \n");
        l_res  = c_actual_argument_to_may_summary_effects
            (EXPRESSION(CAR(CDR(args))), act);
        break;
      }
      else if(ENTITY_ADDRESS_OF_P(real_op)) {
        expression arg1 = EXPRESSION(CAR(args));
	l_res = c_address_of_actual_argument_to_may_summary_effects(arg1, act);
        break;
      }
    }
    // no break
    _FALLTHROUGH_;
    case is_syntax_reference:
    case is_syntax_subscript:
    {
      list l_real_arg_eff = NIL;
      pips_debug(5, "general call, reference or subscript case \n");
      l_tmp = generic_proper_effects_of_complex_address_expression
          (real_arg, &l_real_arg_eff, true);
      effects_free(l_tmp);

      FOREACH(EFFECT, real_arg_eff, l_real_arg_eff)
      {
        if (anywhere_effect_p(real_arg_eff))
        {
          pips_debug(6, "anywhere effects \n");
          l_res = gen_nconc
              (l_res,
                  effect_to_effects_with_given_tag(real_arg_eff,
                      act));
        }
        else
        {
          /* l_res = gen_nconc
                     (l_res,
                     generic_effect_generate_all_accessible_paths_effects
                     (real_arg_eff, real_arg_t, act)); */
          l_res = gen_nconc
              (l_res,generic_effect_generate_all_accessible_paths_effects_with_level(real_arg_eff,
                  real_arg_t,
                  act,
                  false,
                  10, /* to avoid too long paths until GAPS are handled */
                  false));
        }
      }
      gen_free_list(l_real_arg_eff);
    }
    break;
    case is_syntax_cast:
    {
      l_res = c_actual_argument_to_may_summary_effects
          (cast_expression(syntax_cast(s)), act);
    }
    break;
    case is_syntax_sizeofexpression:
    {
      /* generate no effects : this case should never appear because
       * of the test if (real_arg_t_d == 0)
       */
    }
    break;
    case is_syntax_va_arg:
    {
      list al = syntax_va_arg(s);
      sizeofexpression ae = SIZEOFEXPRESSION(CAR(al));
      l_res = c_actual_argument_to_may_summary_effects
          (sizeofexpression_expression(ae), act);
      break;
    }
    default:
      pips_internal_error("case not handled");
      break;
    }

  } /* else du if (real_arg_t_d == 0) */

  // functions that can be pointed by effects_precondition_composition_op:
  // effects_composition_with_preconditions_nop
  // convex_regions_precondition_compose
  if (!transformer_undefined_p(context))
    (*effects_precondition_composition_op)(l_res, context, false);

  effects_to_may_effects(l_res);

  ifdebug(6)
  {
    pips_debug(6, "end, resulting effects are :\n");
    (*effects_prettyprint_func)(l_res);
  }
  return(l_res);
}

/* remove the current element from the list */
static void remove_current_element_from_effect_list(list * l_begin, list *l_current, list l_prec)
{
  if (*l_begin == *l_current)
    {
      *l_current = CDR(*l_current);
      CDR(*l_begin) = NIL;
      gen_free_list(*l_begin);
      *l_begin = *l_current;
    }
  else
    {
      CDR(l_prec) = CDR(*l_current);
      CDR(*l_current) = NIL;
      gen_free_list(*l_current);
      *l_current = CDR(l_prec);
    }
}

static void skip_current_element_from_effect_list(list *l_current, list * l_prec)
{
  *l_prec = *l_current;
  *l_current = CDR(*l_current);
}

/**
 This function translates the list of effects l_sum_eff summarizing
 the effects of module callee from its name space to the name space of
 the caller, that is to say the current module being analyzed.  It is
 generic, which means that it does not depend on the representation of
 effects. There is another similar function for fortran modules.

 @param callee is the called module
 @param real_args is the list of actual arguments
 @param l_sum_eff is the list of summary effects for function func
 @param the current precondition if available
 @return a list of effects in the caller name space

*/
list generic_c_effects_backward_translation(entity callee,
    list /* of expression */ real_args,
    list /* of effect */ l_sum_eff,
    transformer context)
{
  list l_begin = gen_copy_seq(l_sum_eff); /* effects are not copied */
  list l_prec = NIL, l_current;
  list l_eff = NIL; /* proper effect list to be returned */
  list ra;
  bool param_varargs_p = false;
  type callee_ut = entity_basic_concrete_type(callee);
  functional f = type_functional(callee_ut);
  list formal_args = functional_parameters(f);
  int arg_num;

  ifdebug(2)
  {
    pips_debug(2, "begin for function %s\n", entity_local_name(callee));
    pips_debug(2, "with actual arguments :\n");
    print_expressions(real_args);
    pips_debug(2, "and effects :\n");
    (*effects_prettyprint_func)(l_sum_eff);
  }

  // functions that can be pointed by effects_translation_init_func:
  // simple_effects_translation_init
  // convex_regions_translation_init
  (*effects_translation_init_func)(callee, real_args, true);

  /* first, take care of global and formal context effects */

  set binding = safe_user_call_to_points_to_interprocedural_binding_set(callee, real_args);
  l_current = l_begin;
  l_prec = NIL;
  while(!ENDP(l_current))
  {
    effect eff = EFFECT(CAR(l_current));
    reference r = effect_any_reference(eff);
    entity v = reference_variable(r);

    if(!formal_parameter_p(v))
    {
      /* This effect must be either a global effect or an effect
       * on the global context if points-to information is used.
       *
       * A global effect does not require a translation in
       * C. However, it may not be in the scope of the caller.
       *
       * A formal context effect must be translated.
       *
       * In both cases, the descriptor, when it exists, must be
       * translated.
       */
      if(global_variable_p(v)) { // even if it also is a stub
	effect n_eff = (*effect_dup_func)(eff);
        (*effect_descriptor_interprocedural_translation_op)(n_eff);
	l_eff = gen_nconc(l_eff, CONS(EFFECT, n_eff, NIL));
      }
      else if(entity_stub_sink_p(v)) {
        list n_effects
	  = backward_translation_of_points_to_formal_context_effect(callee, real_args, eff, binding);
        FOREACH(EFFECT, n_effect, n_effects) {
          // functions that can be pointed by effect_descriptor_interprocedural_translation_op:
          // simple_effect_descriptor_interprocedural_translation
          // convex_region_descriptor_translation
          (*effect_descriptor_interprocedural_translation_op)(n_effect);
        }
        l_eff = gen_nconc(l_eff, n_effects);
      }
      else { 
	/* Heap and package effects are simply copied, no translation
	   required */
	// extern string effect_to_string(effect); // in effects-simple and not effects-util
	//pips_user_warning("Translation error for \"%s\".\n",
	//		  effect_to_string(eff));
        // functions that can be pointed by effect_dup_func:
        // simple_effect_dup
        // region_dup
        // copy_effect
        effect n_eff = (*effect_dup_func)(eff);
        // functions that can be pointed by effect_descriptor_interprocedural_translation_op:
        // simple_effect_descriptor_interprocedural_translation
        // convex_region_descriptor_translation
        (*effect_descriptor_interprocedural_translation_op)(n_eff);
        l_eff = gen_nconc(l_eff,CONS(EFFECT, n_eff, NIL));
      }

      remove_current_element_from_effect_list(&l_begin, &l_current, l_prec);
    }
    else {
      skip_current_element_from_effect_list(&l_current, &l_prec);
    }
  } /* while */

  ifdebug(5)
  {
    pips_debug(5, "translated global effects :\n");
    (*effects_prettyprint_func)(l_eff);
    pips_debug(5, "remaining effects :\n");
    (*effects_prettyprint_func)(l_begin);
  }

  /* then, handle effects on formal parameters */

  for (ra = real_args, arg_num = 1; !ENDP(ra); ra = CDR(ra), arg_num++)
  {
    expression real_arg = EXPRESSION(CAR(ra));
    parameter formal_arg;
    type te;
    bool spurious_real_arg_p = false;

    pips_debug(5, "current real arg : %s\n", expression_to_string(real_arg));

    if (!param_varargs_p)
    {
      if(ENDP(formal_args)) {
        semantics_user_warning("Function \"%s\" is called with too many arguments in function \"%s\" \n",
            entity_user_name(callee),
            entity_user_name(get_current_module_entity()));
        spurious_real_arg_p = true;
      }
      else {
        formal_arg = PARAMETER(CAR(formal_args));
        te = parameter_type(formal_arg);
        pips_debug(8, "parameter type : %s\n", type_to_string(te));
        param_varargs_p = param_varargs_p || type_varargs_p(te);
      }
    }

    if (param_varargs_p)
    {
      pips_debug(5, "vararg case \n");
      l_eff = gen_nconc(l_eff,
          c_actual_argument_to_may_summary_effects(real_arg,
              'x'));
    }
    else if (!spurious_real_arg_p)
    {
      list l_eff_on_current_formal = NIL;

      dummy formal_arg_dummy = parameter_dummy(formal_arg);
      if (!dummy_unknown_p(formal_arg_dummy))
        pips_debug(5, "corresponding formal argument :%s\n",
            entity_name(dummy_identifier(formal_arg_dummy))
        );
      else
        pips_debug(5, "unknown dummy\n");

      /* first build the list of effects on the current formal argument */
      l_current = l_begin;
      l_prec = NIL;
      while(!ENDP(l_current))
      {
        effect eff = EFFECT(CAR(l_current));
        reference eff_ref = effect_any_reference(eff);
        entity eff_ent = reference_variable(eff_ref);

        if (ith_parameter_p(callee, eff_ent, arg_num))
        {
          bool exact_p = false;
          /* Whatever the real_arg may be if there is an effect on
           * the sole value of the formal arg, it generates no effect
           * on the caller side.
           */
          if (ENDP(reference_indices(eff_ref))
              ||
              (!entity_array_p(eff_ent) // to work around the fact that formal arrays are not internally represented as pointers for the moment
                  && !effect_reference_dereferencing_p(eff_ref, &exact_p))) // for structs and unions
          {
            pips_debug(5, "effect on the value of the formal parameter -> skipped\n");
          }
          else
          {
            l_eff_on_current_formal = gen_nconc
                (l_eff_on_current_formal, CONS(EFFECT,eff, NIL));
          }
          /*   c_summary_effect_to_proper_effects(eff, real_arg));*/
	  remove_current_element_from_effect_list(&l_begin, &l_current, l_prec);
	}
	else {
	  skip_current_element_from_effect_list(&l_current, &l_prec);
	}
      } /* while */

      ifdebug(5)
      {
        pips_debug(5, "effects on current formal argument:\n");
        (*effects_prettyprint_func)(l_eff_on_current_formal);
      }

      /* Eliminate callee stubs in the predicate
       *
       * Should be included in
       * c_effects_on_formal_parameter_backward_translation_func() but
       * we have to cope with argument "binding".
       */
      if(!set_undefined_p(binding)) {
	FOREACH(EFFECT, eff, l_eff_on_current_formal) {
	  // Function available in convex effects
	  if(descriptor_convex_p(effect_descriptor(eff))) {
	    effect substitute_stubs_in_convex_array_region(effect, bool, set);
	    eff = substitute_stubs_in_convex_array_region(eff, true, binding);
	  }
	}
      }

      /* then translate them if possible */
      if (!ENDP( l_eff_on_current_formal))
      {
        type real_arg_t = expression_to_type(real_arg);
        if (types_compatible_for_effects_interprocedural_translation_p(real_arg_t, te))
        {
          // functions that can be pointed by c_effects_on_formal_parameter_backward_translation_func:
          // c_simple_effects_on_formal_parameter_backward_translation
          // c_convex_effects_on_formal_parameter_backward_translation
          l_eff = gen_nconc
              (l_eff,
                  (*c_effects_on_formal_parameter_backward_translation_func)
                  (l_eff_on_current_formal, real_arg, context));
        }
        else
        {
	  // FI: some work needed to retrieve the formal parameter name...
	  semantics_user_warning("Type of actual parameter, \"%s\", "
				 "incompatible with type of formal parameter, "
				 "\"%s\", for precise interprocedural effect "
				 "translation.\n",
				 type_to_full_string_definition(real_arg_t),
				 type_to_full_string_definition(te));
          bool read_p = false;
          bool write_p = false;
          FOREACH(EFFECT, eff, l_eff_on_current_formal)
          {
            write_p = write_p || effect_write_p(eff);
            read_p = read_p || effect_read_p(eff);
          }

          tag t = write_p ? (read_p ? 'x' : 'w') : 'r';
          l_eff = gen_nconc(l_eff,
              c_actual_argument_to_may_summary_effects(real_arg, t));
        }
        free_type(real_arg_t);
      }

      POP(formal_args);
    } /* else if (!spurious_real_arg_p) */

    /* add the proper effects on the real arg evaluation on any case */
    l_eff = gen_nconc(l_eff, generic_proper_effects_of_c_function_call_argument(real_arg));

  } /* for */

  if(!set_undefined_p(binding))
    set_free(binding);

  /* removed because the parser adds arguments to the function (see ticket 452) */
  /* /\* check if there are too few actual arguments *\/ */
  /*   if (!param_varargs_p && !ENDP(formal_args) && !type_void_p(parameter_type(PARAMETER(CAR(formal_args))))) */
  /*     { */
  /*       pips_user_error("Function \"%s\" is called with too few arguments in function \"%s\" \n", */
  /* 		      entity_user_name(callee), */
  /* 		      entity_user_name(get_current_module_entity())); */
  /*     } */

  pips_debug_effects(5, "effects before fields translation:\n", l_eff);
  //  pips_debug(8, "callee's name is %s, current module name %s\n", entity_name(callee), entity_name(get_current_module_entity()));

  //  string callee_cu_name = compilation_unit_of_module(entity_local_name(callee));
  //  string current_cu_name = compilation_unit_of_module(entity_local_name(get_current_module_entity()));
  //  pips_debug(8, "callee cu name %s, current cu name %s\n", callee_cu_name, current_cu_name);

  effects_translate_fields_compilation_unit(l_eff,
      compilation_unit_of_module(entity_local_name(callee)),
      compilation_unit_of_module(entity_local_name(get_current_module_entity())));


  // functions that can be pointed by effects_translation_end_func:
  // simple_effects_translation_end
  // convex_regions_translation_end
  (*effects_translation_end_func)();

  ifdebug(5)
  {
    pips_debug(5, "resulting effects :\n");
    (*effects_prettyprint_func)(l_eff);
  }

  return (l_eff);
}

list generic_c_effects_forward_translation(
  entity callee, list real_args, list l_eff, transformer context)
{
  //entity caller = get_current_module_entity();
  int arg_num;
  list l_formal = NIL;
  list l_global = NIL;
  list l_res = NIL;
  list r_args = real_args;

  ifdebug(2)
  {
    pips_debug(2, "begin for function %s\n", entity_local_name(callee));
    pips_debug(2, "with actual arguments :\n");
    print_expressions(real_args);
    pips_debug(2, "and effects :\n");
    (*effects_prettyprint_func)(l_eff);
  }

  // functions that can be pointed by effects_translation_init_func:
  // simple_effects_translation_init
  // convex_regions_translation_init
  (*effects_translation_init_func)(callee, real_args, false);

  /* First, global effects : To be done
   * There is a problem here, since global entities maybe used as
   * actual arguments and at the same time as globals.
   */
  FOREACH(EFFECT, eff, l_eff)
  {
    storage eff_s = entity_storage(reference_variable(effect_any_reference((eff))));

    if(storage_ram_p(eff_s) &&
        !dynamic_area_p(ram_section(storage_ram(eff_s)))
        && !heap_area_p(ram_section(storage_ram(eff_s)))
        && !stack_area_p(ram_section(storage_ram(eff_s))))
    {
      /* This effect must be a global effect. It does not require
       * translation in C. However, it may not be in the scope of
       * the caller. */
      // functions that can be pointed by effect_dup_func:
      // simple_effect_dup
      // region_dup
      // copy_effect
      effect eff_tmp = (*effect_dup_func)(eff);
      // functions that can be pointed by effect_descriptor_interprocedural_translation_op:
      // simple_effect_descriptor_interprocedural_translation
      // convex_region_descriptor_translation
      (*effect_descriptor_interprocedural_translation_op)(eff_tmp);
      l_global = gen_nconc(l_global, CONS(EFFECT, eff_tmp, NIL));
    }

  }

  /* We should also take care of varargs */

  /* Then formal args */

  for (arg_num = 1; !ENDP(r_args); r_args = CDR(r_args), arg_num++)
  {
    expression real_exp = EXPRESSION(CAR(r_args));
    entity formal_ent = find_ith_formal_parameter(callee, arg_num);

    // functions that can be pointed by c_effects_on_actual_parameter_forward_translation_func:
    // c_simple_effects_on_actual_parameter_forward_translation
    // c_convex_effects_on_actual_parameter_forward_translation
    l_formal = gen_nconc
        (l_formal,
            (*c_effects_on_actual_parameter_forward_translation_func)
            (callee, real_exp, formal_ent, l_eff, context));
  } /* for */

  pips_debug_effects(2,"Formal effects : \n", l_formal);


  l_res = gen_nconc(l_global, l_formal);

  pips_debug_effects(2,"effects before, fields translation: \n",l_res);
  effects_translate_fields_compilation_unit(l_res,
      compilation_unit_of_module(entity_local_name(get_current_module_entity())),
      compilation_unit_of_module(entity_local_name(callee)));
  pips_debug_effects(2,"Ending with effects : \n",l_res);
  // functions that can be pointed by effects_translation_end_func:
  // simple_effects_translation_end
  // convex_regions_translation_end
  (*effects_translation_end_func)();
  return(l_res);
}




/************************************************************ INTERFACE */

list /* of effect */
generic_effects_backward_translation(
				     entity callee,
				     list /* of expression */ real_args,
				     list /* of effect */  l_sum_eff,
				     transformer context)
{
  list el = list_undefined;


  if(parameter_passing_by_reference_p(callee))
    el = generic_fortran_effects_backward_translation(callee, real_args,
						      l_sum_eff, context);
  else
    el = generic_c_effects_backward_translation(callee, real_args,
						l_sum_eff, context);


  return el;
}


list generic_effects_forward_translation(entity callee,
    list real_args,
    list l_eff,
    transformer context)
{
  list el = list_undefined;


  if(parameter_passing_by_reference_p(callee))
    // functions that can be pointed by fortran_effects_forward_translation_op:
    // simple_effects_forward_translation
    // convex_regions_forward_translation
    el = (*fortran_effects_forward_translation_op)(callee, real_args,
        l_eff, context);
  else
    el = generic_c_effects_forward_translation(callee, real_args,
        l_eff, context);

  return el;
}

static void effect_translate_fields(effect eff)
{
  pips_debug_effect(8, "input effect\n", eff);
  list l_indices = cell_indices(effect_cell(eff));

  if (!ENDP(l_indices))
  {

    type current_type = entity_basic_concrete_type(effect_entity(eff));



    while(!ENDP(l_indices))
    {
      switch(type_tag(current_type))
      {
      case is_type_void:
      case is_type_functional:
        // not expected because there are no more indices
        pips_internal_error("void or functional type not expected here, please report\n");
        break;
      case is_type_variable:
      {
        pips_debug(8, "variable case\n");
        basic current_basic = variable_basic(type_variable(current_type));
        list current_dims = variable_dimensions(type_variable(current_type));

        /* skip array dimensions */
        pips_debug(8, "poping %d dimensions\n",  (int) gen_length(current_dims) );
        for(int i=0; i< (int) gen_length(current_dims) && !ENDP(l_indices); i++, POP(l_indices));

        if (!ENDP(l_indices))
        {
          switch(basic_tag(current_basic))
          {
          case is_basic_pointer:
            pips_debug(8, "pointer case, poping one dimension\n");
            POP(l_indices);
            current_type = basic_pointer(current_basic);
            break;
          case is_basic_derived:
            pips_debug(8, "derived case\n");
            current_type = entity_basic_concrete_type(basic_derived(current_basic));
            break;
          case is_basic_typedef:
            pips_debug(8, "typedef case\n");
            current_type = entity_basic_concrete_type(basic_typedef(current_basic));
            break;
          default:
            pips_internal_error("this kind of basic should not appear here\n");
          }
        }

        break;
      }
      case is_type_struct:
      case is_type_union:
      case is_type_enum:
        pips_debug(8, "struct, union or enum case\n");
        expression exp = EXPRESSION(CAR(l_indices));
        pips_assert("current index must be a field entity",
            expression_reference_p(exp)
            && entity_field_p(reference_variable(expression_reference(exp))));
        reference exp_ref = expression_reference(exp);
        entity exp_ent = reference_variable(exp_ref);
        const char* exp_ent_name = entity_user_name(exp_ent);

        // search for matching field in current type
        list l_current_fields = type_fields(current_type);
        bool found = false;
        entity current_field = entity_undefined;
        while(!found && !ENDP(l_current_fields))
        {
          current_field = ENTITY(CAR(l_current_fields));
          pips_debug(8, "current field: %s \n", entity_name(current_field));

          if (same_entity_p(exp_ent, current_field))
          {
            pips_debug(8, "same field entities\n");
            found = true;
          }
          else if (same_string_p(entity_user_name(current_field), exp_ent_name))
          {
            pips_debug(8, "matching field \n");
            found = true;
          }
          POP(l_current_fields);
        }
        if (found)
        {
          reference_variable(exp_ref) = current_field;
          current_type = entity_basic_concrete_type(current_field);
          POP(l_indices);
        }
        else
          pips_internal_error("matching field not found\n");
        break;
      default:
        pips_internal_error("unexpected type: %s\n", type_to_string(current_type) );
        break;
      }
    }
  }
}

void effects_translate_fields_compilation_unit(list l_eff, string source_cu_name, string target_cu_name)
{

  pips_debug(8, "source name: %s, target name %s\n",
	     source_cu_name, target_cu_name);
  //  if(false)
  if (same_string_p(source_cu_name, target_cu_name))
    {
      pips_debug(8, "same compilation units \n");
    }
  else
    {
      FOREACH(EFFECT, eff, l_eff)
	{
	  effect_translate_fields(eff);
	}
    }
}
