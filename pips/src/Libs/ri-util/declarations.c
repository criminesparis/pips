/*

  $Id: declarations.c 23065 2016-03-02 09:05:50Z coelho $

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

/** #define LIST_SEPARATOR (is_fortran? ", " : ",") */

void check_fortran_declaration_dependencies(list ldecl)
{
  /* Check that each declaration only depends on previous declarations */
  int r = 1;

  FOREACH(ENTITY, v, ldecl) {
    type t = entity_type(v);

    if(type_variable_p(t)) {
      list dep = fortran_type_supporting_entities(NIL, t);
      list cdep = list_undefined;
      storage vs = entity_storage(v);

      /* FOREACH(ENTITY, dv, dep) { */
      for(cdep = dep; !ENDP(cdep); POP(cdep)) {
	entity dv = ENTITY(CAR(cdep));
	int dr = gen_position(dv, ldecl);
	value dvv = entity_initial(dv);

	if(storage_formal_p(vs) && value_symbolic_p(dvv)) {
	  /* Formal parameters are put in ldecl right away when
	     parsing the SUBROUTINE or FUNCTION statement. The
	     placement of their actual declaration is unknown. They
	     may depend on PARAMETERs declared later */
	  ;
	}
	else if(dr>=r) {
	  if(entity_symbolic_p(dv))
	    pips_user_warning("Fortran declaration order may be violated. "
			      "Variable \"%s\" depends on parameter \"%s\""
			      " but is, at least partly, declared first.\n",
			      entity_user_name(v), entity_user_name(dv));
	  else if(entity_scalar_p(dv))
	    pips_user_warning("Fortran declaration order may be violated. "
			      "Variable \"%s\" depends on variable \"%s\" "
			      "but is, at least partly, declared first.\n",
			      entity_user_name(v), entity_user_name(dv));
	  else
	    /* Should be a ParserError() when called from ProcessEntries()... */
	    pips_user_error("Fortran declaration order violated. Variable \"%s\" "
			    "depends on variable \"%s\" but is declared first.\n",
			    entity_user_name(v), entity_user_name(dv));
	}
      }
      gen_free_list(dep);
    }
    r++;
  }
}



/* The fprint_functional() and fprint_environment() functions are
   moved from syntax/declaration.c */

/* C Version of print_common_layout this is called by
   fprint_environment(). This function is much simpler than Fortran
   Version */

list get_common_members(entity common,
			entity __attribute__ ((unused)) module,
			bool __attribute__ ((unused)) only_primary)
{
  list result = NIL;
  //int cumulated_offset = 0;
  pips_assert("entity is a common", type_area_p(entity_type(common)));

  list ld = area_layout(type_area(entity_type(common)));
  entity v = entity_undefined;

  for(; !ENDP(ld); ld = CDR(ld))
    {
      v = ENTITY(CAR(ld));
      storage s = entity_storage(v);
      if(storage_ram_p(s))
	{
	  result = CONS(ENTITY, v, result);
	}
    }
  return gen_nreverse(result);
}

void print_C_common_layout(FILE * fd, entity c, bool debug_p)
{
  entity mod = get_current_module_entity();
  list members = get_common_members(c, mod, false);
  list equiv_members = NIL;

  (void) fprintf(fd, "\nLayout for memory area \"%s\" of size %td: \n",
		 entity_name(c), area_size(type_area(entity_type(c))));

  if(ENDP(members)) {
    pips_assert("An empty area has size 0", area_size(type_area(entity_type(c))) ==0);
    (void) fprintf(fd, "\t* empty area *\n\n");
  }
  else {
    if(area_size(type_area(entity_type(c))) == 0)
      {
	if(debug_p) {
	  user_warning("print_common_layout","Non-empty area %s should have a final size greater than 0\n",
		       entity_module_name(c));
	}
	else {
	  // The non-empty area can have size zero if the entity is extern
	  //pips_internal_error(//     "Non-empty area %s should have a size greater than 0",
	  //     entity_module_name(c));
	}
      }
    MAP(ENTITY, m,
    {
      pips_assert("RAM storage",
		  storage_ram_p(entity_storage(m)));
      int s;
      // There can be a Array whose size is not known (Dynamic Variables)
      SizeOfArray(m, &s);

      pips_assert("An area has no offset as -1",
		  (ram_offset(storage_ram(entity_storage(m)))!= -1));
      if(ram_offset(storage_ram(entity_storage(m))) == DYNAMIC_RAM_OFFSET) {
	(void) fprintf(fd,
		       "\tDynamic Variable %s, \toffset = UNKNOWN, \tsize = DYNAMIC\n",
		       entity_name(m));
      }
      else if(ram_offset(storage_ram(entity_storage(m))) == UNDEFINED_RAM_OFFSET) {

	(void) fprintf(fd,
		       "\tExternal Variable %s,\toffset = UNKNOWN,\tsize = %d\n",
		       entity_name(m),s);
      }
      else {
	(void) fprintf(fd,
		       "\tVariable %s,\toffset = %td,\tsize = %d\n",
		       entity_name(m),
		       ram_offset(storage_ram(entity_storage(m))),
		       s);
      }
      //}
    },
	members);
    (void) fprintf(fd, "\n");
    /* Look for variables aliased with a variable in this common */
    MAP(ENTITY, m,
    {
      list equiv = ram_shared(storage_ram(entity_storage(m)));

      equiv_members = arguments_union(equiv_members, equiv);
    },
	members);

    if(!ENDP(equiv_members)){

      equiv_members = arguments_difference(equiv_members, members);
      if(!ENDP(equiv_members)) {
	sort_list_of_entities(equiv_members);

	(void) fprintf(fd, "\tVariables aliased to this common:\n");

	MAP(ENTITY, m,
	{
    int asize;
	  pips_assert("RAM storage", storage_ram_p(entity_storage(m)));
    if (!SizeOfArray(m, &asize))
      asize = -1;
	  (void) fprintf(fd,
                   "\tVariable %s,\toffset = %td,\tsize = %d\n",
                   entity_name(m),
                   ram_offset(storage_ram(entity_storage(m))),
                   asize);
	},
	    equiv_members);
	(void) fprintf(fd, "\n");
	gen_free_list(equiv_members);
      }
    }
  }
  gen_free_list(members);
}

/* This function is called from c_parse() via ResetCurrentModule() and
   fprint_environment() */
void fprint_functional(FILE * fd, functional f)
{
  type tr = functional_result(f);
  int count = 0;

  FOREACH(PARAMETER, p, functional_parameters(f)) {
    type ta = parameter_type(p);

    pips_assert("Argument type is variable or varags:variable or functional or void",
		type_variable_p(ta)
		|| (type_varargs_p(ta) && type_variable_p(type_varargs(ta)))
		|| type_functional_p(ta)
		|| type_void_p(ta));

    if(count>0)
      (void) fprintf(fd, " x ");
    count++;

    if(type_functional_p(ta)) {
      functional fa = type_functional(ta);
      /* (void) fprintf(fd, " %s:", type_to_string(ta)); */
      (void) fprintf(fd, "(");
      fprint_functional(fd, fa);
      (void) fprintf(fd, ")");
    }
    else if(type_void_p(ta)) {
      (void) fprintf(fd, "(");
      (void) fprintf(fd, ")");
    }
    else {
      if(type_varargs_p(ta)) {
	(void) fprintf(fd, " %s:", type_to_string(ta));
	ta = type_varargs(ta);
      }
      (void) fprintf(fd, "%s", basic_to_string(variable_basic(type_variable(ta))));
    }
  }

  if(ENDP(functional_parameters(f))) {
    (void) fprintf(fd, " ()");
  }
  (void) fprintf(fd, " -> ");

  if(type_variable_p(tr))
    (void) fprintf(fd, " %s\n", basic_to_string(variable_basic(type_variable(tr))));
  else if(type_void_p(tr))
    (void) fprintf(fd, " %s\n", type_to_string(tr));
  else if(type_unknown_p(tr)){
    /* Well, seems to occur for C compilation units, instead of void... */
    (void) fprintf(fd, " %s\n", type_to_string(tr));
  }
  else if(type_varargs_p(tr)) {
    (void) fprintf(fd, " %s:%s", type_to_string(tr),
		   basic_to_string(variable_basic(type_variable(type_varargs(tr)))));
  }
  else
    /* An argument can be functional, but not (yet) a result. */
    pips_internal_error("Ill. type %d", type_tag(tr));
}

void fprint_environment(FILE *fd, entity m)
{
  fprint_any_environment(fd, m, true);
}

void fprint_C_environment(FILE *fd, entity m)
{
  fprint_any_environment(fd, m, false);
}

void fprint_any_environment(FILE * fd, entity m, bool is_fortran)
{
  list decls = gen_copy_seq(code_declarations(value_code(entity_initial(m))));
  int nth = 0; /* rank of formal parameter */
  entity rv = entity_undefined; /* return variable */

  pips_assert("fprint_environment", entity_module_p(m));

  /* To simplify validation, at the expense of some information about
     the parsing process. */
  gen_sort_list(decls,(gen_cmp_func_t)compare_entities);

  (void) fprintf(fd, "\nDeclarations for module %s with type ",
		 module_local_name(m));
  fprint_functional(fd, type_functional(entity_type(m)));
  (void) fprintf(fd, "\n\n");

  /* In C, no return entity is created (yet). See MakeCurrentModule(). */
  pips_assert("A module storage is ROM or return",
	      storage_rom_p(entity_storage(m))
	      || storage_return_p(entity_storage(m)));

  /* List of implicitly and explicitly declared variables,
     functions and areas */

  (void) fprintf(fd, "%s\n", ENDP(decls)?
		 "* empty declaration list *\n\n": "Variable list:\n\n");

  MAP(ENTITY, e, {
      type t = entity_type(e);

      fprintf(fd, "Declared entity %s\twith type %s ", entity_name(e), type_to_string(t));

      if(type_variable_p(t))
	fprintf(fd, "%s\n", basic_to_string(variable_basic(type_variable(t))));
      else if(type_functional_p(t)) {
	fprint_functional(fd, type_functional(t));
      }
      else if(type_area_p(t)) {
	(void) fprintf(fd, "with size %td\n", area_size(type_area(t)));
      }
      else
	(void) fprintf(fd, "\n");
    },
    decls);

  if(!is_fortran) {
    list edecls = gen_copy_seq(code_externs(value_code(entity_initial(m))));
    /* List of external variables and functions and areas */

    gen_sort_list(edecls, (gen_cmp_func_t)compare_entities);

    (void) fprintf(fd, "%s\n", ENDP(edecls)?
		   "* empty external declaration list *\n\n": "External variable list:\n\n");

    MAP(ENTITY, e, {
	type t = entity_type(e);

	fprintf(fd, "Declared entity %s\twith type %s ", entity_name(e), type_to_string(t));

	if(type_variable_p(t))
	  fprintf(fd, "%s\n", basic_to_string(variable_basic(type_variable(t))));
	else if(type_functional_p(t)) {
	  fprint_functional(fd, type_functional(t));
	}
	else if(type_area_p(t)) {
	  (void) fprintf(fd, "with size %td\n", area_size(type_area(t)));
	}
	else
	  (void) fprintf(fd, "\n");
      },
      edecls);
    gen_free_list(edecls);
  }

  /* Formal parameters */
  nth = 0;
  MAP(ENTITY, v, {
      storage vs = entity_storage(v);

      pips_assert("All storages are defined", !storage_undefined_p(vs));

      if(storage_formal_p(vs)) {
	nth++;
	if(nth==1) {
	  (void) fprintf(fd, "\nLayouts for formal parameters:\n\n");
	}
	(void) fprintf(fd,
		       "\tVariable %s,\toffset = %td\n",
		       entity_name(v), formal_offset(storage_formal(vs)));
      }
      else if(storage_return_p(vs)) {
	pips_assert("No more than one return variable", entity_undefined_p(rv));
	rv = v;
      }
    }, decls);

  /* Return variable */
  if(!entity_undefined_p(rv))
  {
    int asize;
    if (!SizeOfArray(rv, &asize))
      asize = -1;
    fprintf(fd,
            "\nLayout for return variable:\n\n"
            "\tVariable %s,\tsize = %d\n", entity_name(rv), asize);
  }

  /* Structure of each area/common */
  if(!ENDP(decls)) {
    (void) fprintf(fd, "\nLayouts for areas (commons):\n\n");
  }

  MAP(ENTITY, e, {
      if(type_area_p(entity_type(e))) {
	if(is_fortran)
	  print_common_layout(fd, e, false);
	else
	  print_C_common_layout(fd, e, false);
      }
    },
    decls);

  (void) fprintf(fd, "End of declarations for module %s\n\n",
		 module_local_name(m));

  gen_free_list(decls);
}


/* Transform a declaration with an initialization statement into 2 parts,
   a declaration statement and an initializer statement

   gen_recurse callback on exiting statements. For a declaration to be split:

   - it must be a local declaration

   - the initial value, if any, must be a valid rhs expression or an
     array initialization; struct initialization are not (yet) supported
 */
void split_initializations_in_statement(statement s)
{
  if(!get_bool_property("C89_CODE_GENERATION") && statement_block_p(s)) {
    /* generate C99 code */
    list cs = list_undefined;
    list pcs = NIL;
    list nsl = statement_block(s); // new statement list
    for( cs = statement_block(s); !ENDP(cs); ) {
      statement ls = STATEMENT(CAR(cs));
      if(declaration_statement_p(ls)) {
	list inits = NIL;
	list decls = statement_declarations(ls); // Non-recursive
	//statement sc = statement_undefined; // statement copy

	FOREACH(ENTITY, var, decls) {
	  /* The initialization of a static variable cannot be split */
	  if(entity_static_variable_p(var)) {
	    pips_user_warning("Initialization of variable \"%s\" cannot be "
			      "split from its declaration because \"%s\" "
			      "is a static variable.\n",
			      entity_user_name(var), entity_user_name(var));
	  }
	  else {
	    const char* mn  = entity_module_name(var);
	    const char* cmn = get_current_module_name();
	    if ( same_string_p(mn,cmn)
		 && !value_unknown_p(entity_initial(var))
		 ) {
	      expression ie = variable_initial_expression(var);
	      if (expression_is_C_rhs_p(ie)) {
		statement is = make_assign_statement(entity_to_expression(var), ie);
		inits = gen_nconc(inits, CONS(statement, is, NIL));
		entity_initial(var) = make_value_unknown();
	      }
	      else if(entity_array_p(var)) {
		inits = gen_nconc(inits, brace_expression_to_statements(var,ie));
		brace_expression_to_updated_type(var,ie);
		entity_initial(var) = make_value_unknown();
	      }
	      else if(struct_type_p(entity_basic_concrete_type(var))) {
		inits = gen_nconc(inits, brace_expression_to_statements(var,ie));
		entity_initial(var) = make_value_unknown();
	      }
	      else {
		pips_user_warning("split initializations not implemented yet for structures\n");
	      }
	      /* if this transformation led to an uninitialized const, remove the const qualifier */
	      if(value_unknown_p(entity_initial(var))) {
		list tmp = gen_copy_seq(entity_qualifiers(var));
		FOREACH(QUALIFIER,q,tmp) {
		  if(qualifier_const_p(q))
		    gen_remove_once(&variable_qualifiers(type_variable(entity_type(var))),q);
		}
		gen_free_list(tmp);
	      }
	    }
	  }
	}

	if(!ENDP(inits)) {
	  /* This is not very smart... You do not need pcs in C99
	     since you are going to add the assignment statements
	     just after the current declaration statement... */
	  inits = CONS(STATEMENT, ls, inits);
	  /* Chain the new list within the current statement list */
	  if(ENDP(pcs)) {
	    nsl = inits;
	  }
	  else {
	    CDR(pcs) = inits;
	  }
	  /* Move to the next original element nsl */
	  pcs = gen_last(inits);
	  CDR(pcs) = CDR(cs);
	  POP(cs);
	}
	else {
	  /* Move to the next statement */
	  pcs = cs;
	  POP(cs);
	}
      }
      else {
	/* Move to the next statement */
	pcs = cs;
	POP(cs);
      }
    }
    instruction_block(statement_instruction(s)) = nsl;
  }
  else if(statement_block_p(s)) {
    /* generate C89 code */
    list cs = list_undefined;
    //list pcs = NIL;
    //list nsl = statement_block(s); // new statement list
    list inits = NIL; // list of initialization statements

    for( cs = statement_block(s); !ENDP(cs); POP(cs)) {
      statement ls = STATEMENT(CAR(cs));
      if(declaration_statement_p(ls)) {
	list decls = statement_declarations(ls); // Non-recursive
	//statement sc = statement_undefined; // statement copy

	FOREACH(ENTITY, var, decls) {
        const char* mn  = entity_module_name(var);
        const char* cmn = get_current_module_name();
	  if ( strcmp(mn,cmn) == 0
	       && !value_unknown_p(entity_initial(var))
	       ) {
	    expression ie = variable_initial_expression(var);
            if(expression_undefined_p(ie)) {}
            else if (expression_is_C_rhs_p(ie)) {
	      statement is = make_assign_statement(entity_to_expression(var), ie);
	      inits = gen_nconc(inits, CONS(statement, is, NIL));
	      entity_initial(var) = make_value_unknown();
	    }
	    else if(entity_array_p(var)) {
	      inits=gen_nconc(inits,brace_expression_to_statements(var,ie));
	      entity_initial(var) = make_value_unknown();
	    }
        else {
          pips_user_warning("split initializations not implemented yet for structures\n");
        }
	  }
	}
      }

      if(!ENDP(inits)) {
	list ncs = CDR(cs);
	if(ENDP(ncs) || !declaration_statement_p(STATEMENT(CAR(ncs)))) {
	  list pcs = gen_last(inits);
	  CDR(cs) = inits;
	  CDR(pcs) = ncs;
	  break;
	}
      }
    }
    //instruction_block(statement_instruction(s)) = nsl;
  }
  else {
    /* Do nothing ? */
  }
}

void dump_functional(functional f, string_buffer result)
{
  type tr = functional_result(f);
  bool first = true;

  FOREACH(parameter, p , functional_parameters(f))
  {
    type ta = parameter_type(p);

    if (first)
      first = false;
    else
      string_buffer_append(result, " x ");

    pips_assert("Argument type is variable or varags:variable or functional or void",
                type_variable_p(ta)
                || (type_varargs_p(ta) && type_variable_p(type_varargs(ta)))
                || type_functional_p(ta)
                || type_void_p(ta));

    if (type_variable_p(ta)) {
      variable v = type_variable(ta);
      basic b = variable_basic(v);
      if (basic_pointer_p(b) && type_functional_p(basic_pointer(b))) {
        functional f = type_functional(basic_pointer(b));
        string_buffer_append(result, "(");
        dump_functional(f,result);
        string_buffer_append(result, ") *");
      }
      else {
        string_buffer_append(result, basic_to_string(b));
        int ndims = gen_length(variable_dimensions(v));
        for (int i = 0; i < ndims; i++)
          string_buffer_append(result, "[]");
      }
    }
    else if(type_functional_p(ta)) {
      functional fa = type_functional(ta);

      string_buffer_append(result, "(");
      dump_functional(fa, result);
      string_buffer_append(result, ")");
    }
    else if(type_varargs_p(ta)) {
      string_buffer_append(result, concatenate(type_to_string(ta),":",NULL));
      ta = type_varargs(ta);
      string_buffer_append(result,
                           basic_to_string(variable_basic(type_variable(ta))));
    }
    else if(type_void_p(ta)) {
      /* FI: we could do nothing or put "void". I choose to put "void"
         to give more information about the internal
         representation. */
      string_buffer_append(result, type_to_string(ta));
    }
  }

  if(ENDP(functional_parameters(f))) {
    string_buffer_append(result, concatenate("()",NULL));
  }

  string_buffer_append(result, concatenate(" -> ",NULL));

  if(type_variable_p(tr))
    string_buffer_append(result,
                         concatenate(basic_to_string(variable_basic(type_variable(tr)))
                                     /*,NL*/,NULL));
  else if(type_void_p(tr))
    string_buffer_append(result, concatenate(type_to_string(tr)/*,NL*/,NULL));
  else if(type_unknown_p(tr)){
    string_buffer_append(result, concatenate(type_to_string(tr)/*,NL*/,NULL));
  }
  else if(type_varargs_p(tr)) {
    string_buffer_append(result,
                         concatenate(type_to_string(tr),":",
                                     basic_to_string(variable_basic(type_variable(type_varargs(tr)))),NULL));
  }
  else
    /* An argument can be functional, but not (yet) a result. */
    pips_internal_error("Ill. type %d", type_tag(tr));
}
