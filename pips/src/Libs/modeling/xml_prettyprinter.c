/*

  $Id: xml_prettyprinter.c 23491 2018-10-23 06:20:51Z coelho $

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

#define DEBUG_XML 1

#include <stdio.h>
#include <ctype.h>

#include "genC.h"
#include "linear.h"

#include "pipsdbm.h"
#include "misc.h"

#include "properties.h"
#include "text.h"

#include "effects.h"
#include "ri.h"
#include "ri-util.h"
#include "text-util.h"
#include "control.h" // load_ctrl_graph
#include "effects-util.h"

#include "transformer.h"
#include "prettyprint.h" // for print_statement, words_expression...
#include "dg.h"
typedef dg_arc_label arc_label;
typedef dg_vertex_label vertex_label;
#include "graph.h"
#include "rice.h"
#include "ricedg.h"

#include "effects-convex.h"  // used
#include "effects-generic.h" // used
#include "effects-simple.h" // used
#include "complexity_ri.h"   // for next include
#include "complexity.h"      // used
#include "semantics.h"       // used
#include "modeling.h"

#define COMMA         ","
#define EMPTY         ""
#define NL            "\n"
#define TAB           "    "
#define SEMICOLON     ";" NL
#define SPACE         " "

#define OPENBRACKET   "["
#define CLOSEBRACKET  "]"

#define OPENPAREN     "("
#define CLOSEPAREN    ")"

#define OPENBRACE     "{"
#define CLOSEBRACE    "}"

#define OPENANGLE     "<"
#define CLOSEANGLE    ">"
#define SLASH	      "/"

#define SHARPDEF      "#define"
#define COMMENT	      "//" SPACE
#define QUOTE         "\""


#define XML_TASK_PREFIX "T_"
#define XML_MOTIF_PREFIX "M_"
#define XML_ARRAY_PREFIX "A_"

#define XML_RL      NL,TAB,TAB

#define code_is_a_box 0
#define code_is_a_te 1
#define code_is_a_main 2
#define USER_MAIN "main"

/* array containing extern loop indices names */
static gen_array_t extern_indices_array;
/* array containing intern loop indices (name : "M_") */
static gen_array_t intern_indices_array;
/* array containing extern upperbounds */
static gen_array_t extern_upperbounds_array;
/* array containing intern upperbounds */
static gen_array_t intern_upperbounds_array;
/* array containing the tasks names*/
static gen_array_t tasks_names;

static const char* global_module_name;
#define BL             " "
#define TB1            "\t"

// entity [var] -> Pcallst
static hash_table hash_entity_def_into_tasks = hash_table_undefined;

static const char* global_module_name;
static int global_margin =0;

static bool fortran_appli = true;
static bool box_in_statement_p = false;
static bool motif_in_statement_p = false;
static bool statement_in_truebranch_p = false;
static list cumulated_list = NIL;
static statement test_statement_of_reference;
static list local_declaration_list = NIL;
static call encapsulated_call = call_undefined;
#define MEM_PREFIX "-MEM:"
static string array_location_string;
static string array_mem_string;
static Pvecteur global_application_variables = VECTEUR_NUL;
static Pvecteur local_application_variables = VECTEUR_NUL;

/******************************************************** DEF TO TASK MAPPING */

// entity [var] -> entity [func]
// static hash_table hash_entity_def_to_task = hash_table_undefined;

// global
static entity_to_entity def_to_task_mapping = entity_to_entity_undefined;

static void def_to_task_init(void)
{
  pips_assert("def_to_task_mapping is undefined",
              entity_to_entity_undefined_p(def_to_task_mapping));
  def_to_task_mapping = make_entity_to_entity();
}

static void def_to_task_set(entity_to_entity mapping)
{
  pips_assert("def_to_task_mapping is undefined",
              entity_to_entity_undefined_p(def_to_task_mapping));
  def_to_task_mapping = mapping;
}

static void def_to_task_reset(void)
{
  pips_assert("def_to_task_mapping is defined",
              !entity_to_entity_undefined_p(def_to_task_mapping));
  def_to_task_mapping = entity_to_entity_undefined;
}

static void def_to_task_store(entity var, entity fun)
{
  if (bound_entity_to_entity_p(def_to_task_mapping, var))
    update_entity_to_entity(def_to_task_mapping, var, fun);
  else
    extend_entity_to_entity(def_to_task_mapping, var, fun);
}

static entity def_to_task_get(entity var)
{
  return bound_entity_to_entity_p(def_to_task_mapping, var)?
    apply_entity_to_entity(def_to_task_mapping, var): NULL;
}

/**************************************************************** MISC UTILS */

#define current_module_is_a_function()			\
  (entity_function_p(get_current_module_entity()))

static bool variable_p(entity e)
{
  storage s = entity_storage(e);
  return type_variable_p(entity_type(e)) &&
    (storage_ram_p(s) || storage_return_p(s));
}


#define RESULT_NAME	"result"
static string xml_entity_local_name(entity var)
{
  const char* name;

  if (current_module_is_a_function() &&
      var != get_current_module_entity() &&
      same_string_p(entity_local_name(var),
		    entity_local_name(get_current_module_entity())))
    name = RESULT_NAME;
  else
    {
      name = entity_local_name(var);

      /* Delete all the prefixes */

      if (strstr(name,STRUCT_PREFIX) != NULL)
	name = strstr(name,STRUCT_PREFIX) + 1;
      if (strstr(name,UNION_PREFIX) != NULL)
	name = strstr(name,UNION_PREFIX) + 1;
      if (strstr(name,ENUM_PREFIX) != NULL)
	name = strstr(name,ENUM_PREFIX) + 1;
      if (strstr(name,TYPEDEF_PREFIX) != NULL)
	name = strstr(name,TYPEDEF_PREFIX) + 1;
      if (strstr(name,MEMBER_SEP_STRING) != NULL)
	name = strstr(name,MEMBER_SEP_STRING) + 1;
    }

  /* switch to upper cases... */
  char *rname=strupper(strdup(name),name);
  return rname;
}


/************************************************************** DECLARATIONS */

/*
  integer a(n,m) -> int a[m][n];
  parameter (n=4) -> #define n 4
*/



/* forward declaration */
static string xml_expression(expression);

/* Attention with Fortran: the indices are reversed. */
static string xml_reference_with_explicit_motif(reference r)
{
  string result = strdup(EMPTY), old, svar;
  MAP(EXPRESSION, e,
      {
	string s = strdup(xml_expression(e));
	old = result;
	result = strdup(concatenate(old, OPENBRACKET, s, CLOSEBRACKET, NULL));
	free(old);
	free(s);
      }, reference_indices(r));

  old = result;
  svar = xml_entity_local_name(reference_variable(r));
  result = strdup(concatenate(svar, old, NULL));
  free(old);
  free(svar);
  return result;
}

static string xml_expression(expression e)
{
  string result = string_undefined;
  syntax s = expression_syntax(e);

  switch (syntax_tag(s))
    {
    case is_syntax_reference:
      result = xml_reference_with_explicit_motif(syntax_reference(s));
      break;
    case is_syntax_call: {
      value ev = EvalExpression(e);
      constant ec = value_constant(ev);
      int eiv = 0;

      if(!value_constant_p(ev)) {
	pips_user_error("Constant expected for XML loop bounds.\n");
      }
      if(!constant_int_p(ec)) {
	pips_user_error("Integer constant expected for XML loop bounds.\n");
      }
      eiv = constant_int(ec);
      result = strdup(i2a(eiv));
      break;
    }
    default:
      pips_internal_error("unexpected syntax tag");
    }
  return result;
}

static gen_array_t array_names;
static gen_array_t array_dims;

#define ITEM_NOT_IN_ARRAY -1

static int gen_array_index(gen_array_t ar, string item){
  int i;

  for(i = 0; i<(int) gen_array_nitems(ar); i++){
    if(gen_array_item(ar, i) != NULL){
      if(same_string_p(item, *((string *)(gen_array_item(ar, i))))){
	return i;
      }
    }
  }
  return ITEM_NOT_IN_ARRAY;
}

static string xml_dim_string(list ldim, string name)
{
  string result = "";
  int nbdim = 0;
  string origins = "origins = list<integer>(";
  string dimensions = "dimSizes = list<integer>(";
  string deuxpoints = " :: ";
  string data_array = "DATA_ARRAY(";
  string data_decl = "name = symbol!(";
  string dimstring = "dim = ";
  string datatype = "dataType = INTEGER)";
  string name4p = name;
  string * namep = malloc(sizeof(string));
  int * nbdimptr = malloc(sizeof(int));
  *namep = name4p;
  if (ldim)
    {
      result = strdup(concatenate(name, deuxpoints, data_array, data_decl, QUOTE, name, QUOTE, CLOSEPAREN, COMMA, NL, NULL));
      result = strdup(concatenate(result, TAB, dimstring, NULL));
      MAP(DIMENSION, dim, {
	  expression elow = dimension_lower(dim);
	  expression eup = dimension_upper(dim);

	  intptr_t low;
	  intptr_t up;
	  nbdim++;
	  if (expression_integer_value(elow, &low)){
	    if(nbdim != 1)
	      origins = strdup(concatenate(origins, COMMA ,int2a(low), NULL));
	    else
	      origins = strdup(concatenate(origins, int2a(low), NULL));
	  }
	  else pips_user_error("Array origins must be integer\n");

	  if (expression_integer_value(eup, &up)){
	    if(nbdim != 1)
	      dimensions = strdup(concatenate(dimensions, COMMA ,int2a(up-low+1), NULL));
	    else
	      dimensions = strdup(concatenate(dimensions, int2a(up-low+1), NULL));
	  }
	  else pips_user_error("Array dimensions must be integer\n");
	}, ldim);
      *nbdimptr = nbdim;
      gen_array_append(array_dims, nbdimptr);
      gen_array_append(array_names, namep);
      result = strdup(concatenate(result, int2a(nbdim), COMMA, NL, NULL));
      result = strdup(concatenate(result, TAB, origins, CLOSEPAREN, COMMA, NL, NULL));
      result = strdup(concatenate(result, TAB, dimensions, CLOSEPAREN, COMMA, NL, NULL));
      result = strdup(concatenate(result, TAB, datatype, NL, NL, NULL));
    }
  return result;
}

static string this_entity_xmldeclaration(entity var)
{
  string result = strdup("");
  string name = strdup(concatenate("A_", entity_local_name(var), NULL));
  type t = entity_type(var);
  pips_debug(2,"Entity name : %s\n",entity_name(var));
  /*  Many possible combinations */

  if (strstr(name,TYPEDEF_PREFIX) != NULL)
    pips_user_error("Structs not supported\n");

  switch (type_tag(t)) {
  case is_type_variable:
    {
      variable v = type_variable(t);
      string sd;
      sd = strdup(xml_dim_string(variable_dimensions(v), name));
      result = strdup(concatenate(result, sd, NULL));
      break;
    }
  case is_type_struct:
    {
      pips_user_error("Struct not allowed\n");
      break;
    }
  case is_type_union:
    {
      pips_user_error("Union not allowed\n");
      break;
    }
  case is_type_enum:
    {
      pips_user_error("Enum not allowed\n");
      break;
    }
  default:
    pips_user_error("Something not allowed here\n");
  }

  return result;
}

static string
xml_declarations_with_explicit_motif(entity module,
				     bool (*consider_this_entity)(entity),
				     string separator,
				     bool lastsep)
{
  string result = strdup("");
  code c;
  bool first = true;

  pips_assert("it is a code", value_code_p(entity_initial(module)));

  c = value_code(entity_initial(module));
  MAP(ENTITY, var,
      {
	debug(2, "\n Prettyprinter declaration for variable :",xml_entity_local_name(var));
	if (consider_this_entity(var))
	  {
	    string old = strdup(result);
	    string svar = strdup(this_entity_xmldeclaration(var));
	    result = strdup(concatenate(old, !first && !lastsep? separator: "",
					svar, lastsep? separator: "", NULL));
	    free(old);
	    free(svar);
	    first = false;
	  }
      },code_declarations(c));
  return result;
}

static string xml_array_in_task(reference r, bool first, int task_number);

static string xml_call_from_assignation(call c, int task_number, bool * input_provided){
  /* All arguments of this call are in Rmode (inputs of the task) */
  /* This function is called recursively */
  list arguments = call_arguments(c);
  syntax syn;
  string result = "";

  MAP(EXPRESSION, expr, {
      syn = expression_syntax(expr);
      switch(syntax_tag(syn)){
      case is_syntax_call:{
	result = strdup(concatenate(result, xml_call_from_assignation(syntax_call(syn), task_number, input_provided), NULL));
	break;
      }
      case is_syntax_reference:{
	reference ref = syntax_reference(syn);
    string svar = xml_entity_local_name(reference_variable(ref));
	string varname = strdup(concatenate("A_", svar, NULL));
    free(svar);
	if(gen_array_index(array_names, varname) != ITEM_NOT_IN_ARRAY){
	  result = strdup(concatenate(result, xml_array_in_task(ref, false, task_number), NULL));
	  *input_provided = true;
	}
	break;
      }
      default:{
	pips_user_error("only call and references allowed here\n");
      }
      }
    }, arguments);
  return result;
}

static void xml_call_from_indice(call c, string * offset_array, string paving_array[], string fitting_array[]){
  entity called = call_function(c);
  string funname = xml_entity_local_name(called);
  list arguments = call_arguments(c);
  syntax args[2];
  int i = 0;
  int iterator_nr;
  if(gen_length(arguments)==2){
    if(same_string_p(funname, "+") || same_string_p(funname, "-") || same_string_p(funname, "*")){
      MAP(EXPRESSION, arg, {
	  args[i] = expression_syntax(arg);
	  i++;
	}, arguments);
      if(same_string_p(funname, "+")){
	if(syntax_tag(args[0]) == is_syntax_call){
	  xml_call_from_indice(syntax_call(args[0]), offset_array, paving_array, fitting_array);
	}
	if(syntax_tag(args[1]) == is_syntax_call){
	  xml_call_from_indice(syntax_call(args[1]), offset_array, paving_array, fitting_array);
	}
	if(syntax_tag(args[0]) == is_syntax_reference){
	  reference ref = syntax_reference(args[0]);
	  if((iterator_nr = gen_array_index(extern_indices_array, xml_entity_local_name(reference_variable(ref)))) != ITEM_NOT_IN_ARRAY){
	    paving_array[iterator_nr] = strdup("1");
	  }
	  else if((iterator_nr = gen_array_index(intern_indices_array, xml_entity_local_name(reference_variable(ref)))) != ITEM_NOT_IN_ARRAY){
	    fitting_array[iterator_nr] = strdup("1");
	  }
	}
	if(syntax_tag(args[1]) == is_syntax_reference){
	  reference ref = syntax_reference(args[1]);
	  if((iterator_nr = gen_array_index(extern_indices_array, xml_entity_local_name(reference_variable(ref)))) != ITEM_NOT_IN_ARRAY){
	    paving_array[iterator_nr] = strdup("1");
	  }
	  else if((iterator_nr = gen_array_index(intern_indices_array, xml_entity_local_name(reference_variable(ref)))) != ITEM_NOT_IN_ARRAY){
	    fitting_array[iterator_nr] = strdup("1");
	  }
	}
      }
      else if(same_string_p(funname, "-")){
	if(syntax_tag(args[1]) == is_syntax_call && gen_length(call_arguments(syntax_call(args[1])))==0){
	  if(syntax_tag(args[0]) == is_syntax_reference){
	    reference ref = syntax_reference(args[0]);
	    if((iterator_nr = gen_array_index(extern_indices_array, xml_entity_local_name(reference_variable(ref)))) != ITEM_NOT_IN_ARRAY){
	      paving_array[iterator_nr] = strdup("1");
	    }
	    else if((iterator_nr = gen_array_index(intern_indices_array, xml_entity_local_name(reference_variable(ref)))) != ITEM_NOT_IN_ARRAY){
	      fitting_array[iterator_nr] = strdup("1");
	    }
	  }
	  if(syntax_tag(args[0]) == is_syntax_call){
	    xml_call_from_indice(syntax_call(args[0]), offset_array, paving_array, fitting_array);
	  }
	  xml_call_from_indice(syntax_call(args[1]), offset_array, paving_array, fitting_array);
	}
	else {
	  pips_user_error("APOTRES doesn't allow negative coefficients in paving and fitting matrices\n");
	}
      }
      else if(same_string_p(funname, "*")){
	if(syntax_tag(args[0]) != is_syntax_call || syntax_tag(args[1]) != is_syntax_reference || gen_length(call_arguments(syntax_call(args[0])))!=0 ){
	  pips_user_error("Only scalar * reference are allowed here. Please develop expressions.\n");
	}
	else {
	  int intern_nr = gen_array_index(intern_indices_array, xml_entity_local_name(reference_variable(syntax_reference(args[1]))));
	  int extern_nr = gen_array_index(extern_indices_array, xml_entity_local_name(reference_variable(syntax_reference(args[1]))));
	  string mult =  strdup(xml_entity_local_name(call_function(syntax_call(args[0]))));
	  if(extern_nr != ITEM_NOT_IN_ARRAY){
	    paving_array[extern_nr] = mult;
	  }
	  else if(intern_nr != ITEM_NOT_IN_ARRAY){
	    fitting_array[intern_nr] = strdup(mult);
	  }
	}
      }
    }
    else{
      pips_user_error("only linear expression of indices allowed\n");
    }
  }
  else if(gen_length(arguments) == 0){
    *offset_array = funname;
  }
  else{
    pips_user_error("only +, -, * and constants allowed\n");
  }
}

#define XML_ARRAY_PREFIX "A_"

static string xml_array_in_task(reference r, bool first, int task_number){
  /* XML name of the referenced array */
  string varname = strdup(concatenate(XML_ARRAY_PREFIX,
				      xml_entity_local_name(reference_variable(r)),
				      NULL));
  /* iterator for dimensions of array */
  int indice_nr = 0;
  list indices = reference_indices(r);
  string result = "";
  /* number of external loops*/
  int extern_nb = gen_array_nitems(extern_indices_array);

  /* number of dimensions of referenced array */
  int index_of_array = gen_length(indices); /*((int *) (gen_array_item(array_dims, gen_array_index(array_names, varname))));*/

  /* number of internal loops*/
  int intern_nb = gen_array_nitems(intern_indices_array);

  /* list of offsets for XML code */
  string offset_array[index_of_array];
  /* paving matrix for XML code
     1st coeff: array dimension (row index)
     2nd coeff: iteration dimension (column index) */
  string paving_array[index_of_array][extern_nb];

  /* fitting matrix for XML code
     1st coeff: array dimension
     2nd coeff: iteration dimension*/
  string fitting_array[index_of_array][intern_nb];
  int i;
  int j;
  int depth = 0;

  bool null_fitting_p = true;
  string internal_index_declarations = strdup("");
  string fitting_declaration = strdup("");
  string fitting_declaration2 = strdup("");

  /* initialization of the arrays */
  for (i=0; i<index_of_array; i++)
    offset_array[i] = "0";

  for (i=0; i<index_of_array ; i++)
    for (j=0; j<extern_nb; j++)
      paving_array[i][j] = "0";

  for (i=0; i<index_of_array ; i++)
    for (j=0; j<intern_nb; j++)
      fitting_array[i][j] = "0";

  /* XML reference header */
  result = strdup(concatenate(result, "DATA(name = symbol!(\"", "T_", int2a(task_number),
			      "\" /+ \"", varname, "\"),", NL, TAB, TAB, NULL));

  result = strdup(concatenate(result, "darray = ", varname, "," NL, TAB, TAB, "accessMode = ", (first?"Wmode,":"Rmode,"),
			      NL, TAB, TAB, "offset = list<VARTYPE>(", NULL));

  /* Fill in paving, fitting and offset matrices from index expressions. */
  MAP(EXPRESSION, ind, {
      syntax sind = expression_syntax(ind);
      int iterator_nr;
      switch(syntax_tag(sind)){
      case is_syntax_reference:{
	reference ref = syntax_reference(sind);
	if((iterator_nr = gen_array_index(extern_indices_array, xml_entity_local_name(reference_variable(ref)))) != ITEM_NOT_IN_ARRAY){
	  paving_array[indice_nr][iterator_nr] = strdup("1");
	}
	else if((iterator_nr = gen_array_index(intern_indices_array, xml_entity_local_name(reference_variable(ref)))) != ITEM_NOT_IN_ARRAY){
	  fitting_array[indice_nr][iterator_nr] = strdup("1");
	}

	break;
      }
      case is_syntax_call:{
	call c = syntax_call(sind);
	xml_call_from_indice(c, &(offset_array[indice_nr]), paving_array[indice_nr], fitting_array[indice_nr]);
	break;
      }
      default:{
	pips_user_error("Only call and reference allowed in indices.\n");
	break;
      }
      }
      indice_nr++;
    }, indices);


  /* generate offset list in XML code */
  for(i=0; i<index_of_array - 1; i++){
    result=strdup(concatenate(result, "vartype!(", offset_array[i],"), ", NULL));
  }
  result = strdup(concatenate(result, "vartype!(", offset_array[i], "))," NL, NULL));

  /* fitting header */
  result = strdup(concatenate(result, TAB, TAB, "fitting = list<list[VARTYPE]>(", NULL));

  /* XML column-major storage of fitting matrix */
  for(i=0;i<intern_nb; i++){
    bool is_null_p = true;
    for(j = 0; j<index_of_array; j++){
      is_null_p = is_null_p && (same_string_p(fitting_array[j][i], "0"));
    }
    if(!is_null_p){
      null_fitting_p = false;
      fitting_declaration = strdup(concatenate(fitting_declaration, "list(", NULL));
      for(j = 0; j<index_of_array-1; j++){
	fitting_declaration = strdup(concatenate(fitting_declaration, "vartype!(", fitting_array[j][i], "), ", NULL));
      }
      fitting_declaration = strdup(concatenate(fitting_declaration,
					       "vartype!(",
					       fitting_array[j][i],
					       ")), ",
					       NULL));
    }
  }

  if(!null_fitting_p){
    fitting_declaration2 =
      strdup(concatenate(gen_strndup0(fitting_declaration,
				      strlen(fitting_declaration) - 2),
			 "),", NL, TAB, TAB, TAB, NULL));
    result = strdup(concatenate(result, fitting_declaration2, NULL));
  }

  if(null_fitting_p){
    result = strdup(concatenate(result, "list()),", NL, TAB, TAB, NULL));
  }

  null_fitting_p = true;
  /* Generation of paving XML code*/
  result = strdup(concatenate(result, TAB, TAB, "paving = list<list[VARTYPE]>(", NULL));

  for(i=0;i<extern_nb-1; i++){
    result = strdup(concatenate(result, "list(", NULL));
    for(j = 0; j<index_of_array-1; j++){
      result = strdup(concatenate(result, "vartype!(", paving_array[j][i], "), ", NULL));
    }
    result = strdup(concatenate(result, "vartype!(", paving_array[j][i], ")),", NL, TAB, TAB, TAB, NULL));
  }
  result = strdup(concatenate(result, "list(", NULL));
  for(j = 0; j<index_of_array-1; j++){
    result = strdup(concatenate(result, "vartype!(", paving_array[j][i], "), ", NULL));
  }
  result = strdup(concatenate(result, "vartype!(", paving_array[j][i], "))),", NL, TAB, TAB, NULL));

#define MONMAX(a, b) ((a<b)?b:a)

  /* Definition of the inner loop nest */
  /* FI->IH: if some columns are removed, the effective depth is unkown and must be computed here */
  /* result = strdup(concatenate(result, "inLoopNest = LOOPNEST(deep = ", int2a(MONMAX(gen_array_nitems(intern_indices_array), 1)), ",", NL, TAB, TAB, TAB, NULL)); */

  for (j = 0; j<intern_nb; j++){
    bool is_null_p = true;
    for(i = 0; i < index_of_array; i++){
      is_null_p = is_null_p && (same_string_p(fitting_array[i][j], "0"));
    }
    if(!is_null_p){
      depth++;
    }
  }
  if(depth==0) depth = 1; /* see comment just below about null fitting matrices. */
  result = strdup(concatenate(result, "inLoopNest = LOOPNEST(deep = ", i2a(depth), ",", NL, TAB, TAB, TAB, NULL));
  result = strdup(concatenate(result, "upperBound = list<VARTYPE>(", NULL));

  /* 3 cases :
     - the fitting matrix is null : must generate a (0,0) loop with dummy index
     - some fitting matrix column is null : do not generate anything
     - some fitting matrix column is not null : generate the corresponding loop bound and index name
  */

  for (j = 0; j<intern_nb; j++){
    bool is_null_p = true;
    for(i = 0; i < index_of_array; i++){
      is_null_p = is_null_p && (same_string_p(fitting_array[i][j], "0"));
    }
    if(!is_null_p){
      null_fitting_p = false;
      result = strdup(concatenate(result,
				  "vartype!(",
				  *((string *)(gen_array_item(intern_upperbounds_array, j))),
				  "), ",
				  NULL));
      internal_index_declarations =
	strdup(concatenate(internal_index_declarations,
			   QUOTE,
			   *((string *)(gen_array_item(intern_indices_array, j))),
			   QUOTE,
			   ", ",
			   NULL));
    }
  }
  if(!null_fitting_p)
    {
      result = strdup(concatenate(gen_strndup0(result, strlen(result) - 2),
				  "),", NULL));
      internal_index_declarations =
	strdup(concatenate(gen_strndup0(internal_index_declarations,
					strlen(internal_index_declarations) -2),
			   ")", NULL));
    }



  if(null_fitting_p){
    result = strdup(concatenate(result, "vartype!(1)),", NL, TAB, TAB, TAB, "names = list<string>(\"M_I\")", NULL));
  }
  else{
    result = strdup(concatenate(result, NL, TAB, "names = list<string>(", internal_index_declarations, NULL));
  }

  /* Complete XML reference */
  result = strdup(concatenate(result, "))", (first?")":","), NL, NULL));
  return result;
}

static string xml_call_from_loopnest(call c, int task_number){
  entity called = call_function(c);
  list arguments = call_arguments(c);
  syntax s;
  string result = "";
  string first_result = "";
  bool first = true;
  bool input_provided = false, output_provided = false;
  string name = strdup(xml_entity_local_name(called));

  if(!same_string_p(name, "="))
    pips_user_error("Only assignation allowed here.\n");

  FOREACH(EXPRESSION, e, arguments){
    s = expression_syntax(e);
    switch(syntax_tag(s)){
    case is_syntax_call:{
      if(first)
	pips_user_error("Call not allowed in left-hand side argument of assignation.\n");
      else
	result = strdup(concatenate(result, xml_call_from_assignation(syntax_call(s), task_number, &input_provided), NULL));
      break;
    }
    case is_syntax_reference:
    {
      reference r = syntax_reference(s);
      string varname = strdup(concatenate("A_",
        xml_entity_local_name(reference_variable(r)), NULL));
      if (gen_array_index(array_names, varname) != ITEM_NOT_IN_ARRAY)
      {
        if(first){
          first_result = xml_array_in_task(r, first, task_number);
          output_provided = true;
        }
        else{
          result = strdup(concatenate(result,
             xml_array_in_task(r, first, task_number), NULL));
          input_provided = true;
        }
      }
      break;
    }
    default:
      pips_internal_error("unhandled case");
    }
    first = false;
  }

  if(!input_provided){
    result = strdup(concatenate("data = list<DATA>(dummyDATA, ", result, first_result, NULL));
  }
  else{
    result = strdup(concatenate("data = list<DATA>(", result, first_result, NULL));
  }
  if(!output_provided){
    result = strdup(concatenate(result, " dummyDATA)", NULL));
  }
  result = strdup(concatenate(result, TAB, ")", NL, NULL));
  return result;
}


static call sequence_call(sequence seq)
{
  call mc = call_undefined; /* meaningful call */
  int nc = 0; /* number of calls */

  MAP(STATEMENT, s, {
      if(continue_statement_p(s))
	;
      else if(statement_call_p(s)) {
	mc = instruction_call(statement_instruction(s));
	nc++;
      }
      else {
	nc = 0;
	break;
      }
    }, sequence_statements(seq));

  if(nc!=1)
    mc = call_undefined;

  return mc;
}

static loop sequence_loop(sequence seq)
{
  loop ml = loop_undefined; /* meaningful loop */
  int nl = 0; /* number of loops */

  MAP(STATEMENT, s, {
      if(continue_statement_p(s))
	;
      else if(statement_loop_p(s)) {
	ml = instruction_loop(statement_instruction(s));
	nl++;
      }
      else {
	nl = 0;
	break;
      }
    }, sequence_statements(seq));

  if(nl!=1)
    ml = loop_undefined;

  return ml;
}

static call xml_loop_from_loop(loop l, string * result, int task_number){

  string * up = malloc(sizeof(string));
  string * xml_name = malloc(sizeof(string));
  statement s = loop_body(l);
  instruction i = statement_instruction(s);
  int u, low;
  expression incr_e = range_increment(loop_range(l));
  syntax incr_s = expression_syntax(incr_e);

  if(!syntax_call_p(incr_s) ||
     strcmp( entity_local_name(call_function(syntax_call(incr_s))), "1") != 0 ) {
    pips_user_error("Loop increments must be constant \"1\".\n");
  }

  u = atoi(xml_expression(range_upper(loop_range(l))));
  low = atoi(xml_expression(range_lower(loop_range(l))));
  /*  printf("%i %i\n", u, low); */
  *up = strdup(int2a(u - low+1));
  //*up = xml_expression(range_upper(loop_range(l)) - range_lower(loop_range(l)) + 1);
  *xml_name = xml_entity_local_name(loop_index(l));
  if( (*xml_name)[0] == 'M'){
    gen_array_append(intern_indices_array, xml_name);
    gen_array_append(intern_upperbounds_array, up);
  }
  else{
    gen_array_append(extern_indices_array, xml_name);
    gen_array_append(extern_upperbounds_array, up);
  }

  switch(instruction_tag(i)){
  case is_instruction_loop:{
    loop l = instruction_loop(i);
    return xml_loop_from_loop(l, result, task_number);
    break;
  }
  case is_instruction_call: {
    call c = instruction_call(i);
    return c;
  }
  case is_instruction_sequence:
  {
    call c = sequence_call(instruction_sequence(i));
    loop l = sequence_loop(instruction_sequence(i));
    if (!call_undefined_p(c))
      return c;
    if (!loop_undefined_p(l))
      return xml_loop_from_loop(l, result, task_number);
    pips_user_error("A sequence should only contain a call or a loop");
  }
  default:
    pips_user_error("Only loops and calls allowed in a loop.");
  }
  return call_undefined;
}


/* We enter a loop nest. The first loop must be an extern loop. */
static string xml_loop_from_sequence(loop l, int task_number){
  statement s = loop_body(l);
  call c= call_undefined;
  int i;
  string * taskname = (string *)(malloc(sizeof(string)));
  expression incr_e = range_increment(loop_range(l));
  syntax incr_s = expression_syntax(incr_e);


  /* Initialize result string with the declaration of the task */
  string result;

  instruction ins = statement_instruction(s);
  string * name = malloc(sizeof(string));
  string * up = malloc(sizeof(string));
  int u, low;
  if(!syntax_call_p(incr_s) ||
     strcmp( entity_local_name(call_function(syntax_call(incr_s))), "1") != 0 ) {
    pips_user_error("Loop increments must be constant \"1\".\n");
  }


  *taskname = strdup(concatenate("T_", int2a(task_number), NULL));
  result = strdup(concatenate(*taskname,
			      " :: TASK(unitSpentTime = vartype!(1),"
			      NL, TAB, "exLoopNest = LOOPNEST(deep = ", NULL));
  gen_array_append(tasks_names, taskname);
  /* (re-)initialize task-scoped arrays*/
  extern_indices_array = gen_array_make(0);
  intern_indices_array = gen_array_make(0);
  extern_upperbounds_array = gen_array_make(0);
  intern_upperbounds_array = gen_array_make(0);

  *name = xml_entity_local_name(loop_index(l));
  u = atoi(xml_expression(range_upper(loop_range(l))));
  low = atoi(xml_expression(range_lower(loop_range(l))));
  *up = strdup(int2a(u - low+1));
  //*up = xml_expression(range_upper(loop_range(l)) - range_lower(loop_range(l)) + 1);

  if((*name)[0] == 'M'){
    pips_user_error("At least one extern loop is needed.\n");
  }
  else{
    gen_array_append(extern_indices_array, name);
    gen_array_append(extern_upperbounds_array, up);
  }


  switch(instruction_tag(ins)){
  case is_instruction_loop:{
    loop l = instruction_loop(ins);
    c = xml_loop_from_loop(l, &result, task_number);
    break;
  }
  case is_instruction_call:
    {
      c = instruction_call(ins);
    }
    break;
  case is_instruction_sequence:
    /* The sequence should contain only one meaningful call */
    if(!call_undefined_p(c=sequence_call(instruction_sequence(ins))))
      break;
    if(!loop_undefined_p(l=sequence_loop(instruction_sequence(ins)))) {
      c = xml_loop_from_loop(l, &result, task_number);
      break;
    }
    pips_user_error("Sequence should contain one loop or one call");
    break;
  default:
    pips_user_error("Only loops and one significant call allowed in a loop.");
  }

  /* External loop nest depth */
  result = strdup(concatenate(result, int2a(gen_array_nitems(extern_upperbounds_array)), ",", NL, TAB, TAB, NULL));

  /* add external upperbounds */
  result = strdup(concatenate(result, "upperBound = list<VARTYPE>(", NULL));

  for(i=0; i< ((int) gen_array_nitems(extern_upperbounds_array)) - 1; i++){
    result = strdup(concatenate(result, "vartype!(", *((string *)(gen_array_item(extern_upperbounds_array, i))), "), ", NULL));
  }
  result = strdup(concatenate(result, "vartype!(",*((string *)(gen_array_item(extern_upperbounds_array, i))), ")),",NL, TAB, TAB, NULL));

  /* add external indices names*/
  result = strdup(concatenate(result, "names = list<string>(", NULL));
  for(i=0; i<((int) gen_array_nitems(extern_indices_array)) - 1; i++){
    result = strdup(concatenate(result, QUOTE, *((string *)(gen_array_item(extern_indices_array, i))), QUOTE ", ", NULL));
  }
  result = strdup(concatenate(result, QUOTE, *((string *)(gen_array_item(extern_indices_array, i))), QUOTE, ")),", NL, TAB, NULL));

  result = strdup(concatenate(result, xml_call_from_loopnest(c, task_number), NULL));

  gen_array_free(extern_indices_array);
  gen_array_free(intern_indices_array);
  gen_array_free(extern_upperbounds_array);
  gen_array_free(intern_upperbounds_array);
  result = strdup(concatenate(result, NL, NULL));
  return result;
}

/* We are here at the highest level of statements. The statements are either
   loopnests or a RETURN instruction. Any other possibility pips_user_errors
   the prettyprinter.*/
static string xml_statement_from_sequence(statement s, int task_number){
  string result = "";
  instruction i = statement_instruction(s);

  switch(instruction_tag(i)){
  case is_instruction_loop:{
    loop l = instruction_loop(i);
    result = xml_loop_from_sequence(l, task_number);
    break;
  }
  case is_instruction_call:{
    /* RETURN should only be allowed as the last statement in the sequence */
    if(!return_statement_p(s) && !continue_statement_p(s))
      pips_user_error("Only RETURN and CONTINUE allowed here.\n");
    break;
  }
  default:{
    pips_user_error("Only loops and calls allowed here.\n");
  }
  }

  return result;
}

/* Concatentates each task to the final result.
   The validity of the task is not checked in this function but
   it is into xml_statementement_from_sequence and subsequent
   functions.*/
static string xml_sequence_from_task(sequence seq){
  string result = "";
  int task_number = 0;
  MAP(STATEMENT, s,
      {
	string oldresult = strdup(result);
	string current = strdup(xml_statement_from_sequence(s, task_number));

	if(strlen(current)==0) {
	  free(current);
	  result = oldresult;
	}
	else {
	  result = strdup(concatenate(oldresult, current, NULL));
	  free(current);
	  free(oldresult);
	  task_number++;
	}
      }, sequence_statements(seq));
  return result;
}

/* Manages tasks. The code is very defensive and hangs if sth not
   predicted happens. Here basically we begin the code in itself
   and thus $stat is obligatory a sequence. */
static string xml_tasks_with_motif(statement stat){
  int j;
  instruction i;
  string result = "tasks\n";
  if(statement_undefined_p(stat))
    {
      pips_internal_error("statement error");
    }
  i = statement_instruction(stat);
  tasks_names = gen_array_make(0);
  switch(instruction_tag(i)){
  case is_instruction_sequence:{
    sequence seq = instruction_sequence(i);
    result = xml_sequence_from_task(seq);
    break;
  }
  default:{
    pips_user_error("Only a sequence can be here");
  }
  }
  result = strdup(concatenate(result, NL, NL, "PRES:APPLICATION := APPLICATION(name = symbol!(", QUOTE, global_module_name, QUOTE, "), ", NL, TAB,NULL));
  result = strdup(concatenate(result, "tasks = list<TASK>(", NULL));
  for(j = 0; j<(int) gen_array_nitems(tasks_names) - 1; j++){
    result = strdup(concatenate(result, *((string *)(gen_array_item(tasks_names, j))), ", ", NULL));
  }
  result = strdup(concatenate(result, *((string *)(gen_array_item(tasks_names, j))), "))", NULL));

  return result;
}

/* Creates string for xml pretty printer.
   This string divides in declarations (array decl.) and
   tasks which are loopnest with an instruction at the core.
*/
static string xml_code_string(entity module, statement stat)
{
  string decls="", tasks="", result="";

  ifdebug(2)
    {
      printf("Module statement: \n");
      print_statement(stat);
      printf("and declarations: \n");
      print_entities(statement_declarations(stat));
    }

  decls       = xml_declarations_with_explicit_motif(module, variable_p, "", true);
  tasks       = xml_tasks_with_motif(stat);
  result = strdup(concatenate(decls, NL, tasks, NL, NULL));
  ifdebug(2)
    {
      printf("%s", result);
    }
  return result;
}


/******************************************************** PIPSMAKE INTERFACE */

/* Initiates xml pretty print modules
 */
bool print_xml_code_with_explicit_motif(const char* module_name)
{
  FILE * out;
  string ppt, xml, dir, filename;
  entity module;
  statement stat;
  array_names = gen_array_make(0);
  array_dims = gen_array_make(0);
  xml = db_build_file_resource_name(DBR_XML_PRINTED_FILE, module_name, ".xml");

  global_module_name = module_name;
  module = module_name_to_entity(module_name);
  dir = db_get_current_workspace_directory();
  filename = strdup(concatenate(dir, "/", xml, NULL));
  stat = (statement) db_get_memory_resource(DBR_CODE, module_name, true);

  if(statement_undefined_p(stat))
    {
      pips_internal_error("No statement for module %s", module_name);
    }
  set_current_module_entity(module);
  set_current_module_statement(stat);

  debug_on("XMLPRETTYPRINTER_DEBUG_LEVEL");
  pips_debug(1, "Begin Claire prettyprinter for %s\n", entity_name(module));
  ppt = xml_code_string(module, stat);
  pips_debug(1, "end\n");
  debug_off();

  /* save to file */
  out = safe_fopen(filename, "w");
  fprintf(out, "%s", ppt);
  safe_fclose(out, filename);

  free(ppt);
  free(dir);
  free(filename);

  DB_PUT_FILE_RESOURCE(DBR_XML_PRINTED_FILE, module_name, xml);

  reset_current_module_statement();
  reset_current_module_entity();

  return true;
}


/* ======================================================= */


// If false prettyprint the full name of entities - used in Arguments, Parameters
// If true prettyprint the first level of the entity name  (no struct field,...)
static bool print_full_name_p()
{
  return false;
}

// If false prettyprint the full name of entities - used in the Chain_graph
// If true prettyprint the first level of the entity name  (no struct field,...)
static bool print_name_1_level_p()
{
  return true;
}

static void
xml_declarations(entity module, string_buffer result)
{
  list dim;
  list ldecl = code_declarations(value_code(entity_initial(module)));
  list ld;

  entity var = entity_undefined;
  for(ld = ldecl; !ENDP(ld); ld = CDR(ld)){

    //printf("inside for");
    var = ENTITY(CAR(ld));
    //printf("Entity Name in the List : %s  ",entity_name(var));

    if (variable_p(var) && ( variable_entity_dimension(var) > 0))
      {
	// int nb_dim = variable_entity_dimension(var);
	//printf("inside p, %d",nb_dim);

	string_buffer_append(result,
			     concatenate(TAB, OPENANGLE, "array name =", QUOTE, XML_ARRAY_PREFIX,entity_user_name(var),QUOTE,
					 " dataType = ", QUOTE,
					 "INTEGER", QUOTE,CLOSEANGLE
					 , XML_RL, NULL));
	string_buffer_append(result,
			     concatenate(OPENANGLE,"dimensions",CLOSEANGLE
					 , XML_RL,NULL));

	for (dim = variable_dimensions(type_variable(entity_type(var))); !ENDP(dim); dim = CDR(dim)) {

	  intptr_t low;
	  intptr_t  up;
	  expression elow = dimension_lower(DIMENSION(CAR(dim)));
	  expression eup = dimension_upper(DIMENSION(CAR(dim)));
	  if (expression_integer_value(elow, &low) && expression_integer_value(eup, &up)){
	    string_buffer_append(result,
				 concatenate( TAB,OPENANGLE, "range min =", QUOTE,  int2a(low), QUOTE, NULL));
	    string_buffer_append(result,
				 concatenate(" max =", QUOTE,  int2a(up-low+1),QUOTE, SLASH, CLOSEANGLE, XML_RL, NULL));
	  }
	  else pips_user_error("Array dimensions must be integer\n");

	}

	string_buffer_append(result,
			     concatenate(OPENANGLE, SLASH, "dimensions", CLOSEANGLE,NL ,NULL));
	string_buffer_append(result,
			     concatenate(TAB, OPENANGLE, SLASH, "array", CLOSEANGLE, NL, NULL));

      }
  }
}


static void
push_current_statement(statement s, nest_context_p nest)
{
  stack_push(s , nest->current_stat);
}

static void
pop_current_statement(statement s __attribute__ ((unused)),
		      nest_context_p nest)
{
  /*   if (debug) print_statement(s);*/
  stack_pop(nest->current_stat);
}

static void
push_loop(loop l, nest_context_p nest)
{
  /* on sauve le statement associe a la boucle courante */
  statement sl = (statement) stack_head(nest->current_stat);
  stack_push(sl , nest->loops_for_call);
  stack_push(loop_index(l) , nest->loop_indices);
}

static void
pop_loop(_UNUSED_ loop l, nest_context_p nest)
{
  stack_pop(nest->loops_for_call);
  stack_pop(nest->loop_indices);
}

static void
push_if(_UNUSED_ test l, nest_context_p nest)
{
  /* on sauve le statement associe au test */
  statement sl = (statement) stack_head(nest->current_stat);
  stack_push(sl , nest->testif);
}

static void
pop_if(test l __attribute__ ((unused)),
	 nest_context_p nest)
{
  stack_pop(nest->testif);

}
typedef struct {
  entity e;
  bool entity_in_p;
} expression_ctxt;

static void search_1r_function_call(call c)
{
  entity f = call_function(c);
  if  (ENTITY_ASSIGN_P(f) || entity_subroutine_p(f)|| entity_function_p(f))
    if (encapsulated_call ==call_undefined)
      encapsulated_call =c;
}

static bool call_selection(call c, nest_context_p nest __attribute__ ((unused)))
{
  /* CA il faut implemeter  un choix judicieux ... distribution ou encapsulation*/
  /* pour le moment distribution systematique de tout call */
  /* il faut recuperer les appels de fonction value_code_p(entity_initial(f)*/
  entity f = call_function(c);
  if  (ENTITY_ASSIGN_P(f) || entity_subroutine_p(f)|| entity_function_p(f))
    return true;
  else return false;
}

static void store_call_context(call c __attribute__((unused)),
                               nest_context_p nest) {
  /* on sauve le statement associe au call */
  statement statc = (statement)stack_head(nest->current_stat);
  //  if (instruction_call_p(statement_instruction(statc))) {
  stack sl = stack_copy(nest->loops_for_call);
  stack si = stack_copy(nest->loop_indices);
  stack statif = stack_copy(nest->testif);
  gen_array_append(nest->nested_loop_indices, si);
  gen_array_append(nest->nested_loops, sl);
  gen_array_append(nest->nested_call, statc);
  gen_array_append(nest->nested_if, statif);
  //  }
}


// gen_true ?
static bool push_test(test t  __attribute__ ((unused)),
		      nest_context_p nest  __attribute__ ((unused)))
{
  /* encapsulation de l'ensemble des instructions appartenant au test*/
  return true;
}

// gen_null
static void pop_test(test t __attribute__ ((unused)),
		     nest_context_p nest __attribute__ ((unused)))
{
  /* encapsulation de l'ensemble des instructions appartenant au test*/
}



static void
search_nested_loops_and_calls(statement stmp, nest_context_p nest)
{
  gen_context_multi_recurse(stmp,nest, loop_domain,push_loop,pop_loop,
			    statement_domain, push_current_statement,pop_current_statement,
			    test_domain, push_test, pop_test,
			    call_domain,call_selection,store_call_context,
			    NULL);
}

static void __attribute__ ((unused)) print_call_selection(nest_context_p nest)
{
  int j;
  int numberOfTasks=(int) gen_array_nitems(nest->nested_call);
  for (j = 0; j<numberOfTasks; j++)
    {
      //statement s = gen_array_item(nest->nested_call,j);
      //stack st = gen_array_item(nest->nested_loops,j);
      /*   print_statement(s);
	   stack_map( st, print_statement);*/
    }
}


static expression expression_plusplus(expression e)
{
  expression new_e;
  if (expression_constant_p(e)) {
    new_e = int_to_expression(1+ expression_to_int(e));
  }
  else {
    entity add_ent = entity_intrinsic(PLUS_OPERATOR_NAME);
    new_e =  make_call_expression(add_ent,
				  CONS(EXPRESSION, e, CONS(EXPRESSION,  int_to_expression(1), NIL)));
  }
  return new_e;
}

static void xml_loop(stack st, string_buffer result)
{
  string_buffer_append(result,concatenate(TAB,SPACE, OPENANGLE, "outLoop", CLOSEANGLE, NL, NULL));
  string_buffer_append(result,concatenate(TAB,SPACE, SPACE, OPENANGLE, "loopNest", CLOSEANGLE, NL, NULL));
  string_buffer_append(result,concatenate(TAB,SPACE, SPACE, SPACE, OPENANGLE, "bounds", CLOSEANGLE, NL, NULL));

  STACK_MAP_X(s, statement,
	      {
		loop l = instruction_loop(statement_instruction(s));
		expression el =range_lower(loop_range(l));
		expression eu =range_upper(loop_range(l));
		expression new_eu= expression_plusplus(eu);

		string_buffer_append(result,
				     concatenate(TAB,SPACE,SPACE,SPACE,SPACE,OPENANGLE,"bound idx =",QUOTE,entity_user_name(loop_index(l)),QUOTE,NULL));
		string_buffer_append(result,
				     concatenate(SPACE, "lower =",QUOTE,expression_to_string(el),QUOTE,NULL));
		string_buffer_append(result,
				     concatenate(SPACE, "upper =", QUOTE, expression_to_string(new_eu),QUOTE, SLASH, CLOSEANGLE,NL,NULL));
	      },
	      st, 0);

  string_buffer_append(result,concatenate(TAB,SPACE, SPACE, SPACE,  OPENANGLE,SLASH "bounds", CLOSEANGLE, NL, NULL));
  string_buffer_append(result,concatenate(TAB,SPACE, SPACE, OPENANGLE,SLASH, "loopNest", CLOSEANGLE, NL, NULL));
  string_buffer_append(result,concatenate(TAB,SPACE,  OPENANGLE, SLASH, "openLoop", CLOSEANGLE, NL, NULL));
}



static void xml_reference(int taskNumber __attribute__ ((unused)), reference r, bool wmode,
			  string_buffer result)
{

  const char* varname = entity_user_name(reference_variable(r));
  string_buffer_append
    (result,
     concatenate(SPACE, QUOTE, XML_ARRAY_PREFIX, varname, QUOTE, SPACE, "accessMode =", QUOTE,
		 (wmode?"W":"R"),QUOTE, CLOSEANGLE,NL,
		 NULL));
}

static void  find_motif(Psysteme ps, Pvecteur nested_indices, int dim, int nb_dim __attribute__ ((unused)), Pcontrainte *bound_inf, Pcontrainte *bound_sup, Pcontrainte *iterator, int *motif_up_bound, int *lowerbound, int *upperbound)
{
  Variable phi;
  Value	v;
  Pvecteur pi;
  Pcontrainte c, next, cl, cu, cl_dup, cu_dup,lind, lind_dup,
    list_cl=NULL,
    list_cu=NULL,
    list_ind=NULL;
  int lower =1;
  int upper =2;
  int ind =3;
  Pcontrainte bounds[4][4];
  int nb_bounds =0;
  int nb_lower = 0;
  int nb_upper = 0;
  int nb_indices=0;
  int i,j;
  Pbase vars_to_eliminate = BASE_NULLE;

  for (i=1; i<=3;i++)
    for (j=1; j<=3;j++)
      bounds[i][j]=CONTRAINTE_UNDEFINED;

  phi = (Variable) make_phi_entity(dim);
  /* elimination des variables autres de les phi et les indices de boucles englobants
     copie de la base + mise a zero des indices englobants + projection selon les elem de ce vecteur*/

  if (!SC_EMPTY_P(ps)) {
    vars_to_eliminate = vect_copy(ps->base);
    /* printf("Base des variables :\n");
       vect_print(vars_to_eliminate, entity_local_name);
    */
    vect_erase_var(&vars_to_eliminate, phi);
    for (pi = nested_indices; !VECTEUR_NUL_P(pi); pi = pi->succ)
      vect_erase_var(&vars_to_eliminate, var_of(pi));

    /* printf("Elimination des variables :\n");
       vect_print(vars_to_eliminate, entity_local_name);
    */

    sc_projection_along_variables_ofl_ctrl(&ps,vars_to_eliminate , NO_OFL_CTRL);

    for(c = sc_inegalites(ps), next=(c==NULL ? NULL : c->succ);
	c!=NULL;
	c=next, next=(c==NULL ? NULL : c->succ))
      {
	Pvecteur indices_in_vecteur = VECTEUR_NUL;
	/* printf("Tri de la contrainte :\n");
	   vect_print(c->vecteur, entity_local_name);
	*/
	v = vect_coeff(phi, c->vecteur);
	for (pi = nested_indices; !VECTEUR_NUL_P(pi); pi = pi->succ)
	  {
	    int coeff_index = vect_coeff(var_of(pi),c->vecteur);
	    if (coeff_index)
	      vect_add_elem(&indices_in_vecteur,var_of(pi), coeff_index);
	  }

	nb_indices=vect_size(indices_in_vecteur);
	nb_indices = (nb_indices >2) ? 2 : nb_indices;

	if (value_pos_p(v)) {
	  c->succ = bounds[upper][nb_indices+1];
	  bounds[upper][nb_indices+1] = c;
	  /* printf(" bornes inf avec indices de boucles englobants :\n");
	     vect_print(bounds[upper][nb_indices+1]->vecteur, entity_local_name); */
	  nb_upper ++;
	}
	else if (value_neg_p(v)) {
	  c->succ = bounds[lower][nb_indices+1];
	  bounds[lower][nb_indices+1] = c;
	  /* printf(" bornes inf avec indices de boucles englobants :\n");
	     vect_print(bounds[lower][nb_indices+1]->vecteur, entity_local_name);*/
	  lind = contrainte_make(indices_in_vecteur);
	  lind->succ = bounds[ind][nb_indices+1];
	  bounds[ind][nb_indices+1] = lind;
	  /* printf(" indices contenus dans la contrainte :\n");
	     vect_print(bounds[ind][nb_indices+1]->vecteur, entity_local_name); */
	  nb_lower ++;
	}
      }
    /* printf("Nb borne inf = %d, Nb borne sup = %d ;\n",nb_lower,nb_upper); */

    if  (!CONTRAINTE_UNDEFINED_P(bounds[lower][2])) {
      /* case with 1 loop index in the loop bound constraints */
      for(cl = bounds[lower][2], lind= bounds[ind][2]; cl !=NULL; cl=cl->succ,lind=lind->succ)  {
	for(cu = bounds[upper][2]; cu !=NULL; cu =cu->succ) {
	  /*  printf("Tests de la negation des  contraintes :\n");
	      vect_print(cl->vecteur, entity_local_name);
	      vect_print(cu->vecteur, entity_local_name); */
	  if (vect_opposite_except(cl->vecteur,cu->vecteur,TCST)){
	    cl_dup = contrainte_dup(cl);
	    cl_dup->succ = list_cl, list_cl=cl_dup;
	    cu_dup = contrainte_dup(cu);
	    cu_dup->succ = list_cu, list_cu=cu_dup;
	    lind_dup = contrainte_dup(lind);
	    lind_dup->succ = list_ind, list_ind = lind_dup;
	    nb_bounds ++;
	  }
	}
      }
      *bound_inf= list_cl;
      *bound_sup = list_cu;
      *iterator = list_ind;
      *motif_up_bound =- vect_coeff(TCST,list_cl->vecteur) - vect_coeff(TCST,list_cu->vecteur) +1;
      *lowerbound = vect_coeff(TCST,list_cl->vecteur);
      *upperbound = vect_coeff(TCST,list_cu->vecteur)+1;
    }
    else if (!CONTRAINTE_UNDEFINED_P(bounds[lower][1]) && !CONTRAINTE_UNDEFINED_P(bounds[upper][1])) {
      /* case where loop bounds are numeric */
      *bound_inf= bounds[lower][1];
      *bound_sup = bounds[upper][1];
      *iterator =  bounds[ind][1];
      *motif_up_bound = - vect_coeff(TCST,bounds[lower][1]->vecteur)
	- vect_coeff(TCST,bounds[upper][1]->vecteur)+1;
      *upperbound = vect_coeff(TCST,bounds[upper][1]->vecteur)+1;
      *lowerbound = vect_coeff(TCST,bounds[lower][1]->vecteur);
    } else {
      /* Only bounds with several loop indices */
      /* printf("PB - Only bounds with several loop indices\n"); */
      *bound_inf= CONTRAINTE_UNDEFINED;
      *bound_sup = CONTRAINTE_UNDEFINED;
      *iterator = CONTRAINTE_UNDEFINED;
      *motif_up_bound = 1;
      *upperbound = 1;
      *lowerbound = 0;
    }
  }
  vect_rm( vars_to_eliminate);
}


static void xml_tiling(int taskNumber, reference ref,  region reg, stack indices,  string_buffer result)
{
  fprintf(stderr,"XML");
  Psysteme ps_reg = sc_dup(region_system(reg));
  entity var = reference_variable(ref);
  int dim = (int) gen_length(variable_dimensions(type_variable(entity_type(var))));
  int i, j ;
  string_buffer buffer_bound = string_buffer_make(true);
  string_buffer buffer_offset = string_buffer_make(true);
  string_buffer buffer_fitting = string_buffer_make(true);
  string_buffer buffer_paving = string_buffer_make(true);
  string string_bound = "";
  string string_offset = "";
  string string_paving = "";
  string string_fitting =  "";
  Pvecteur iterat, pi= VECTEUR_NUL;
  Pcontrainte bound_inf = CONTRAINTE_UNDEFINED;
  Pcontrainte bound_up = CONTRAINTE_UNDEFINED;
  Pcontrainte iterator = CONTRAINTE_UNDEFINED;
  int motif_up_bound =0;
  int lowerbound = 0;
  int upperbound = 0;
  int dim_indices= stack_size(indices);
  int pav_matrix[10][10], fit_matrix[10][10];

  for (i=1; i<=9;i++)
    for (j=1;j<=9;j++)
      pav_matrix[i][j]=0, fit_matrix[i][j]=0;

  STACK_MAP_X(index,entity,
	      {
		vect_add_elem (&pi,(Variable) index ,VALUE_ONE);
	      }, indices,1);

  for(i=1; i<=dim ; i++) {
    Psysteme ps = sc_dup(ps_reg);
    sc_transform_eg_in_ineg(ps);

    find_motif(ps, pi, i,  dim, &bound_inf, &bound_up, &iterator,
	       &motif_up_bound, &lowerbound, &upperbound);
    string_buffer_append(buffer_offset,
			 concatenate(TAB,TAB,OPENANGLE,"offset val =", QUOTE,
				     (CONTRAINTE_UNDEFINED_P(bound_inf))? "0" :
				     int2a(vect_coeff(TCST,bound_inf->vecteur)),
				     QUOTE, SLASH, CLOSEANGLE,NL,NULL));
    if (!CONTRAINTE_UNDEFINED_P(iterator)) {
      for (iterat = pi, j=1; !VECTEUR_NUL_P(iterat); iterat = iterat->succ, j++)
	pav_matrix[i][j]= vect_coeff(var_of(iterat),iterator->vecteur);
    }
    if (!CONTRAINTE_UNDEFINED_P(bound_inf))
      fit_matrix[i][i]= (motif_up_bound >1) ? 1:0;

    string_buffer_append(buffer_bound,
			 concatenate(TAB,TAB, OPENANGLE, "bound idx=",
				     QUOTE, XML_MOTIF_PREFIX, int2a(taskNumber),"_",
				     entity_user_name(var), "_",int2a(i),QUOTE, SPACE,
				     "lower =" QUOTE,int2a(lowerbound),QUOTE,
				     SPACE, "upper =", QUOTE, int2a(upperbound),
				     QUOTE, SLASH, CLOSEANGLE,
				     NL,NULL));
  }

  for (j=1; j<=dim_indices ; j++){
    string_buffer_append(buffer_paving,concatenate(TAB,TAB, OPENANGLE,"row",
						   CLOSEANGLE,NULL));
    for(i=1; i<=dim ; i++)
      string_buffer_append(buffer_paving,
			   concatenate(OPENANGLE, "cell val =", QUOTE,
				       int2a( pav_matrix[i][j]),QUOTE, SLASH,
				       CLOSEANGLE,NULL));
    string_buffer_append(buffer_paving,concatenate(OPENANGLE,SLASH, "row",
						   CLOSEANGLE,NL,NULL));
  }
  for(i=1; i<=dim ; i++) {
    string_buffer_append(buffer_fitting,concatenate(TAB, TAB,OPENANGLE,"row",
						    CLOSEANGLE,NULL));
    for(j=1; j<=dim ; j++)
      string_buffer_append(buffer_fitting, concatenate(OPENANGLE, "cell val =", QUOTE,
						       int2a( fit_matrix[i][j]),
						       QUOTE, SLASH,
						       CLOSEANGLE,NULL));

    string_buffer_append(buffer_fitting,concatenate(OPENANGLE,SLASH, "row",
						    CLOSEANGLE,NL,NULL));
  }
  string_buffer_append(result,concatenate(TAB,SPACE,SPACE,OPENANGLE,"origin",
					  CLOSEANGLE,NL,NULL));
  string_offset =string_buffer_to_string(buffer_offset);
  string_buffer_append(result,string_offset);
  free(string_offset);
  string_offset=NULL;
  string_buffer_append(result,concatenate(TAB,SPACE,SPACE,OPENANGLE,SLASH,"origin",
					  CLOSEANGLE,NL,NULL));

  string_buffer_append(result,concatenate(TAB,SPACE,SPACE,OPENANGLE,"fitting",
					  CLOSEANGLE,NL,NULL));
  string_fitting =string_buffer_to_string(buffer_fitting);
  string_buffer_append(result,string_fitting);
  free(string_fitting);
  string_fitting=NULL;
  string_buffer_append(result,concatenate(TAB,SPACE,SPACE,OPENANGLE,SLASH,"fitting",
					  CLOSEANGLE,NL,NULL));
  string_buffer_append(result,concatenate(TAB,SPACE,SPACE,OPENANGLE,"paving",
					  CLOSEANGLE,NL,NULL));
  string_paving =string_buffer_to_string(buffer_paving);
  string_buffer_append(result,string_paving);
  free(string_paving);
  string_paving=NULL;
  string_buffer_append(result,concatenate(TAB,SPACE,SPACE,OPENANGLE,SLASH,"paving",
					  CLOSEANGLE,NL,NULL));
  string_buffer_append(result,concatenate(TAB,SPACE, OPENANGLE, "inLoop",
					  CLOSEANGLE, NL, NULL));
  string_buffer_append(result,concatenate(TAB,SPACE, SPACE, OPENANGLE, "loopNest",
					  CLOSEANGLE, NL, NULL));
  string_buffer_append(result,concatenate(TAB,SPACE, SPACE, SPACE, OPENANGLE, "bounds",
					  CLOSEANGLE, NL, NULL));
  string_bound =string_buffer_to_string(buffer_bound);
  string_buffer_append(result,string_bound);
  free(string_bound);
  string_bound=NULL;

  string_buffer_append(result,concatenate(TAB,SPACE, SPACE, SPACE,OPENANGLE,
					  SLASH "bounds", CLOSEANGLE, NL, NULL));
  string_buffer_append(result,concatenate(TAB,SPACE, SPACE, OPENANGLE,SLASH, "loopNest",
					  CLOSEANGLE, NL, NULL));
  string_buffer_append(result,concatenate(TAB,SPACE,  OPENANGLE, SLASH, "inLoop",
					  CLOSEANGLE, NL, NULL));


}

static void xml_references(int taskNumber, list l_regions, stack indices, string_buffer result)
{
  list lr;
  bool atleast_one_read_ref = false;
  bool atleast_one_written_ref = false;
  /*   Read array references first */
  for ( lr = l_regions; !ENDP(lr); lr = CDR(lr))
    {
      region re = REGION(CAR(lr));
      reference ref = effect_any_reference(re);
      if (array_entity_p(reference_variable(ref)) && region_read_p(re)) {
	atleast_one_read_ref = true;
	string_buffer_append(result,concatenate(TAB, SPACE, SPACE, OPENANGLE,  "data darray=",NULL));
	xml_reference(taskNumber, ref,  region_write_p(re), result);
	xml_tiling(taskNumber, ref,re, indices, result);
      }
    }
  if (!atleast_one_read_ref)
    string_buffer_append(result,concatenate(TAB,SPACE, SPACE, "dummyDATA",
					    NL,NULL));
  for ( lr = l_regions; !ENDP(lr); lr = CDR(lr))
    {
      region re = REGION(CAR(lr));
      reference ref = effect_any_reference(re);
      if (array_entity_p(reference_variable(ref)) && region_write_p(re)) {
	atleast_one_written_ref = true;
	string_buffer_append(result,concatenate(TAB, SPACE, SPACE, OPENANGLE, "data darray=",NULL));
	xml_reference(taskNumber, ref,  region_write_p(re), result);
	xml_tiling(taskNumber, ref,re, indices, result);
      }
    }
  if (!atleast_one_written_ref)
    string_buffer_append(result,concatenate(TAB,SPACE, SPACE,"dummyDATA",NL,NULL));
}

static void xml_data(int taskNumber,statement s, stack indices, string_buffer result )
{

  list  l_regions = regions_dup(load_statement_local_regions(s));
  string_buffer_append(result,concatenate(TAB,SPACE, OPENANGLE, "dataList", CLOSEANGLE, NL,NULL));
  /*
    ifdebug(2) {
    fprintf(stderr, "\n list of regions ");
    print_regions(l_regions);
    fprintf(stderr, "\n for the statement");
    print_statement(s);
    }
  */
  xml_references(taskNumber, l_regions, indices, result);
  string_buffer_append(result,concatenate(TAB,SPACE,OPENANGLE, SLASH, "dataList", CLOSEANGLE,NL,NULL));
  regions_free(l_regions);
}

static string task_complexity(statement s)
{
  complexity stat_comp = load_statement_complexity(s);
  string r;
  if(stat_comp != (complexity) HASH_UNDEFINED_VALUE && !complexity_zero_p(stat_comp)) {
    cons *pc = CHAIN_SWORD(NIL, complexity_sprint(stat_comp, false,
						  true));
    r = words_to_string(pc);
  }
  else r = int2a(1);
  return  (r);
}
static void xml_task( int taskNumber, nest_context_p nest, string_buffer result)
{

  statement s = gen_array_item(nest->nested_call,taskNumber);
  stack st = gen_array_item(nest->nested_loops,taskNumber);
  stack sindices = gen_array_item(nest->nested_loop_indices,taskNumber);

  string_buffer_append(result, concatenate(NL,TAB,OPENANGLE,"task name =", QUOTE, XML_TASK_PREFIX,int2a(taskNumber),QUOTE, CLOSEANGLE, NL, NULL));
  string_buffer_append(result, concatenate(TAB, SPACE, OPENANGLE, "unitSpentTime", CLOSEANGLE,task_complexity(s),NULL));
  string_buffer_append(result, concatenate(OPENANGLE,SLASH,"unitSpentTime",CLOSEANGLE,NL,NULL));

  xml_loop(st, result);
  xml_data (taskNumber, s,sindices, result);
  string_buffer_append(result, concatenate(TAB,OPENANGLE,SLASH,"task",CLOSEANGLE, NL, NULL));
}

static void  xml_tasks(statement stat, string_buffer result){

  const char*  module_name = get_current_module_name();
  nest_context_t nest;
  int taskNumber =0;
  nest.loops_for_call = stack_make(statement_domain,0,0);
  nest.loop_indices = stack_make(entity_domain,0,0);
  nest.current_stat = stack_make(statement_domain,0,0);
  nest.nested_loops=  gen_array_make(0);
  nest.nested_loop_indices =  gen_array_make(0);
  nest.nested_call=  gen_array_make(0);

  string_buffer_append(result,concatenate(NL,SPACE,OPENANGLE,"tasks",CLOSEANGLE,NL, NULL));

  if(statement_undefined_p(stat)) {
    pips_internal_error("statement error");
  }

  search_nested_loops_and_calls(stat,&nest);
  /* ifdebug(2)  print_call_selection(&nest); */

  for (taskNumber = 0; taskNumber<(int) gen_array_nitems(nest.nested_call); taskNumber++)

    xml_task(taskNumber, &nest,result);
  string_buffer_append(result,concatenate(SPACE,OPENANGLE, SLASH, "tasks", CLOSEANGLE, NL,NULL));
  string_buffer_append(result,
		       concatenate(SPACE, OPENANGLE,
				   "application name = ",
				   QUOTE, module_name, QUOTE, CLOSEANGLE
				   NL, NULL));

  for(taskNumber = 0; taskNumber<(int) gen_array_nitems(nest.nested_call)-1; taskNumber++)
    string_buffer_append(result,concatenate(TAB, OPENANGLE, "taskref ref = ", QUOTE, XML_TASK_PREFIX,
					    int2a(taskNumber),QUOTE, SLASH,  CLOSEANGLE, NL, NULL));

  string_buffer_append(result,concatenate(TAB, OPENANGLE, "taskref ref = ", QUOTE, XML_TASK_PREFIX,
					  int2a(taskNumber),QUOTE, SLASH,  CLOSEANGLE, NL, NULL));

  string_buffer_append(result,concatenate(SPACE, OPENANGLE, SLASH, "application",CLOSEANGLE, NL, NULL));

  gen_array_free(nest.nested_loops);
  gen_array_free(nest.nested_loop_indices);
  gen_array_free(nest.nested_call);
  stack_free(&(nest.loops_for_call));
  stack_free(&(nest.loop_indices));
  stack_free(&(nest.current_stat));

}

/* Creates string for xml pretty printer.
   This string divides in declarations (array decl.) and
   tasks which are loopnests with an instruction at the core.
*/

static string xml_code(entity module, statement stat)
{
  string_buffer result=string_buffer_make(true);
  string result2;

  string_buffer_append(result,concatenate(OPENANGLE, "module name=", QUOTE,get_current_module_name(), QUOTE, CLOSEANGLE, NL, NULL ));
  xml_declarations(module,result);
  xml_tasks(stat,result);

  string_buffer_append(result,concatenate(OPENANGLE, SLASH, "module", CLOSEANGLE, NL, NULL ));
  result2=string_buffer_to_string(result);
  /* ifdebug(2)
     {
     printf("%s", result2);
     } */
  return result2;
}

static bool valid_specification_p(entity module __attribute__ ((unused)),
				  statement stat __attribute__ ((unused)))
{ return true;
}

/******************************************************** PIPSMAKE INTERFACE */

/* Initiates xml pretty print modules
 */

bool print_xml_code(const char* module_name)
{
  FILE * out;
  string ppt;
  entity module = module_name_to_entity(module_name);
  string xml = db_build_file_resource_name(DBR_XML_PRINTED_FILE,
					   module_name, ".xml");
  string  dir = db_get_current_workspace_directory();
  string filename = strdup(concatenate(dir, "/", xml, NULL));
  statement stat=(statement) db_get_memory_resource(DBR_CODE,
						    module_name, true);

  init_cost_table();
  /* Get the READ and WRITE regions of the module */
  set_rw_effects((statement_effects)
		 db_get_memory_resource(DBR_REGIONS, module_name, true));

  set_complexity_map( (statement_mapping)
		      db_get_memory_resource(DBR_COMPLEXITIES, module_name, true));

  if(statement_undefined_p(stat))
    {
      pips_internal_error("No statement for module %s", module_name);
    }
  set_current_module_entity(module);
  set_current_module_statement(stat);

  debug_on("XMLPRETTYPRINTER_DEBUG_LEVEL");
  pips_debug(1, "Spec validation before xml prettyprinter for %s\n",
	     entity_name(module));
  if (valid_specification_p(module,stat)){
    pips_debug(1, "Spec is valid\n");
    pips_debug(1, "Begin XML prettyprinter for %s\n", entity_name(module));
    ppt = xml_code(module, stat);
    pips_debug(1, "end\n");
    debug_off();
    /* save to file */
    out = safe_fopen(filename, "w");
    fprintf(out,"%s",ppt);
    safe_fclose(out, filename);
    free(ppt);
  }

  free(dir);
  free(filename);

  DB_PUT_FILE_RESOURCE(DBR_XML_PRINTED_FILE, module_name, xml);

  reset_current_module_statement();
  reset_current_module_entity();
  reset_complexity_map();
  reset_rw_effects();
  return true;
}



//================== PRETTYPRINT TERAOPT DTD ============================


static string vect_to_string(Pvecteur pv) {
  return  expression_to_string(make_vecteur_expression(pv));
}

/* UNUSED
static bool vect_one_p(Pvecteur v) {
  return  (!VECTEUR_NUL_P(v) && vect_size(v) == 1 && vect_coeff(TCST, v) ==1);
}
*/

/* UNUSED
static bool vect_zero_p(Pvecteur v) {
  return  (VECTEUR_NUL_P(v) ||
	   (!VECTEUR_NUL_P(v) && vect_size(v) == 1 && value_zero_p(vect_coeff(TCST, v))));
}
*/

static void type_and_size_of_var(entity var, const char ** datatype, int *size)
{
  // type t = ultimate_type(entity_type(var));
  type t = entity_type(var);
  if (type_variable_p(t)) {
    basic b = variable_basic(type_variable(t));
    int e = SizeOfElements(b);
    if (e==-1)
      *size = 9999;
    else
      *size = e;
    *datatype =basic_to_string(b);
  }
}


static void add_margin(int gm, string_buffer sb_result) {
  int i;
  for (i=1;i<=gm;i++)
    string_buffer_append(sb_result, "  ");
}

static void string_buffer_append_word(string str, string_buffer sb_result)
{
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,NULL));
  string_buffer_append_xml_text(sb_result, str, false);
  string_buffer_append(sb_result,
		       concatenate(CLOSEANGLE, NL, NULL));
}

static void string_buffer_append_symbolic(string str, string_buffer sb_result){
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE, "Symbolic", CLOSEANGLE, NULL));
  string_buffer_append_xml_text(sb_result, str, false);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,"/Symbolic",CLOSEANGLE,
				   NL, NULL));
}

static void two_string_buffer_append_symbolic(string str1, string str2, string_buffer sb_result){
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,"Symbolic",CLOSEANGLE, NULL));
  string_buffer_append_xml_text(sb_result,str1,false);
  string_buffer_append_xml_text(sb_result,str2,false);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,"/Symbolic",CLOSEANGLE,
				   NL, NULL));
}

static void string_buffer_append_numeric(string str, string_buffer sb_result){
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,"Numeric",CLOSEANGLE,
				   str,
				   OPENANGLE,"/Numeric",CLOSEANGLE,
				   NL, NULL));
}



static void
find_loops_and_calls_in_box(statement stmp, nest_context_p nest)
{
  gen_context_multi_recurse(stmp,nest, loop_domain,push_loop,pop_loop,
			    statement_domain, push_current_statement,pop_current_statement,
			    test_domain, push_if, pop_if,
			    call_domain,call_selection,store_call_context,
			    NULL);
}

// A completer
static void xml_Library(string_buffer sb_result)
{
  string_buffer_append_word("Library",sb_result);
  string_buffer_append_word("/Library",sb_result);
}
// A completer
static void xml_Returns(string_buffer sb_result __attribute__ ((unused)))
{
  //string_buffer_append_word("Returns",sb_result);
  //string_buffer_append_word("/Returns",sb_result);
}
// A completer
static void xml_Timecosts(string_buffer sb_result __attribute__ ((unused)))
{
  //string_buffer_append_word("Timecosts",sb_result);
  // string_buffer_append_word("/Timecosts",sb_result);
}

// A completer
static void  xml_AccessFunction(string_buffer sb_result __attribute__ ((unused)))
{
  //string_buffer_append_word("AccessFunction",sb_result);
  //string_buffer_append_word("/AccessFunction",sb_result);
}
// A completer
static void xml_Regions(string_buffer sb_result __attribute__ ((unused)))
{
  // string_buffer_append_word("Regions",sb_result);
  // string_buffer_append_word("/Regions",sb_result);
}
// A completer
static void xml_CodeSize(string_buffer sb_result)
{
  string_buffer_append_word("CodeSize",sb_result);
  string_buffer_append_word("/CodeSize",sb_result);
}

// A changer par une fonction qui detectera si la variable a ete definie
// dans un fichier de parametres ...
static bool entity_xml_parameter_p(entity e)
{
  const char* s = entity_local_name(e);
  bool b=false;
  if (strstr(s,"PARAM")!=NULL || strstr(s,"param")!=NULL) b = true;
  return (b);
}

typedef struct Spattern {
  Pvecteur diff;
  Pvecteur lower;
  Pvecteur upper;
  Pvecteur lind;
  int cl_coeff;
  bool unitp;
  struct Spattern *next;
} Spattern, *Ppattern;

/*
Pour traiter les cas ou il y a des patterns symboliques, sans preconditions
interprocedurales permettant d'evaluer un min sur les bornes:
Choix selon ordre de priorite:
 - borne numerique
 - borne symbolique avec un seul parametre et coeff ==1
 - borne symbolique avec un seul parametre
 - la premiere borne symbolique avec plusieurs parametres
*/

static  void choose_pattern(Ppattern *patt)
{
  Ppattern patt1= NULL,
    pattn= NULL,
    pattc1= NULL,
    pattcx= NULL,
    pattcp= NULL;
  Pvecteur pv;
  for(patt1 = *patt; patt1 !=NULL; patt1=patt1->next)  {
    if  (vect_size(patt1->diff) ==1) {
      if (vect_dimension(patt1->diff)==0) // borne constante numerique
	pattn = patt1;
      else  { // borne constante symbolique
	for (pv = patt1->diff;pv!=NULL;pv=pv->succ) {
	  if (pv->var!= TCST) {
	    if (pv->val ==1)
	      pattc1=patt1;
	    else pattcx = patt1;
	  }
	}
      }
    }
    else pattcp = patt1;
  }
    if (pattn!=NULL ) *patt=pattn;
    else if (pattc1!= NULL) *patt=pattc1;
    else if (pattcx!=NULL ) *patt=pattcx;
    else *patt=pattcp;
}


//static void  find_pattern(Psysteme ps, Pvecteur paving_indices, Pvecteur formal_parameters, int dim,  Pcontrainte *bound_inf, Pcontrainte *bound_sup, Pcontrainte *pattern_up_bound , Pcontrainte *iterator, int *mult)
static void  find_pattern(Psysteme ps, Pvecteur paving_indices, Pvecteur formal_parameters, int dim,  Ppattern *patt)
{
  Variable phi;
  Value	v;
  Pvecteur pi;
  Pcontrainte c, next, cl, cu, lind;
  *patt = NULL;
  int lower =1;
  int upper =2;
  int ind =3;
  Pcontrainte bounds[4][4];
  int nb_bounds =0;
  int nb_lower = 0;
  int nb_upper = 0;
  int nb_indices=0;
  int i,j;
  Pbase vars_to_eliminate = BASE_NULLE;
  Pvecteur vdiff = VECTEUR_NUL,
    diff2 = VECTEUR_NUL;
  // DEBUG  Ppattern pt= NULL;
  Ppattern patt1=NULL;
  int mult=1;
  for (i=1; i<=3;i++)
    for (j=1; j<=3;j++)
      bounds[i][j]=CONTRAINTE_UNDEFINED;

  phi = (Variable) make_phi_entity(dim);

  /* Liste des  variables a eliminer autres de les phi et les indices de boucles englobants
     et les parametres formels de la fonction.
     copie de la base + mise a zero des indices englobants
     + projection selon les elem de ce vecteur
  */
  if (!SC_EMPTY_P(ps)) {

    Psysteme ps_dup=sc_dup(ps);
    vars_to_eliminate = vect_copy(ps->base);
    vect_erase_var(&vars_to_eliminate, phi);

    //printf("paving_indices:\n");
    //vect_fprint(stdout,paving_indices,(char * (*)(Variable))  entity_local_name);

    for (pi = paving_indices; !VECTEUR_NUL_P(pi); pi = pi->succ)
      vect_erase_var(&vars_to_eliminate, var_of(pi));
    //printf("formal_parameters:\n");
    // vect_fprint(stdout,formal_parameters,(char * (*)(Variable)) entity_local_name);

    for (pi = formal_parameters; !VECTEUR_NUL_P(pi); pi = pi->succ)
      vect_erase_var(&vars_to_eliminate, var_of(pi));
    //printf("vars_to_eliminate:\n");
    //vect_fprint(stdout,vars_to_eliminate,(char * (*)(Variable)) entity_local_name);

    sc_projection_along_variables_ofl_ctrl(&ps_dup,vars_to_eliminate , NO_OFL_CTRL);

    //printf("Systeme a partir duquel on genere les contraintes  du motif:\n");
    //sc_fprint(stdout,ps,entity_local_name);

    for(c = sc_inegalites(ps_dup), next=(c==NULL ? NULL : c->succ);
	c!=NULL;
	c=next, next=(c==NULL ? NULL : c->succ))
      {
	Pvecteur indices_in_vecteur = VECTEUR_NUL;
	vdiff = VECTEUR_NUL;
	v = vect_coeff(phi, c->vecteur);
	for (pi = paving_indices; !VECTEUR_NUL_P(pi); pi = pi->succ)
	  {
	    int coeff_index = vect_coeff(var_of(pi),c->vecteur);
	    if (coeff_index)
	      vect_add_elem(&indices_in_vecteur,var_of(pi), coeff_index);
	  }
	/* on classe toutes les contraintes ayant plus de 2 indices de boucles
	   externes ensemble */
	nb_indices=vect_size(indices_in_vecteur);
	nb_indices = (nb_indices >2) ? 2 : nb_indices;

	if (value_pos_p(v)) {
	  c->succ = bounds[upper][nb_indices+1];
	  bounds[upper][nb_indices+1] = c;

	  //  printf(" bornes sup avec indices de boucles englobants :\n");
	  //    vect_print(bounds[upper][nb_indices+1]->vecteur, (char * (*)(Variable)) entity_local_name);
	  nb_upper ++;
	}
	else if (value_neg_p(v)) {
	  c->succ = bounds[lower][nb_indices+1];
	  bounds[lower][nb_indices+1] = c;
	  //   printf(" bornes inf avec indices de boucles englobants :\n");
	  //    vect_print(bounds[lower][nb_indices+1]->vecteur, (char * (*)(Variable)) entity_local_name);
	  lind = contrainte_make(indices_in_vecteur);
	  lind->succ = bounds[ind][nb_indices+1];
	  bounds[ind][nb_indices+1] = lind;
	  //   printf(" indices contenus dans la contrainte :\n");
	  //    vect_print(bounds[ind][nb_indices+1]->vecteur, (char * (*)(Variable)) entity_local_name);
	  nb_lower ++;
	}
      }
    // printf("Nb borne inf = %d, Nb borne sup = %d pour dimension %d;\n",nb_lower,nb_upper,dim);


    for (int nb_ind=2; nb_ind>=1; nb_ind--){
	/* case with 1 loop index in the loop bound constraints than 0 */
      if  (!CONTRAINTE_UNDEFINED_P(bounds[lower][nb_ind])) {
	for(cl = bounds[lower][nb_ind], lind= bounds[ind][nb_ind]; cl !=NULL; cl=cl->succ,lind=lind->succ)  {
	  for(cu = bounds[upper][nb_ind]; cu !=NULL; cu =cu->succ) {
	    Value cv1 = vect_coeff(phi, cl->vecteur);
	    Value cv2 = vect_coeff(phi, cu->vecteur);
	    if (value_abs(cv1)==value_abs(cv2)) {
	      vdiff = vect_add(cu->vecteur,cl->vecteur);
	      mult=value_abs(cv1);
	    }
	    else {
	      vdiff = vect_cl2(value_abs(cv1),cu->vecteur,value_abs(cv2),cl->vecteur);
	      mult=(int) value_abs(cv1 * cv2);
	    }
	    vect_chg_sgn(vdiff);

	    // le +1 est ajoute dans l'expression apres division lorsque mult!=1
	    if (mult==1)
	      vect_add_elem(&vdiff,TCST,1);
	    //  pattern = contrainte_make(vect_dup(vdiff));

	    diff2=vect_dup(vdiff);
	    for (pi = formal_parameters; !VECTEUR_NUL_P(pi); pi = pi->succ)
	      vect_erase_var(&vdiff, var_of(pi));

	    if (vect_dimension(vdiff)==0) {
	      patt1= (Ppattern) malloc(sizeof(Spattern));
	      patt1->diff = vect_dup(diff2);
	      patt1->lower = vect_dup(cl->vecteur);
	      patt1->upper = vect_dup(cu->vecteur);
	      patt1->lind = vect_dup(lind->vecteur);
	      patt1->cl_coeff=mult;
	      patt1->unitp=(vect_dimension(diff2)==0 && vect_coeff(TCST, diff2)==1)?true:false;

	      vect_chg_sgn(patt1->upper);
	      for (pi = lind->vecteur; !VECTEUR_NUL_P(pi); pi = pi->succ) {
	     	vect_erase_var(&(patt1->lower), var_of(pi));
	      	vect_erase_var(&(patt1->upper), var_of(pi));
	      }
	      vect_erase_var(&(patt1->lower), phi);
	      vect_erase_var(&(patt1->upper),phi);
	      patt1->next = *patt, *patt=patt1;
	      nb_bounds ++;
	    }
	    vect_rm(vdiff);
	    vect_rm(diff2);
	  }
	}
      }
    }
    /* DEBUG
    printf("Liste des contraintes ajoutees PHI-%d: \n",dim);
      for (pt=*patt; pt != NULL; pt=pt->next) {
      vect_fprint(stdout, pt->diff, (char * (*)(Variable)) entity_local_name);
      vect_fprint(stdout, pt->lower, (char * (*)(Variable)) entity_local_name);
      vect_fprint(stdout, pt->upper, (char * (*)(Variable)) entity_local_name);
      vect_fprint(stdout, pt->lind, (char * (*)(Variable)) entity_local_name);
      fprintf(stdout,"mult = %d\n", pt->cl_coeff);
      } */

    choose_pattern(patt);
     /* DEBUG
	pt =*patt;
    if (patt != NULL && pt != NULL) {
    printf("Pattern choisi : \n");
    vect_fprint(stdout, pt->diff, (char * (*)(Variable)) entity_local_name);
    vect_fprint(stdout, pt->lower, (char * (*)(Variable)) entity_local_name);
    vect_fprint(stdout, pt->upper, (char * (*)(Variable)) entity_local_name);
    vect_fprint(stdout, pt->lind, (char * (*)(Variable)) entity_local_name);
    fprintf(stdout,"mult = %d\n", pt->cl_coeff);
    } */

    base_rm( vars_to_eliminate);
    sc_rm(ps_dup);
  }
}

static void xml_Pattern_Paving( region reg,entity var, bool effet_read, Pvecteur formal_parameters, Pvecteur paving_indices, string_buffer sb_result)
{
  string_buffer buffer_pattern = string_buffer_make(true);
  string_buffer buffer_paving = string_buffer_make(true);
  string string_paving = "";
  string string_pattern =  "";
  Pvecteur voffset;

  if(reg != region_undefined) {
    reference ref = effect_any_reference(reg);
    entity vreg = reference_variable(ref);
    if ( array_entity_p(reference_variable(ref)) && same_entity_p(vreg,var) && region_read_p(reg)== effet_read) {
      Psysteme ps_reg = sc_dup(region_system(reg));
      Pvecteur iterat= VECTEUR_NUL;
      Pvecteur iterator = VECTEUR_NUL;
      Ppattern patt=NULL;
      Pvecteur vpattern=VECTEUR_NUL;
      int dim = (int) gen_length(variable_dimensions(type_variable(entity_type(var))));
      int i ;
      int val =0;
      int inc =0;
      dimension vreg_dim = dimension_undefined;
      int mult=1;
      if (!SC_UNDEFINED_P(ps_reg))
	sc_transform_eg_in_ineg(ps_reg);
      add_margin(global_margin,buffer_pattern);
      string_buffer_append(buffer_pattern,
			   concatenate(OPENANGLE,
				       "Pattern AccessMode=",
				       QUOTE,(effet_read)? "USE":"DEF",QUOTE,CLOSEANGLE,NL,NULL));
      add_margin(global_margin,buffer_paving);
      string_buffer_append(buffer_paving,
			   concatenate(OPENANGLE,
				       "Pavage AccessMode=",
				       QUOTE,(effet_read)? "USE":"DEF",QUOTE,CLOSEANGLE,NL,NULL));
      global_margin++;
      // pour chaque dimension : generer en meme temps le pattern et le pavage
      for(i=1; i<=dim; i++) {
	int uniqp=0;
	voffset =vect_new(TCST,0);
	patt = NULL;
	//	printf("find pattern for entity %s [dim=%d]\n",entity_local_name(var),i);
     	//     sc_fprint(stdout,ps_reg,(char * (*)(Variable)) entity_local_name);
	//	printf("paving_indices:\n");
	//	vect_fprint(stdout,paving_indices,(char * (*)(Variable))  entity_local_name);

	//find_pattern(ps_reg, paving_indices, formal_parameters, i, &bound_inf, &bound_up, &pattern_up_bound, &iterator, &mult);
	find_pattern(ps_reg, paving_indices, formal_parameters, i, &patt);
	if (patt !=NULL) {
	  vpattern=patt->diff;
	  iterator= patt->lind;
	  mult = patt->cl_coeff;
	  uniqp=patt->unitp;
	  voffset = patt->lower;
	}
	else
	  {
	    vpattern=VECTEUR_NUL;
	    iterator = VECTEUR_NUL;
	  }

	//	printf("pattern_bound:\n");
	//if (!VECTEUR_NUL_P(vpattern))
	//  vect_fprint(stdout,vpattern,(char * (*)(Variable))  entity_local_name);
	/*	phi = (Variable) make_phi_entity(i);
	if(!SC_UNDEFINED_P(ps_reg) && base_contains_variable_p(sc_base(ps_reg),phi)) {
	  ps1 = sc_dup(ps_reg);
	  feasible = sc_minmax_of_variable(ps1, (Variable)phi, &min, &max);
	  if (feasible){
	    if (min!=VALUE_MIN)
	      voffset = vect_new(TCST,min);
	    //  if (min==max)
	    // uniqp=1;
	  }
	}
	*/

	if (!uniqp) {
	  if (VECTEUR_NUL_P(vpattern)) { // if we cannot deduce pattern length from region, array dim size is taken
	    list ldim = variable_dimensions(type_variable(entity_type(vreg)));
	    vreg_dim = find_ith_dimension(ldim,i);
	    normalized ndim = NORMALIZE_EXPRESSION(dimension_upper(vreg_dim));
	    vpattern = vect_dup((Pvecteur) normalized_linear(ndim));
	    if (vpattern != VECTEUR_NUL)
	      vect_add_elem(&vpattern,TCST,1);
	  }
	}
	/* PRINT PATTERN and PAVING */
	//	if ((vect_zero_p(voffset)  && (!VECTEUR_NUL_P(vpattern) && vect_one_p(vpattern)))
	//      || (uniqp && vect_zero_p(voffset)))
	if (!VECTEUR_NUL_P(vpattern) && uniqp && vect_dimension(voffset)==0 && vect_coeff(TCST,voffset)==0)
	  string_buffer_append_word("DimUnitPattern/",buffer_pattern);
	else {
	  add_margin(global_margin,buffer_pattern);
	  // A completer - choisir un indice pour le motif ?
	  string_buffer_append(buffer_pattern,
			       concatenate(OPENANGLE,
					   "DimPattern Index=",QUOTE, QUOTE,CLOSEANGLE,NL,NULL));

	  global_margin++;
	  string_buffer_append_word("Offset",buffer_pattern);
	  string_buffer_append_symbolic(vect_to_string(voffset),
					buffer_pattern);
	  if (vect_dimension(voffset)==0)
	    string_buffer_append_numeric(vect_to_string(voffset),
					 buffer_pattern);
	  string_buffer_append_word("/Offset",buffer_pattern);

	  string_buffer_append_word("Length",buffer_pattern);

	  // The upper bound is not a complex expression
	  if (uniqp) {
	    string_buffer_append_symbolic(int2a(1),buffer_pattern);
	    string_buffer_append_numeric(int2a(1),buffer_pattern);
	  }
	  else {
	    if (vpattern != VECTEUR_NUL) {
	      if (mult==1)
		string_buffer_append_symbolic(vect_to_string(vpattern),buffer_pattern);
	      else {
		add_margin(global_margin,buffer_pattern);
		string_buffer_append(buffer_pattern,
				     concatenate(OPENANGLE,"Symbolic",CLOSEANGLE,
						 "(",NULL));
		string_buffer_append_xml_text(buffer_pattern,vect_to_string(vpattern),false);
		string_buffer_append(buffer_pattern,
				     concatenate(")",
						 "/",i2a(mult),"+1",
						 OPENANGLE,"/Symbolic",CLOSEANGLE,
						 NL, NULL));
	      }
	      
	    }
	    else //vpattern == VECTEUR_NUL
	      two_string_buffer_append_symbolic(expression_to_string(dimension_upper(vreg_dim)), "+1",
						buffer_pattern);
	    if ((vpattern != VECTEUR_NUL) && vect_dimension(vpattern)==0)
	      string_buffer_append_numeric(vect_to_string(vpattern),
					   buffer_pattern);
	  }
	  string_buffer_append_word("/Length",buffer_pattern);

	  string_buffer_append_word("Stride",buffer_pattern);
	  val =1;
	  string_buffer_append_symbolic(int2a(val),buffer_pattern);
	  string_buffer_append_numeric(int2a(val),buffer_pattern);
	  string_buffer_append_word("/Stride",buffer_pattern);
	  global_margin--;
	  string_buffer_append_word("/DimPattern",buffer_pattern);
	}
	if (!VECTEUR_UNDEFINED_P(iterator) &&!VECTEUR_NUL_P(iterator)) {
	  string_buffer_append_word("DimPavage",buffer_paving);
	  for (iterat = paving_indices; !VECTEUR_NUL_P(iterat); iterat = iterat->succ) {
	    if ((inc = vect_coeff(var_of(iterat),iterator)) !=0) {
	      add_margin(global_margin,buffer_paving);
	      string_buffer_append(buffer_paving,
				   concatenate(OPENANGLE,
					       "RefLoopIndex Name=",
					       QUOTE,entity_user_name(var_of(iterat)),QUOTE, BL,
					       "Inc=", QUOTE,
					       int2a(inc),QUOTE,"/", CLOSEANGLE,NL,NULL));
	    }
	  }
	  string_buffer_append_word("/DimPavage",buffer_paving);
	}
	else
	  string_buffer_append_word("DimPavage/",buffer_paving);
      }
      global_margin--;
      string_buffer_append_word("/Pattern",buffer_pattern);
      string_buffer_append_word("/Pavage",buffer_paving);
      string_pattern = string_buffer_to_string(buffer_pattern);
      string_paving = string_buffer_to_string(buffer_paving);
      string_buffer_append(sb_result, string_pattern);
      free(string_pattern);
      string_pattern=NULL;
      string_buffer_append(sb_result, string_paving);
      free(string_paving);
      string_paving=NULL;
      xml_AccessFunction(sb_result);
      sc_free(ps_reg);
    }
  }
}

/* UNUSED
static void array_vars_read_or_written(list effects_list, Pvecteur *vl)
{
  Pvecteur vin=VECTEUR_NUL;
  Pvecteur vout = VECTEUR_NUL;
  list pc;
  for (pc= effects_list;pc != NIL; pc = CDR(pc)){
    effect e = EFFECT(CAR(pc));
    reference r = effect_any_reference(e);
    if (store_effect_p(e) && array_entity_p(reference_variable(r))) {
      entity v = reference_variable(r);
      if (effect_read_p(e))
	vect_add_elem(&vin,v,1);
      else  vect_add_elem(&vout,v,1);
    }
  }
  vin = base_normalize(vin);
  vout = base_normalize(vout);
  *vl = vect_substract(vin,vout);
  *vl= base_normalize(*vl);
  vect_rm(vin);
  vect_rm(vout);
}
*/

static void vars_read_and_written(list effects_list, Pvecteur *vr, Pvecteur *vw)
{
  list pc;
  for (pc= effects_list;pc != NIL; pc = CDR(pc)){
    effect e = EFFECT(CAR(pc));
    if (e!=(effect) 0 && effect_cell(e)!=0 && !effect_undefined_p(e)  && store_effect_p(e)) {
      reference r = effect_any_reference(e);
      entity v = reference_variable(r);
      if (effect_read_p(e))
	vect_add_elem(vr,v,1);
      else  vect_add_elem(vw,v,1);
    }
  }
  *vr = base_normalize(*vr);
  *vw = base_normalize(*vw);
}

static void  xml_Region_Range(region reg, string_buffer sb_result)
{
  Variable phi;
  int i;
  Pcontrainte pc;
  if(reg != region_undefined) {
    reference ref = effect_any_reference(reg);
    entity vreg = reference_variable(ref);
    if (array_entity_p(reference_variable(ref))) {
      int dim = (int) gen_length(variable_dimensions(type_variable(entity_type(vreg))));
      Psysteme ps_reg = sc_dup(region_system(reg));
      /* on peut ameliorer les resultats en projetant
	 les egalites portant sur les variables autres que les PHI */
      /*
	Pvecteur vva = VECTEUR_NUL;
	Variable va;
	for(pc = sc_egalites(ps_reg); pc!=NULL;pc= pc->succ)
	{
	va = vect_one_coeff_if_any(pc->vecteur);
	if (va!= NULL && strcmp(variable_name(va),"PHI")==0 ) vect_add_elem(&vva,va,1);
	}
	sc_projection_along_variables_ofl_ctrl(&ps_reg,vva , NO_OFL_CTRL);
      */
      if (!SC_UNDEFINED_P(ps_reg)) {
	sc_transform_eg_in_ineg(ps_reg);
	for (i=1;i<=dim;i++) {
	  string_buffer sbi_result=string_buffer_make(true);
	  string_buffer sbu_result=string_buffer_make(true);
	  string string_sbi, string_sbu;
	  int fub = 0;
	  int fib = 0;
	  phi = (Variable) make_phi_entity(i);
	  string_buffer_append(sbi_result,
			       concatenate("[", NULL));
	  string_buffer_append(sbu_result,
			       concatenate(";",NULL));
	  for(pc = sc_inegalites(ps_reg); pc!=NULL;pc= pc->succ)
	    {
	      int vc = vect_coeff(phi, pc->vecteur);
	      Pvecteur vvc = vect_dup(pc->vecteur);
	      string sb= NULL;
	      string scst;
	      if (value_pos_p(vc)) { // borne sup
		vect_erase_var(&vvc,phi);
		vect_chg_sgn(vvc);
		sb = vect_to_string(vvc);
		if (vc-1)
		  scst =strdup(i2a(vc));
		if (fub++)
		  if  (vc-1)
		    string_buffer_append(sbu_result,
					 concatenate(",(",sb, NULL));
		  else  string_buffer_append(sbu_result,
					     concatenate(",",sb, NULL));
		else
		  if  (vc-1)
		    string_buffer_append(sbu_result,
					 concatenate("(",sb, NULL));
		  else string_buffer_append(sbu_result,
					    concatenate(sb, NULL));
		if (vc-1)
		  string_buffer_append(sbu_result,
				       concatenate(")/",scst, NULL));
	      }
	      else if (value_neg_p(vc)) {
		vect_erase_var(&vvc,phi);
		sb = vect_to_string(vvc);
		if (vc+1) scst =strdup(i2a(-1*vc));
		if (fib++)
		  if (vc+1)
		    string_buffer_append(sbi_result,
					 concatenate(",(",sb, NULL));
		  else string_buffer_append(sbi_result,
					    concatenate(",",sb, NULL));
		else
		  if (vc+1)
		    string_buffer_append(sbi_result,
					 concatenate("(",sb, NULL));
		  else   string_buffer_append(sbi_result,
					      concatenate(sb, NULL));
		if (vc+1)
		  string_buffer_append(sbi_result,
				       concatenate(")/",scst, NULL));
	      }
	    }
	  string_buffer_append(sbu_result,
			       concatenate("]",NULL));
	  string_sbi = string_buffer_to_string(sbi_result);
	  string_sbu = string_buffer_to_string(sbu_result);
	  string_buffer_append(sb_result,string_sbi);
	  string_buffer_append(sb_result,string_sbu);
	}
	sc_rm(ps_reg);
      }
    }
  }
}

/*static bool string_in_list_p(string ts,list lr){
  bool trouve=false;
  MAPL(tt,
       {trouve= trouve || strcmp(STRING(CAR(tt)),ts) == 0;},
       lr);
  return trouve;
}
*/

static bool  region_range_nul_p(region reg,Variable phi)
{
  Pcontrainte pc;
  bool result=false;
  if(reg != region_undefined) {
    reference ref = effect_any_reference(reg);
    entity vreg = reference_variable(ref);
    if (array_entity_p(reference_variable(ref))) {
      if (gen_length(variable_dimensions(type_variable(entity_type(vreg)))) ==1) {
	Psysteme ps_reg = sc_dup(region_system(reg));
	if (!SC_UNDEFINED_P(ps_reg)) {
	  for(pc = sc_egalites(ps_reg); pc!=NULL;pc= pc->succ)  {
	    if (vect_coeff(phi, pc->vecteur) && (vect_size(pc->vecteur)==1 ))
	      result=true;
	  }
	}
      }
    }
  }
  return result;
}


char *str_sub (const char *s, int start, int end)
{
   char *new_s = NULL;
   if (s != NULL && start <= end)
   {
      new_s = malloc (sizeof (*new_s) * (end - start + 2));
      if (new_s != NULL) {
         int i;
         for (i = start; i <= end; i++) {
            new_s[i-start] = s[i];
         }
         new_s[i-start] = '\0';
      }
   }
   return new_s;
}

char * pointer_to_initial_name(char *ts, _UNUSED_ char * ste)
{
  string ts_tmp = ts;
  string initial_ts =ts;
  /* Prefix extraction
  int nbpref= strcspn(ste, ts);
  string pref_ts= malloc (sizeof (char) * (nbpref+1));
  pref_ts = strncpy(pref_ts,ste,(int)nbpref);
  pref_ts[nbpref]='\0';
  fprintf(stdout,"Prefix for %s in %s is %s\n",ts, ste,pref_ts );
  */
  bool reduction_p=true;
  // Remove "_" on either side of intial entity name ts in case of pointer
  while (reduction_p && strchr(ts_tmp,'_')==ts_tmp)
    {
      string end_ts=strrchr(ts,'_');
      if (strlen(ts_tmp)-strlen(end_ts)-1>0)
	initial_ts = str_sub (ts,1,strlen(ts_tmp)-strlen(end_ts)-1);
      else reduction_p=false;
      ts_tmp=initial_ts;
    }

  /* Search entity to determine its type
  string newst = malloc (sizeof (char) * (nbpref+strlen(initial_ts)));
  newst = strcat(pref_ts,initial_ts); 
  entity newent=gen_find_entity(newst);
  */
   return(initial_ts);
}

static const char * words_points_to_reference(reference rv, bool suffix_only_p, region reg)
{
  list pc = NIL;
  list pc1=NIL;
  int i;
  bool bp=false;
  entity vv = reference_variable(rv);
  type ct = entity_basic_concrete_type(vv);
  list lr=reference_indices(rv);

  if (!suffix_only_p)  {
    // Translate temporary constant entity name into user entity name
    string full_name= (string) entity_user_name(vv);
    string initial_name = pointer_to_initial_name(full_name,(string)entity_name(vv));
    pc = CHAIN_SWORD(pc, initial_name);
  }
  while(lr != NIL) {
    switch (type_tag(ct)) {
    case is_type_variable: {

      variable vt = type_variable(ct);
      basic bt = variable_basic(vt);
      list lt = variable_dimensions(vt);

      if (array_type_p(ct)) {
	expression ll = EXPRESSION(CAR(lr));
	entity re=entity_undefined;
	if (syntax_reference_p(expression_syntax(ll)))
	  re=reference_variable(syntax_reference(expression_syntax(ll)));
	if (gen_length(lt) ==1 && !region_undefined_p(reg) && !entity_undefined_p(re) && region_range_nul_p(reg,(Variable)re)) {
	  if (CDR(lr)!=NIL)  {
	    pc = CHAIN_SWORD(pc,"->");
	    bp=true;
	  }
	  else {
	    pc1=NIL;
	    pc1 = CHAIN_SWORD(pc1,"*");
	    gen_nconc(pc1,pc);
	    pc=pc1;
	  }
	  lr=CDR(lr);
	}
	else {
	  for (i= 1; i<= (int) gen_length(lt) && lr!=NIL; i++) {
	    pc = CHAIN_SWORD(pc,"[*]");
	    lr=CDR(lr);
	  }
	}
      }

      if (lr!=NIL) {
	if(basic_typedef_p(bt)) {
	  entity e = basic_typedef(bt);
	  ct= compute_basic_concrete_type(entity_type(e));
	}
	else if(basic_pointer_p(bt)) {
	  pc = CHAIN_SWORD(pc, "->");
	  lr=CDR(lr); // equivalent to [0]
	  ct = compute_basic_concrete_type(basic_pointer(bt));
	  bp=true;
	}
	else if(basic_derived_p(bt)) {
	  ct = compute_basic_concrete_type(entity_type(basic_derived(bt)));
	}
	else  { // int, float, logical, overload, complex, string, bit ==> nothing to do
	  if (lr ==NIL)
	    printf(" additional basic type, PB \n");
	  else {
	    lr=CDR(lr);
	  }
	}
      }
      break;
    }

    case is_type_struct: {
      if (!bp) pc = CHAIN_SWORD(pc, ".");
      bp=false;
      list fe = type_struct(ct); // list of type entities in struct
      expression exp= EXPRESSION(CAR(lr));
      syntax se = expression_syntax(exp);
      if (syntax_reference_p(se)) {
	entity re=reference_variable(syntax_reference(se));
	FOREACH(ENTITY, fee, fe){
	  if (same_entity_p(fee,re))
	    ct = compute_basic_concrete_type(entity_type(fee));
	}
	pc = CHAIN_SWORD(pc,expression_to_string(exp));
	lr = CDR(lr);
      }
      else printf("pb avec le STRUCT\n");
      break;
    }
    case is_type_union: {
      if (!bp) pc = CHAIN_SWORD(pc, ".");
      bp=false;
      list fe = type_union(ct); // list of type entities in union
      expression exp= EXPRESSION(CAR(lr));
      syntax se = expression_syntax(exp);
      if (syntax_reference_p(se)) {
	entity re=reference_variable(syntax_reference(se));
	FOREACH(ENTITY, fee, fe){
	  if (same_entity_p(fee,re))
	    ct = compute_basic_concrete_type(entity_type(fee));
	}
	pc = CHAIN_SWORD(pc, "{");
	pc = CHAIN_SWORD(pc,expression_to_string(exp));
	pc = CHAIN_SWORD(pc, "}");
	lr = CDR(lr);
      }
      else printf("pb avec le UNION\n");
      break;
    }
    case is_type_enum: {
      if (!bp) pc = CHAIN_SWORD(pc, ".");
      bp=false;
      list fe = type_enum(ct); // list of type entities in union
      expression exp= EXPRESSION(CAR(lr));
      syntax se = expression_syntax(exp);
      if (syntax_reference_p(se)) {
	entity re=reference_variable(syntax_reference(se));
	FOREACH(ENTITY, fee, fe){
	  if (same_entity_p(fee,re))
	    ct = compute_basic_concrete_type(entity_type(fee));
	}
	pc = CHAIN_SWORD(pc, "{");
	pc = CHAIN_SWORD(pc,expression_to_string(exp));
	pc = CHAIN_SWORD(pc, "}");
	lr = CDR(lr);
      }
      else printf("pb avec le ENUM\n");
      break;
    }
    default: // void(not here), unknown(not here), varargs (to be added?), functional (not here), statement(not here), area (not here)
      {
	printf("Not implemented\n");
	pc = CHAIN_SWORD(pc, expression_to_string(EXPRESSION(CAR(lr))));
	lr = CDR(lr);
      }
    }
  }
  return(strdup(list_to_string(pc)));
}



static void xml_Full_Type(type pt, int max_step, string_buffer type_result)
{
  if (max_step>=0) {
    switch (type_tag(pt)) {
    case is_type_variable: {
      variable vt1 = type_variable(pt);
      basic bt1 = variable_basic(vt1);
      list lt1 = variable_dimensions(vt1);
      //DEBUG- if ((int)gen_length(lt1)>0) 	printf("ARRAY_DIMENSION= %d ", (int)gen_length(lt1));

      global_margin++;

      if ((int)gen_length(lt1)>0) {
        add_margin(global_margin,type_result);
        string_buffer_append(type_result,
			     concatenate(OPENANGLE,
					 "ArrayType Dimension = ",QUOTE,i2a((int)gen_length(lt1)),QUOTE,
					 CLOSEANGLE,NL,NULL));
      }
      if(basic_typedef_p(bt1)) {
        entity e1 = basic_typedef(bt1);
        //DEBUG- printf("TYPEDEF %s \n",basic_to_string(bt1));
        add_margin(global_margin,type_result);
        string_buffer_append(type_result,
			     concatenate(OPENANGLE,
					 "Typedef Name= ",QUOTE,basic_to_string(bt1),QUOTE,CLOSEANGLE,NL,NULL));
        xml_Full_Type(entity_type(e1),max_step-1,type_result);
        string_buffer_append_word("/Typedef",type_result);
      }
      else if(basic_pointer_p(bt1)) {
        type pt1 = basic_pointer(bt1);
        //DEBUG- printf("POINTER %s\n",basic_to_string(bt1));
        add_margin(global_margin,type_result);
        string_buffer_append(type_result, concatenate(
          OPENANGLE, "Pointer Name = ", QUOTE, basic_to_string(bt1), QUOTE,
          CLOSEANGLE,NL,NULL));
        xml_Full_Type(pt1,max_step-1,type_result);
        string_buffer_append_word("/Pointer",type_result);
      }
      else if(basic_derived_p(bt1)) {
        entity e1 = basic_derived(bt1);
        //DEBUG- printf("DERIVED  %s \n", basic_to_string(bt1));
        add_margin(global_margin,type_result);
        string_buffer_append(type_result, concatenate(OPENANGLE,
					 "Derived Name= ",QUOTE,basic_to_string(bt1),QUOTE,CLOSEANGLE,NL, NULL));
        xml_Full_Type(entity_type(e1),max_step-1,type_result);
        string_buffer_append_word("/Derived",type_result);
      }
      else  { // int, float, logical, overload, complex, string, bit ==> nothing to do
	add_margin(global_margin,type_result);
	string_buffer_append(type_result,
			     concatenate(OPENANGLE,"Basic",CLOSEANGLE,
					 basic_to_string(bt1),
					 OPENANGLE,"/Basic",CLOSEANGLE,NL, NULL));
	//DEBUG- printf("BASIC  %s \n", basic_to_string(bt1));
      }
      if ((int)gen_length(lt1)>0)
	string_buffer_append_word("/ArrayType",type_result);
      global_margin--;
      break;
    }

    case is_type_struct: {
      list fe1 = type_struct(pt);
      global_margin++;
      string_buffer_append_word("Struct",type_result);
      FOREACH(ENTITY, fee1, fe1){
        global_margin++;
        //DEBUG- printf("field %s \n",entity_user_name(fee1));
        add_margin(global_margin,type_result);
        string_buffer_append(type_result, concatenate(
          OPENANGLE, "Field Name= ",QUOTE,entity_user_name(fee1),QUOTE,BL,
          CLOSEANGLE,NL,NULL));
        xml_Full_Type(entity_type(fee1),max_step-1,type_result);
        string_buffer_append_word("/Field",type_result);
        global_margin--;
      }
      string_buffer_append_word("/Struct",type_result);
      global_margin--;
      break;
    }
    case is_type_union: {
      list fe1 = type_union(pt);
      global_margin++;
      string_buffer_append_word("Union",type_result);
      FOREACH(ENTITY, fee1, fe1){
	global_margin++;
	//DEBUG- printf("field %s \n",entity_user_name(fee1));
	add_margin(global_margin,type_result);
	string_buffer_append(type_result,
			     concatenate(OPENANGLE,"Field Name= ",QUOTE,entity_user_name(fee1),QUOTE,BL,CLOSEANGLE,NL,NULL));
	xml_Full_Type(entity_type(fee1),max_step-1,type_result);
	string_buffer_append_word("/Field",type_result);
	global_margin--;
      }
      string_buffer_append_word("/Union",type_result);
      global_margin--;
      break;
    }
    case is_type_enum: {
      list fe1 = type_enum(pt);
      global_margin++;
      string_buffer_append_word("Enum",type_result);
      FOREACH(ENTITY, fee1, fe1){
        global_margin++;
        //DEBUG- printf("field %s \n",entity_user_name(fee1));
        add_margin(global_margin,type_result);
        string_buffer_append(type_result,
			     concatenate(OPENANGLE,"Field Name= ",QUOTE,entity_user_name(fee1),QUOTE,BL,CLOSEANGLE,NL,NULL));
        xml_Full_Type(entity_type(fee1),max_step-1,type_result);
        string_buffer_append_word("/Field",type_result);
        global_margin--;
      }
      string_buffer_append_word("/Enum",type_result);
      global_margin--;
      break;
    }
    default: // void(not here), unknown(not here), varargs (to be added?), functional (not here), statement(not here), area (not here)
      {	 //printf("Not implemented\n");
        max_step=-1;
      }
      return;
    }
  }
}

static void xml_Type_Entity(entity vv,string_buffer type_buffer)
{
  int max_step = (int) maximal_type_depth(entity_type(vv));
  if (max_step <=30) {
    // if (!io_entity_p(vv) && !ENTITY_STDOUT_P(vv) && !ENTITY_STDIN_P(vv) && !ENTITY_STDERR_P(vv)) {
    if (!effects_package_entity_p(vv) && !std_file_entity_p(vv) && !variable_heap_p(vv)) {
      type ct = entity_type(vv);
      global_margin++;
      add_margin(global_margin,type_buffer);
      string_buffer_append(type_buffer,
			   concatenate(OPENANGLE,
				       "Reference Name= ",QUOTE,NULL));
      string_buffer_append_xml_text(type_buffer, (string) entity_user_name(vv),false);
      string_buffer_append(type_buffer, concatenate(QUOTE,CLOSEANGLE,NL,NULL));
      xml_Full_Type(ct,max_step,type_buffer);
     string_buffer_append_word("/Reference",type_buffer);
      global_margin--;
    }
  }
}

static void xml_Region_Parameter(list pattern_region, string_buffer sb_result)
{
  list lr;
  list lrr = NIL, lrw=NIL;
  bool effet_read = true;
  reference ref;
  region reg;
  entity v;

  string_buffer_append_word("ReferencedParameters",sb_result);
  global_margin++;

  for ( lr = pattern_region; !ENDP(lr); lr = CDR(lr))
    {
      reg = REGION(CAR(lr));
      ref = effect_any_reference(reg);
      v = reference_variable(ref);
      if (store_effect_p(reg) && array_entity_p(reference_variable(ref)) && !variable_heap_p(v)
	  && !(entity_static_variable_p(v) && !top_level_entity_p(v))) {
	string ts = strdup(entity_user_name(v));
	
	//	string temp2 = pointer_to_initial_name(ts);
	 
	effet_read = region_read_p(reg);
	//	if ((effet_read && !string_in_list_p(ts,lrr)) || (!effet_read && !string_in_list_p(ts,lrw))) {
	  if (effet_read)
	    lrr = gen_nconc(lrr,CONS(STRING,ts,NIL));
	  else lrw = gen_nconc(lrw,CONS(STRING,ts,NIL));
	  add_margin(global_margin,sb_result);
	  string_buffer_append(sb_result,
			       concatenate(OPENANGLE,
					   "ReferencedParameter"," Name=",
					   QUOTE,NULL));
	  string_buffer_append_xml_text(sb_result,
					(string)((print_full_name_p() || reference_undefined_p(ref))? entity_user_name(v):words_points_to_reference(ref,false,reg)),
					false);
	  string_buffer_append(sb_result,
			       concatenate(QUOTE, BL,"Range=",QUOTE,NULL));
	  xml_Region_Range(reg, sb_result);

	  string_buffer_append(sb_result,
			       concatenate(QUOTE, BL,
					   "Type=", QUOTE,(entity_xml_parameter_p(v))? "CONTROL":"DATA",QUOTE,BL,
					   "AccessMode=", QUOTE, (effet_read)? "USE":"DEF",QUOTE,BL,
					   "ArrayP=", QUOTE, (array_entity_p(v))?"TRUE":"FALSE",QUOTE, BL,
					   "Kind=", QUOTE,  "VARIABLE",QUOTE,"/",
					   CLOSEANGLE
					   NL, NULL));
	 
	  //	}
      }
    }
  global_margin--;
  string_buffer_append_word("/ReferencedParameters",sb_result);
  gen_free_list(lrr);
  gen_free_list(lrw);
}

static int find_effect_actions_for_entity(
  list leff, effect *effr, effect *effw, entity e)
{
  // return effet_rwb = 1 for Read, 2 for Write, 3 for Read/Write
  int effet_rwb=0;
  list lr = NIL;
  bool er = false;
  bool ew = false;
  //fprintf(stdout,"DEBUG - Effects for var =%s\n",entity_user_name(e));
  //print_effects(leff);
  for ( lr = leff; !ENDP(lr); lr = CDR(lr)) {
    effect eff=  EFFECT(CAR(lr));
    reference ref = effect_any_reference(eff);
    entity v = reference_variable(ref);
    if (store_effect_p(eff) && same_entity_p(v,e) && !environment_effect_p(eff)) {
      if (action_read_p(effect_action(eff)))
	er = true, *effr =eff;
      else ew = true, *effw=eff;
    }
  }
  effet_rwb = (er?1:0) +(ew?2:0);
  return (effet_rwb);
}

static void same_entities(reference r, expression_ctxt *ctxt)
{
  if (same_entity_p(reference_variable(r),ctxt->e))
    ctxt->entity_in_p = true;
}

static bool entity_in_expression_p(expression exp,entity e)
{

  expression_ctxt ctxt = { e, false };
  gen_context_recurse(exp, &ctxt, reference_domain, gen_true2, same_entities);
  return ctxt.entity_in_p;
}

static void xml_ParameterUseToArrayBound(entity var, string_buffer sb_result)
{
  string sdim;
  entity FormalArrayName, mod = get_current_module_entity();
  int ith, FormalParameterNumber = (int) gen_length(module_formal_parameters(mod));
  global_margin++;
  for (ith=1;ith<=FormalParameterNumber;ith++) {
    FormalArrayName = find_ith_formal_parameter(mod,ith);
    if (type_variable_p(entity_type(FormalArrayName))
	&& ( variable_entity_dimension(FormalArrayName)>0)) {
      list ld, ldim = variable_dimensions(type_variable(entity_type(FormalArrayName)));
      int dim;
      for (ld = ldim, dim =1 ; !ENDP(ld); ld = CDR(ld), dim++) {
	expression elow = dimension_lower(DIMENSION(CAR(ld)));
	expression eup = dimension_upper(DIMENSION(CAR(ld)));
	//const char * low= words_to_string(words_syntax(expression_syntax(elow),NIL));
	//const char * up = words_to_string(words_syntax(expression_syntax(eup),NIL));
	//const char * sv = entity_local_name(var);
	//if ((strstr(low,sv)!=NULL) || (strstr(up,sv)!=NULL)) {
	if (entity_in_expression_p(elow,var) || entity_in_expression_p(eup,var)) {
	  sdim= strdup(i2a(variable_entity_dimension(FormalArrayName)-dim+1));
	  add_margin(global_margin,sb_result);
	  string_buffer_append(sb_result,
			       concatenate(OPENANGLE,
					   "TaskParameterUsedFor"," ArrayName=", QUOTE, NULL));
	  string_buffer_append_xml_text(sb_result, (string) entity_user_name(FormalArrayName),false);
	  string_buffer_append(sb_result,
			       concatenate(QUOTE, BL,
					   //QUOTE,words_points_to_reference(FormalArrayName),QUOTE, BL,
					   "Dim=", QUOTE,sdim,QUOTE,"/", CLOSEANGLE, NL, NULL));
	}
      }
    }
  }
  global_margin--;
}


typedef struct callst
{
  entity  func;
  int stat_nb;
  struct callst *succ;
} callst, *Pcallst;

static bool same_callst_p(Pcallst c1,Pcallst c2)
{
  return(same_entity_p(c1->func,c2->func) && (c1->stat_nb ==c2->stat_nb));
}

static void update_def_into_tasks_table(entity v, Pcallst c1)
{
  Pcallst ll= NULL,lc2;
  bool found=false;
  Pcallst ldef = (Pcallst) hash_get(hash_entity_def_into_tasks,(char *) v);
  if (ldef != (Pcallst) HASH_UNDEFINED_VALUE) {
    for(lc2=ldef;lc2 !=(Pcallst) HASH_UNDEFINED_VALUE && lc2 !=(Pcallst) NULL && !found; lc2=lc2->succ)
      {
	if (same_callst_p(c1,lc2))
	  found=true;
      }
    if (!found)
      c1->succ=ldef, ll=c1;
    else ll =ldef;
  }
  else ll=c1;
  hash_del(hash_entity_def_into_tasks,(char *) v);
  hash_put(hash_entity_def_into_tasks,(char *) v,(char *)ll);
}
static void add_def_into_tasks_table(entity v, Pcallst c1)
{
  Pcallst ldef = (Pcallst) hash_get(hash_entity_def_into_tasks,(char *) v);
  if (ldef == (Pcallst) HASH_UNDEFINED_VALUE) {
    hash_put(hash_entity_def_into_tasks,(char *) v,(char *)c1);
  }
}

static void xml_TaskReturnParameter(entity function, _UNUSED_ int statnb, string_buffer sb_result)
{
  const char* datatype ="";

  if (type_functional_p(entity_type(function))) {
    type tp=functional_result(type_functional(entity_type(function)));
    if (type_variable_p(tp)) {
      variable v=type_variable(tp);
      basic b = variable_basic(v);
      //int e = SizeOfElements(b);
      // int size = (e==-1) ? 9999:e;
      datatype =basic_to_string(b);

      add_margin(global_margin,sb_result);
      string_buffer_append(sb_result,
			   concatenate(OPENANGLE,
				       "AssignParameter",
				       " Name= ",QUOTE, "RETURN",QUOTE,BL,
				       "DataType=",QUOTE,datatype,QUOTE,BL,
				       "AccessMode=", QUOTE,"DEF",QUOTE,BL,
				       "ArrayP=", QUOTE, (variable_dimensions(v) != NIL)?"TRUE":"FALSE",QUOTE, BL,
				       "Kind=", QUOTE,  "VARIABLE",QUOTE,
				       CLOSEANGLE,
				       NL, NULL));
      string_buffer_append_word("/AssignParameter",sb_result);

    }
  }
}


static void xml_TaskParameter(bool assign_function, _UNUSED_ entity function, int statnb, bool is_not_main_p, entity var, Pvecteur formal_parameters, list pattern_region, Pvecteur paving_indices, string_buffer sb_result, string_buffer buffer_assign)
{
  bool effet_read = true;
  region rwr = region_undefined;
  region rre = region_undefined;
  const char* datatype ="";
  int size=0, rw_ef=0, prems=0;
  reference ref = reference_undefined;
  region reg = region_undefined;
  entity v = entity_undefined;
  list pc = list_undefined;
  bool  pavp=true, RW_effet=false;

  // rappel : les regions contiennent les effects sur les scalaires
  // - Pour les fonctions, on ecrit les parametres formels dans l'ordre.
  // - Pour le MAIN, ordre des regions:
  if (assign_function){
    reg = REGION(CAR(pattern_region));
    ref = effect_any_reference(reg);
    v = reference_variable(ref);
    pavp = true;
    effet_read = region_read_p(reg);
    rw_ef=(!effet_read)?2:1;
  }
  else {
    if  (!is_not_main_p) {
      reg = REGION(CAR(pattern_region));
      ref = effect_any_reference(reg);
      v = reference_variable(ref);
      pavp =(vect_coeff(v,paving_indices) == 0);
      effet_read = region_read_p(reg);
    }
    else { // c'est une fonction -->  impression selon l'ordre des parametres formels
      // recherche des regions du parametre formel
      rw_ef= find_effect_actions_for_entity(pattern_region,&rre, &rwr,var);
      // choix de l'affichage des regions write en premier lorsque R&W existent
      if (rwr != region_undefined)
	reg=rwr, effet_read=false;
      else reg= rre, effet_read=true;
      if (reg != region_undefined) {
	ref = effect_any_reference(reg);
	v = reference_variable(ref);
      }
      else  // cas ou il n'y a pas d'effet sur le parametre formel,
	//  mais il fait partie de la liste des parametres de la fonction
	v = var, effet_read = true;

      // La liste des effects de la fonction a ete completee dans le TaskParameters
      // On recherche le premier effect sur la variable pour en deduire l'info Use OU Def dans la fonction
      if((rw_ef>=3) && (int)gen_length(cumulated_list) >0) {
	for (pc= cumulated_list;pc != NIL && prems ==0; pc = CDR(pc)){
	  effect e = EFFECT(CAR(pc));
	  reference r = effect_any_reference(e);
	  if (store_effect_p(e) && array_entity_p(reference_variable(r)) && (same_entity_p(v,reference_variable(r))) ) {
	    prems=(effect_read_p(e)) ? 1:2;
	  }
	}
	//  printf("DEBUG - DEF_USE detection %s \n",(prems)? ((prems==1)?"USE":"DEF"):"Erreur pas d'effets sur cette variable");
      }
    }
  }

  RW_effet=((!is_not_main_p || assign_function) && !effet_read) || (is_not_main_p && (rw_ef==2 || prems==2));
  if (pavp) {
    type_and_size_of_var(v, &datatype,&size);

    if (assign_function && RW_effet && same_entity_p(var,v)) {
      add_margin(global_margin,buffer_assign);
      string_buffer_append(buffer_assign,
			   concatenate(OPENANGLE,
				       "AssignParameter"," Name=",
				       QUOTE, NULL));
      string_buffer_append_xml_text(buffer_assign,
				    (string) ((print_full_name_p() || reference_undefined_p(ref)) ?
							    entity_user_name(v):words_points_to_reference(ref, false,region_undefined)),
				    false);
      string_buffer_append(buffer_assign,
			   concatenate(QUOTE, BL,
				        "Type=", QUOTE,(entity_xml_parameter_p(v))? "CONTROL":"DATA",QUOTE,BL,
				       "DataType=",QUOTE,datatype,QUOTE,BL,
				       "AccessMode=", QUOTE, RW_effet ? "DEF":"USE",QUOTE,BL,
				       "ArrayP=", QUOTE, (array_entity_p(v))?"TRUE":"FALSE",QUOTE, BL,
				       "Kind=", QUOTE,  "VARIABLE",QUOTE,
				       CLOSEANGLE,
				       NL, NULL));

      global_margin++;
      xml_Pattern_Paving(reg,v, effet_read, formal_parameters,
			 paving_indices, buffer_assign);
      if (rw_ef>=3)
	xml_Pattern_Paving(rre,v, true, formal_parameters,
			   paving_indices, buffer_assign);
      global_margin--;
      string_buffer_append_word("/AssignParameter",buffer_assign);

    }
    else {
      add_margin(global_margin,sb_result);
      string_buffer_append(sb_result,
			   concatenate(OPENANGLE,
				       "TaskParameter",
				       // " Name=", QUOTE,entity_user_name(v),QUOTE, BL,
				       " Name=", QUOTE, NULL));
      // For the task/function parameter, only one region is taken to represent all the struct fields if any.
      string_buffer_append_xml_text(sb_result,
				    (string) ((print_full_name_p() || reference_undefined_p(ref) || is_not_main_p)?
					      entity_user_name(v):words_points_to_reference(ref,false,region_undefined)),
				    false);
      string_buffer_append(sb_result,
			   concatenate(QUOTE, BL,
				       "Type=", QUOTE,(entity_xml_parameter_p(v))? "CONTROL":"DATA",QUOTE,BL,
				       "DataType=",QUOTE,datatype,QUOTE,BL,
				       "AccessMode=", QUOTE, RW_effet ? "DEF":"USE",QUOTE,BL,
				       "ArrayP=", QUOTE, (array_entity_p(v))?"TRUE":"FALSE",QUOTE, BL,
				       "Kind=", QUOTE,  "VARIABLE",QUOTE,
				       CLOSEANGLE,
				       NL, NULL));
      xml_ParameterUseToArrayBound(var,sb_result);
      global_margin++;
      xml_Pattern_Paving(reg,v, effet_read, formal_parameters,
			 paving_indices, sb_result);
      if (rw_ef>=3)
	xml_Pattern_Paving(rre,v, true, formal_parameters,
			   paving_indices, sb_result);
      global_margin--;
      string_buffer_append_word("/TaskParameter",sb_result);
    }
    if (assign_function && rw_ef>=2 && statnb>0) {
      Pcallst cst1=(callst *) malloc(sizeof(callst));
      entity assign_ent = gen_find_tabulated(make_entity_fullname(TOP_LEVEL_MODULE_NAME,
								  ASSIGN_OPERATOR_NAME),
					     entity_domain);
      cst1->func = assign_ent;
      cst1->stat_nb= statnb;
      cst1->succ = (Pcallst)NULL;
      update_def_into_tasks_table(v ,cst1);
    }
  }
}

static void cumul_and_update_effects_of_statement(statement s) {
  list l = load_proper_rw_effects_list(s);
  if (!ENDP(l) && !list_undefined_p(l)) {
    cumulated_list = gen_append(cumulated_list, l);

    for (list pc = l; pc != NIL; pc = CDR(pc)) {
      effect e = EFFECT(CAR(pc));
      reference r = effect_any_reference(e);
      action ac = effect_action(e);
      entity v = reference_variable(r);
      if (store_effect_p(e)
	  && !effects_package_entity_p(v) && !std_file_entity_p(v) //&& !variable_heap_p(v)
	  && action_write_p(ac) &&
          !(entity_static_variable_p(v) && !top_level_entity_p(v))) {
        {
          Pcallst cst1 = (callst *)malloc(sizeof(callst));
          cst1->func = entity_undefined;
          cst1->stat_nb = statement_number(s);
          cst1->succ = (Pcallst)NULL;
          add_def_into_tasks_table(v, cst1);
        }
      }
    }
  }
}

static void cumul_effects_of_statement(statement s)
{
  list l=load_proper_rw_effects_list(s);
  if (!ENDP(l) && !list_undefined_p(l))
    cumulated_list = gen_append(cumulated_list,l);

}

static void xml_TaskParameters(statement stat, bool assign_function, int code_tag, entity module, list pattern_region, Pvecteur paving_indices, string_buffer sb_result)
{
  string_buffer buffer_assign = string_buffer_make(true);
  string string_temp = "";
  list lr=NIL;
  call c=call_undefined;
  int ith;
  entity FormalName = entity_undefined;
  Pvecteur formal_parameters = VECTEUR_NUL;
  int FormalParameterNumber = (int) gen_length(module_formal_parameters(module));

  string_buffer_append_word("TaskParameters",sb_result);
  global_margin++;

  if (assign_function){
    if (instruction_call_p(statement_instruction(stat))) {
      c = instruction_call(statement_instruction(stat));
    }
    else {
      encapsulated_call =call_undefined;
      gen_recurse(stat, call_domain, gen_true,search_1r_function_call);
      c =encapsulated_call;
    }
    if (c==call_undefined)
      pips_internal_error("Unexpected call in statement number %d \n",(int) statement_number(stat));

    expression lhs_exp=EXPRESSION(CAR(call_arguments(c)));
    syntax lhs_syn= expression_syntax(lhs_exp);
    if (syntax_reference_p(lhs_syn))
      FormalName = reference_variable(syntax_reference(lhs_syn));
    else FormalName = entity_undefined;

    for (lr = pattern_region; !ENDP(lr); lr = CDR(lr)) {
      effect efs = REGION(CAR(lr));
      reference rs = effect_any_reference(efs);
      entity vs =  reference_variable(rs);

      if (store_effect_p(efs) &&
	  !effects_package_entity_p(vs) && !std_file_entity_p(vs) && !variable_heap_p(vs))
	xml_TaskParameter(assign_function,module, statement_number(stat),false,FormalName,
			  formal_parameters,lr,paving_indices,sb_result, buffer_assign);
    }
  }
  else {
    // Formal parameters list
    for (ith=1;ith<=FormalParameterNumber;ith++) {
      FormalName = find_ith_formal_parameter(module,ith);
      vect_add_elem (&formal_parameters,(Variable) FormalName,VALUE_ONE);
    }

    if (code_tag != code_is_a_main) {
      // Formal parameters of functions are printed in the function argument order
      for (ith=1;ith<=FormalParameterNumber;ith++) {
	FormalName = find_ith_formal_parameter(module,ith);

	xml_TaskParameter(assign_function,module, statement_number(stat),true,FormalName,
			  formal_parameters,pattern_region,paving_indices,sb_result, buffer_assign);
      }
    }
    else   {
      for (lr = pattern_region; !ENDP(lr); lr = CDR(lr)) {
	if (store_effect_p(REGION(CAR(lr))))
	  xml_TaskParameter(assign_function,module, statement_number(stat), false,FormalName,
			    formal_parameters,lr,paving_indices,sb_result, buffer_assign);
      }
    }
    xml_TaskReturnParameter(module, statement_number(stat),sb_result);
  }

  if (assign_function && !string_buffer_empty_p(buffer_assign)) {
    string_temp =string_buffer_to_string(buffer_assign);
    string_buffer_append(sb_result,string_temp);
  }
  string_temp=NULL;
  global_margin--;
  string_buffer_append_word("/TaskParameters",sb_result);
}

bool  eval_linear_expression(
			     expression exp, transformer ps, int *val, int *min, int *max)
{
  bool result=true;
  *val = 0;
  *min=0;
  *max=0;
  /* printf("Eval expression :\n");
     print_expression(exp);
     Psysteme prec = sc_dup((Psysteme) predicate_system(transformer_relation(ps)));
     printf("In context :\n");
     sc_print(prec, (get_variable_name_t) entity_local_name);
  */

  if (!transformer_undefined_p(ps) && transformer_is_rn_p(ps)) {
    *min=INT_MIN,*max =INT_MAX;
    return(false);
  }
   
  // Should  be part of semantics/utils.c FI
  set_analyzed_types();
  transformer psr=transformer_range(ps);
  type et = compute_basic_concrete_type(expression_to_type(exp));
  if (integer_type_p(et)) {
    integer_expression_and_precondition_to_integer_interval(exp,psr, min,max);
    // DEBUG - printf("Min = %d, Max = %d \n", *min,*max);
  }
  else result = false;
  free_transformer(psr);
  reset_analyzed_types();
  if (*max<*min) {
    *min=INT_MIN,*max =INT_MAX;
    result= false;
  }
  else if (*max==*min && result) {
    *val = *min;
  }
  return (result);
}

/* UNUSED
static bool  eval_linear_expression2(
  expression exp, Psysteme ps, int *val, int *min, int *max)
{
  normalized norm= normalized_undefined;
  Pvecteur   vexp,pv;
  bool result = true,result_exact = true,min_exact=true,max_exact=true;
  *val = 0;
  *min=0;
  *max=0;

  // fprintf(stdout,"Expression a evaluer : %s",words_to_string(words_expression(exp,NIL)));

  if (expression_normalized(exp) == normalized_undefined)
    expression_normalized(exp)= NormalizeExpression(exp);
  norm = expression_normalized(exp);
  if (normalized_linear_p(norm) && !SC_UNDEFINED_P(ps)) {
    vexp = (Pvecteur)normalized_linear(norm);
    for (pv= vexp; pv != VECTEUR_NUL; pv=pv->succ) {
      Variable v = var_of(pv);
      if (v==TCST) {
	*val += vect_coeff(TCST,vexp);
	*min += vect_coeff(TCST,vexp);
	*max += vect_coeff(TCST,vexp);
      }
      else {
	if(base_contains_variable_p(sc_base(ps), v)) {
	  Value min1, max1;
	  Psysteme ps1 = sc_dup(ps);
	  bool  feasible = sc_minmax_of_variable2(ps1, (Variable)v, &min1, &max1);
	  if (feasible) {
	    if (value_eq(min1,max1)) {
	      *val += vect_coeff(v,vexp) *min1;
	      *min+= vect_coeff(v,vexp) *min1;
	      *max+= vect_coeff(v,vexp) *max1;
	    }
	    else {
	      result_exact=false;
	      bool pb = (vect_coeff(v,vexp)>0);
	      if (pb) {
		if (*min!=INT_MIN && min1!=INT_MIN && min1!=VALUE_MIN)
		  *min+= vect_coeff(v,vexp) *min1;
		else min_exact=false;
		if (*max!=INT_MAX && max1!=INT_MAX && max1!=VALUE_MAX)
		  *max+= vect_coeff(v,vexp) *max1;
		else max_exact=false;
	      }
	      else   {
		if (*max!=INT_MIN && min1!=INT_MIN && min1!=VALUE_MIN)
		  *max+= vect_coeff(v,vexp) *min1;
		else max_exact=false;
		if (*min!=INT_MAX && max1!=INT_MAX && max1!=VALUE_MAX)
		  *min+= vect_coeff(v,vexp) *max1;
		else min_exact=false;
	      }
	    }
	  }
	  else  // fprintf(stdout,"le systeme est non faisable\n");
	    result = false,min_exact=false,max_exact=false;
	} //  sc_free(ps1); le systeme est desalloue par sc_minmax_of_variable
	else
	  result = false,min_exact=false,max_exact=false;
      }
    }
  }
  else  // fprintf(stdout,"Ce n'est pas une expression lineaire\n");
    result = false,min_exact=false,max_exact=false;
  if (!result) *min=INT_MIN,*max =INT_MAX;
  if (!min_exact) *min=INT_MIN;
  if (!max_exact) *max=INT_MAX;
  if (!result_exact) result=false;
  //fprintf(stdout,"Valeur trouvee : %d \n",*val);
  return result;
}
*/

static void xml_Bounds(expression elow, expression eup, transformer t,
                       _UNUSED_ Psysteme prec, bool formal_p, string_buffer sb_result) {
  intptr_t low, up;
  int valr = 0;
  int min = 0, max = 0;
  bool tb = true;
  /* Print XML Array LOWER BOUND */
  string_buffer_append_word("LowerBound", sb_result);
  global_margin++;
  string_buffer_append_symbolic(expression_to_string(elow), sb_result);
  if (expression_integer_value(elow, &low))
    string_buffer_append_numeric(int2a(low), sb_result);
  else if (!formal_p && (tb = eval_linear_expression(elow, t, &valr, &min, &max)) == true) {
    if (valr == min && valr == max)
      string_buffer_append_numeric(int2a(valr), sb_result);
    else {
      if (min != INT_MIN) {
	add_margin(global_margin, sb_result);
	string_buffer_append(sb_result,
			     concatenate(OPENANGLE,
					 "MinNumeric", CLOSEANGLE, int2a(min), OPENANGLE,
					 "/MinNumeric",
					 CLOSEANGLE, NL, NULL));
      }
      if (max != INT_MAX) {
	add_margin(global_margin, sb_result);
	string_buffer_append(sb_result,
			     concatenate(OPENANGLE,
					 "MaxNumeric", CLOSEANGLE, int2a(max), OPENANGLE,
					 "/MaxNumeric",
					 CLOSEANGLE, NL, NULL));
      }
    }
  }
  global_margin--;
  string_buffer_append_word("/LowerBound", sb_result);

  /* Print XML Array UPPER BOUND */
  string_buffer_append_word("UpperBound", sb_result);
  global_margin++;
  string_buffer_append_symbolic(expression_to_string(eup), sb_result);
  if (expression_integer_value(eup, &up))
    string_buffer_append_numeric(int2a(up), sb_result);
  else if (!formal_p && (tb = eval_linear_expression(eup, t, &valr, &min, &max)) == true) {
    if (valr == min && valr == max)
      string_buffer_append_numeric(int2a(valr), sb_result);
    else {
      if (min != INT_MIN) {
	add_margin(global_margin, sb_result);
	string_buffer_append(sb_result,
			     concatenate(OPENANGLE,
					 "MinNumeric", CLOSEANGLE, int2a(min), OPENANGLE,
					 "/MinNumeric",
					 CLOSEANGLE, NL, NULL));
      }
      if (max != INT_MAX) {
	add_margin(global_margin, sb_result);
	string_buffer_append(sb_result,
			     concatenate(OPENANGLE,
					 "MaxNumeric", CLOSEANGLE, int2a(max), OPENANGLE,
					 "/MaxNumeric",
					 CLOSEANGLE, NL, NULL));
      }
    }
  }
  global_margin--;
  string_buffer_append_word("/UpperBound", sb_result);
}
static void xml_Bounds_and_Stride(expression elow, expression eup, expression stride,
				  transformer t, Psysteme prec, bool formal_p, string_buffer sb_result)
{
  intptr_t inc;
  int  valr =0,min=0,max=0;
  xml_Bounds(elow, eup,t,prec,formal_p, sb_result);
  string_buffer_append_word("Stride",sb_result);
  global_margin++;
  string_buffer_append_symbolic(expression_to_string(stride),
				sb_result);
  if (expression_integer_value(stride, &inc))
    string_buffer_append_numeric(int2a(inc),sb_result);
  else if (eval_linear_expression(stride,t,&valr,&min,&max)) {
    if (valr==min && valr==max)
      string_buffer_append_numeric(int2a(valr),sb_result);
  }
  global_margin--;
  string_buffer_append_word("/Stride",sb_result);

}

static void find_memory_comment_on_array(statement s)
{
  string comm = statement_comments(s);
  string result = NULL;

  if (!string_undefined_p(comm)
      && (result=strstr(comm,array_mem_string))!=NULL)
    array_location_string = result;
}

static string memory_location_for_array_p(const char* sa)
{
  statement stat = get_current_module_statement();
  string result=NULL;
  int n=0;

  array_location_string = NULL;
  array_mem_string = (char *)malloc(strlen(sa)+5+1);
  (void)  strcpy(array_mem_string, sa);
  (void) strcat(array_mem_string,MEM_PREFIX);
  gen_recurse(stat, statement_domain, gen_true,find_memory_comment_on_array);
  if (array_location_string != NULL) {
    n= strcspn(array_location_string+strlen(sa)+5,":\n");
    result=(char *)malloc(n+1);
    strncpy(result,array_location_string+strlen(sa)+5,n);
    result[n]=(char) 0;
  }
  free(array_mem_string);
  return (result);
}


static void xml_Array(entity var,transformer t,Psysteme prec, bool formal_p, string_buffer sb_result)
{
  const char* datatype ="";
  list ld, ldim = variable_dimensions(type_variable(entity_type(var)));
  int i,j, size =0;
  int nb_dim = (int) gen_length(ldim);
  char* layout_up[nb_dim];
  char *layout_low[nb_dim];
  int no_dim=0;

  string spec_location = memory_location_for_array_p(entity_user_name(var));

  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE, "Array Name=",QUOTE,NULL));
  string_buffer_append_xml_text(sb_result,(string) entity_user_name(var),false);
  string_buffer_append(sb_result,
		       concatenate(QUOTE, BL,
				   "Type=", QUOTE,(entity_xml_parameter_p(var))? "CONTROL":"DATA",QUOTE,BL,
				   "Allocation=", QUOTE,
				   (heap_area_p(var) || stack_area_p(var)) ? "DYNAMIC": "STATIC", QUOTE,BL,
				   "Kind=", QUOTE,   "VARIABLE",QUOTE,
				   CLOSEANGLE,NL, NULL));

  /* Print XML Array DATA TYPE and DATA SIZE */
  type_and_size_of_var(var, &datatype,&size);
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,
				   "DataType Type=",QUOTE,datatype,QUOTE, BL,
				   "Size=",QUOTE, int2a(size), QUOTE, "/"
				   CLOSEANGLE,NL,NULL));
  /* Print XML Array Memory Location */
  if (spec_location!=NULL) {
    add_margin(global_margin,sb_result);
    string_buffer_append(sb_result,
			 concatenate(OPENANGLE,
				     "ArrayLocation",CLOSEANGLE, spec_location,OPENANGLE,
				     "/ArrayLocation",CLOSEANGLE,
				     NL, NULL));
  }
  /* Print XML Array DIMENSION */

  if((int) gen_length(ldim) >0) {
    string_buffer_append_word("Dimensions",sb_result);

    for (ld = ldim ; !ENDP(ld); ld = CDR(ld)) {
      expression elow = dimension_lower(DIMENSION(CAR(ld)));
      expression eup = dimension_upper(DIMENSION(CAR(ld)));
      global_margin++;
      string_buffer_append_word("Dimension",sb_result);
      /* Print XML Array Bound */
      global_margin++;
      xml_Bounds(elow,eup,t,prec, formal_p, sb_result);
      global_margin--;
      string_buffer_append_word("/Dimension",sb_result);
      global_margin--;
      layout_low[no_dim] = expression_to_string(elow);
      layout_up[no_dim] = expression_to_string(eup);
      no_dim++;
    }
  }

  string_buffer_append_word("/Dimensions",sb_result);

  /* Print XML Array LAYOUT */
  string_buffer_append_word("Layout",sb_result);
  global_margin++;
  for (i =0; i<= no_dim-1; i++) {
    string_buffer_append_word("DimLayout",sb_result);
    global_margin++;
    string_buffer_append_word("Symbolic",sb_result);
    if (i==no_dim-1) {
      add_margin(global_margin,sb_result);
      string_buffer_append(sb_result,concatenate("1",NL,NULL));
    }
    else {
      add_margin(global_margin,sb_result);
      for (j=no_dim-1; j>=i+1; j--)
	{
	  if (strcmp(layout_low[j],"0")==0)
	    string_buffer_append(sb_result,
				 concatenate("(",layout_up[j],"+1)",NULL));
	  else
	    string_buffer_append(sb_result,
				 concatenate("(",layout_up[j],"-",
					     layout_low[j],"+1)",NULL));
	  if (j==i+1)
	    string_buffer_append(sb_result,NL);
	}
    }
    string_buffer_append_word("/Symbolic",sb_result);
    global_margin--;
    string_buffer_append_word("/DimLayout",sb_result);
  }
  global_margin--;
  string_buffer_append_word("/Layout",sb_result);
  string_buffer_append_word("/Array",sb_result);
}

static void xml_Scalar(entity var, _UNUSED_ Psysteme prec,string_buffer sb_result)
{
  const char* datatype ="";
  int  size =0;

  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE, "Scalar Name=", QUOTE,NULL));
  string_buffer_append_xml_text(sb_result, (string) entity_user_name(var),false);
  string_buffer_append(sb_result,
		       concatenate(QUOTE, BL,
				   "Type=", QUOTE,(entity_xml_parameter_p(var))? "CONTROL":"DATA",QUOTE,BL,
				   "Allocation=", QUOTE,
				   (heap_area_p(var) || stack_area_p(var)) ? "DYNAMIC": "STATIC", QUOTE,BL,
				   "Kind=", QUOTE,"VARIABLE",QUOTE, NULL));
  /* Print XML Array DATA TYPE and DATA SIZE */
  type_and_size_of_var(var, &datatype,&size);
  //add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(BL,
				   "DataType=",QUOTE,datatype,QUOTE, BL,
				   "Size=",QUOTE, int2a(size), QUOTE, "/"
				   CLOSEANGLE,NL,NULL));
}

static void xml_GlobalVariables(transformer t,Psysteme prec, bool printp, string_buffer sb_result)
{
  list ldecl;
  int nb_dim=0;

  Pvecteur v_already_seen=VECTEUR_NUL;
  statement s = get_current_module_statement();
  cumulated_list = NIL;
  gen_recurse(s, statement_domain, gen_true, cumul_effects_of_statement);

  ldecl = statement_declarations(s);
  MAP(ENTITY,var, {
      vect_add_elem(&v_already_seen,var,1);
    },ldecl);
  if((int) gen_length( cumulated_list) >0) {
    string_buffer_append_word("GlobalVariables",sb_result);
    global_margin++;
    MAP(EFFECT,ef, {
	reference ref = effect_any_reference(ef);
	entity v = reference_variable(ref);
	if (type_variable_p(entity_type(v))
	    && !effects_package_entity_p(v) && !std_file_entity_p(v) && !variable_heap_p(v)
	    &&  (storage_ram_p(entity_storage(v)))
	    && top_level_entity_p(v)
	    && !storage_formal_p(entity_storage(v))
	    && !vect_coeff(v,v_already_seen)) {
	  vect_add_elem(&v_already_seen,v,1);
	  if (printp) {
	    if ((nb_dim = variable_entity_dimension(v))>0)
	      xml_Array(v,t,prec,false,sb_result);
	    else xml_Scalar(v,prec,sb_result);
	  }
	}
      }, cumulated_list);
    global_application_variables=vect_copy(v_already_seen);
    vect_rm(v_already_seen);
    global_margin--;
    string_buffer_append_word("/GlobalVariables",sb_result);
  }
  else
    string_buffer_append_word("GlobalVariables/",sb_result);
}

static void store_local_array_declaration(statement s)
{
  list ls;
  if (declaration_statement_p(s)) {
    ls=statement_declarations(s);
    local_declaration_list = gen_append(local_declaration_list,ls);
  }
}
static void xml_LocalVariables(entity module, transformer t, Psysteme prec,string_buffer sb_result)
{
  list ldecl;
  int nb_dim=0;
  Pvecteur pv_dec= vect_new(TCST,1);
  statement s = get_current_module_statement();
  if (fortran_appli)
    ldecl = code_declarations(value_code(entity_initial(module)));
  else
    ldecl = statement_declarations(s);

  if((int) gen_length(ldecl) >0) {
    string_buffer_append_word("LocalVariables",sb_result);
    global_margin++;
    MAP(ENTITY,var, {
	if (type_variable_p(entity_type(var))
	    //&& ((nb_dim = variable_entity_dimension(var))>0)
	    &&  !(storage_formal_p(entity_storage(var)))) {
	  if ((nb_dim = variable_entity_dimension(var))>0)
	    xml_Array(var,t, prec,false,sb_result);
	  else xml_Scalar(var,prec,sb_result);
	  vect_add_elem(&pv_dec,(Variable)var,1);
	}
      },ldecl);
    local_declaration_list =NIL;
    gen_recurse(s,statement_domain,gen_true,store_local_array_declaration);
    //    printf("list tableaux locaux pour module %s\n",entity_user_name(module));
    //    MAP(ENTITY,var, {
    //	printf("Entity = %s\n",entity_user_name(var));
    //      },local_declaration_list);

    MAP(ENTITY,var, {
	if (type_variable_p(entity_type(var))
	    // && (variable_entity_dimension(var)>0)
	    &&  !(storage_formal_p(entity_storage(var)))
	    && !vect_coeff(var,pv_dec)) {
	  if ((nb_dim = variable_entity_dimension(var))>0)
	    xml_Array(var,t, prec,false,sb_result);
	  else xml_Scalar(var,prec,sb_result);
	  vect_add_elem(&pv_dec,(Variable)var,1);
	}
      },local_declaration_list);

    global_margin--;
    string_buffer_append_word("/LocalVariables",sb_result);
    local_application_variables=vect_copy(pv_dec);
  }
  else
    string_buffer_append_word("LocalVariables/",sb_result);
  vect_rm(pv_dec);
}

static void xml_FormalVariables(entity module, transformer t, Psysteme prec,string_buffer sb_result)
{
  // gen_length(functional_results(type_functional(entity_type(module))))
  int FormalParameterNumber = (int) gen_length(module_formal_parameters(module));
  entity FormalArrayName = entity_undefined;
  int ith ;
  if(FormalParameterNumber >=1) {
    string_buffer_append_word("FormalVariables",sb_result);
    global_margin++;

    for (ith=1;ith<=FormalParameterNumber;ith++) {
      FormalArrayName = find_ith_formal_parameter(module,ith);
      if (type_variable_p(entity_type(FormalArrayName))
	  &&  (storage_formal_p(entity_storage(FormalArrayName)))) {
	if (variable_entity_dimension(FormalArrayName)>0)
	  xml_Array(FormalArrayName,t, prec, true, sb_result);
	else xml_Scalar(FormalArrayName,prec,sb_result);
      }
    }
    global_margin--;
    string_buffer_append_word("/FormalVariables",sb_result);
  }
  else string_buffer_append_word("FormalVariables/",sb_result);
}

static bool pragma_motif_p(statement s)
{
  extensions es = statement_extensions(s);
  list exl=extensions_extension(es);
  string name="MOTIF";
  bool result=false;
  FOREACH(EXTENSION, ex, exl){
    if (extension_pragma_p(ex)) {
      pragma p = extension_pragma(ex);
      if(pragma_string_p(p)) {
        if(same_string_p(pragma_string(p),name))
          result= true;
      }
    }
  }
  return result;
}

static void motif_in_statement(statement s)
{
  if (pragma_motif_p(s)) motif_in_statement_p= true;
}
/* currently unused
   static void motif_in_statement2(statement s)
   {
   string comm = statement_comments(s);
   if (!string_undefined_p(comm) && strstr(comm,"MOTIF")!=NULL)
   motif_in_statement_p= true;
   }
*/
static void box_in_statement(statement s)
{
  string comm = statement_comments(s);
  if (!string_undefined_p(comm) && strstr(comm,"BOX")!=NULL)
    box_in_statement_p= true;
}

static bool string_parameter_p(entity e)
{
  const char * comm = entity_user_name(e);
  if (!string_undefined_p(comm) && strstr(comm,"\"")!=NULL)
    return (true);
  else return (false);
}

static void xml_Loop(statement s, string_buffer sb_result)
{
  loop l = instruction_loop(statement_instruction(s));
  transformer t = load_statement_precondition(s);
  Psysteme prec = sc_dup((Psysteme) predicate_system(transformer_relation(t)));
  expression el =range_lower(loop_range(l));
  expression eu =range_upper(loop_range(l));
  expression stride = range_increment(loop_range(l));
  entity index =loop_index(l);

  push_statement_on_statement_global_stack(s);
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,
				   "Loop Index=",QUOTE, NULL));
  string_buffer_append_xml_text(sb_result, (string) entity_user_name(index),false);
  string_buffer_append(sb_result,
		       concatenate(QUOTE, BL,
				   "ExecutionMode=",QUOTE,
				   (execution_parallel_p(loop_execution(l)))? "PARALLEL":"SEQUENTIAL", QUOTE,
				   CLOSEANGLE,NL,NULL));
  xml_Bounds_and_Stride(el,eu,stride,t,prec, false,sb_result);
  string_buffer_append_word("/Loop",sb_result);
  pop_statement_global_stack();
 sc_free(prec);
}

static void xml_Loops(stack st,bool call_external_loop_p, list *pattern_region, Pvecteur *paving_indices, Pvecteur *pattern_indices, bool motif_in_te_p, string_buffer sb_result)
{
  bool in_motif_p=!call_external_loop_p && !motif_in_te_p;
  bool motif_on_loop_p=false;
  // Boucles externes a la TE
  if (call_external_loop_p)
    string_buffer_append_word("ExternalLoops",sb_result);
  else
    // Boucles externes au motif dans la TE
    string_buffer_append_word("Loops",sb_result);

  // if comment MOTIF is on the loop, the pattern_region is the loop region
  // if comment MOTIF is on a statement inside the sequence of the loop body
  // the cumulated regions of the loop body are taken
  // if comment MOTIF is outside the loop nest, the pattern_region is the call region
  global_margin++;
  if (st != STACK_NULL) {
    STACK_MAP_X(s, statement,
		{
		  loop l = instruction_loop(statement_instruction(s));
		  //string comm = statement_comments(s);
		  entity index =loop_index(l);
		  push_statement_on_statement_global_stack(s);
		  if (!in_motif_p) {
		    // Test : Motif is in the loop body  or not
		    motif_in_statement_p=false;
		    gen_recurse(loop_body(l), statement_domain, gen_true,motif_in_statement);
		    //motif_on_loop_p = !string_undefined_p(comm) && strstr(comm,"MOTIF")!=NULL;
		    motif_on_loop_p = pragma_motif_p(s);

		    if (motif_on_loop_p) {      // comment MOTIF  is on the Loop
		      *pattern_region = regions_dup(load_statement_local_regions(s));
		      vect_add_elem (pattern_indices,(Variable) index ,VALUE_ONE);
		    }
		    else if (motif_in_statement_p) {
		      // cumulated regions on the sequence of the loop body instructions are needed
		      *pattern_region = regions_dup(load_statement_local_regions(loop_body(l)));
		    }
		    in_motif_p =   (!call_external_loop_p && !motif_in_te_p) //Par default on englobe si TE
		      || in_motif_p        // on etait deja dans le motif
		      || motif_on_loop_p  // on vient de trouver un Motif sur la boucle
		      || (motif_in_te_p && !motif_on_loop_p && !motif_in_statement_p);
		    // motif externe au nid de boucles (cas des motif au milieu d'une sequence)
		  }
		  if (!in_motif_p) {
		    vect_add_elem (paving_indices,(Variable) index ,VALUE_ONE);
		    xml_Loop(s, sb_result);
		  }
		  (void) pop_statement_global_stack();
		},
		st, 0);
  }
  global_margin--;
  if (call_external_loop_p)
    string_buffer_append_word("/ExternalLoops",sb_result);
  else
    string_buffer_append_word("/Loops",sb_result);
}

static transformer first_precondition_of_module(const char* module_name __attribute__ ((unused)), Psysteme *ps)
{
  statement st1 = get_current_module_statement();
  statement fst = statement_undefined;
  instruction inst = statement_instruction(st1);
  transformer t=transformer_undefined;
  *ps= SC_UNDEFINED;
  switch instruction_tag(inst)
    {
    case is_instruction_sequence:{
      list sts = sequence_statements(instruction_sequence(inst));
      if (sts !=NULL)
	fst = STATEMENT(CAR(sts));
      break;
    }

    default:
      fst = st1;
    }
  if ( fst!= statement_undefined) {
    t = (transformer)load_statement_precondition(fst);
    *ps = sc_dup((Psysteme) predicate_system(transformer_relation(t)));
  }
  return t;
}

// ??? reset? zero?
static void matrix_init(Pmatrix mat, int n, int m)
{
  int i,j;
  for (i=1;i<=n;i++) {
    for (j=1;j<=m;j++) {
      MATRIX_ELEM(mat,i,j)=0;
    }
  }
}

static void xml_Matrix(Pmatrix mat, int n, int m, string_buffer sb_result)
{
  string srow, scolumn;
  int i,j;
  // cas des nids de boucles vides
  if (n==0 && m!=0) m=0;
  if (m==0 && n!=0) n=0;
  srow =strdup(i2a(n));
  scolumn=strdup(i2a(m));

  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,
				   "Matrix NbRows=", QUOTE,srow,QUOTE,BL,
				   "NbColumns=", QUOTE, scolumn,QUOTE, BL,
				   CLOSEANGLE,NL, NULL));
  for (i=1;i<=n;i++) {
    add_margin(global_margin,sb_result);
    string_buffer_append(sb_result,
			 concatenate(OPENANGLE,
				     "Row", CLOSEANGLE,BL, NULL));
    for (j=1;j<=m;j++) {
      string_buffer_append(sb_result,
			   concatenate(OPENANGLE,"c", CLOSEANGLE,
				       i2a(MATRIX_ELEM(mat,i,j)),
				       OPENANGLE, "/c", CLOSEANGLE,
				       BL, NULL));
    }
    string_buffer_append(sb_result,
			 concatenate(OPENANGLE,
				     "/Row", CLOSEANGLE, NL, NULL));
  }
  string_buffer_append_word("/Matrix",sb_result);
}

static int int_compare(void const *a, void const *b)
{
  int const*pa=a;
  int const*pb=b;
  return(*pb-*pa);
}

static void tri_abc(int a[12], int dim, int result[12])
{
  int a_copy[12];
  int i;
  memcpy(a_copy,a,(2*dim+1)*sizeof(int));
  qsort(&a_copy[1],dim,sizeof(int), int_compare);
  qsort(&a_copy[1+dim],dim,sizeof(int), int_compare);
  for (int k=0;k<=1;k++)
    for ( i=1; i<=dim; i++) {
      for (int j=1; j<=dim; j++)
	if (a_copy[i+dim*k]==a[j+dim*k])
	  result[i+dim*k]=j;
    }
}


static void xml_Transposed_Matrix2D( Pmatrix mat)
{
  MATRIX_ELEM(mat,1,1)=0;
  MATRIX_ELEM(mat,1,2)=1;
  MATRIX_ELEM(mat,2,1)=1;
  MATRIX_ELEM(mat,2,2)=0;
}

static void xml_Transposed_Matrix3_5D(
			       Pmatrix mat
			       ,int a[12], int ArrayDim1, _UNUSED_ int ArrayDim2)
{

  int i,j,n;
  int result[]={0,0,0,0,0,0,0,0,0,0,0,0};
  tri_abc(a,ArrayDim1,result);
  for (i=1; i<= ArrayDim1; i++) {
    n = result[i+ArrayDim1];
    for (j=1;j<=ArrayDim1;j++) {
      if (result[j]==n)
	MATRIX_ELEM(mat,i,j)=1;
    }
  }
}

static expression skip_cast_expression(expression exp)
{
  expression exp1=exp;
  if (syntax_cast_p(expression_syntax(exp)))
    exp1 = cast_expression(syntax_cast(expression_syntax(exp)));
  return exp1;
}

static expression skip_field_and_cast_expression(expression exp)
{
  expression exp1=exp;
  if (expression_field_p(exp))
    exp1= EXPRESSION(CAR(call_arguments(expression_call(exp))));
  if (syntax_cast_p(expression_syntax(exp1)))
    exp1 = cast_expression(syntax_cast(expression_syntax(exp1)));
  return exp1;
}

static expression skip_cast_and_addop_expression(expression exp)
{
  expression exp1=exp;
  if (syntax_cast_p(expression_syntax(exp)))
    exp1 = cast_expression(syntax_cast(expression_syntax(exp)));
  if (syntax_call_p(expression_syntax(exp1))) {
    call cl = syntax_call(expression_syntax(exp1));
    const char *fun = entity_local_name(call_function(cl));
    if (strcmp(fun, ADDRESS_OF_OPERATOR_NAME) == 0) {
      exp1 = EXPRESSION(CAR(call_arguments(cl)));
    }
  }
  return exp1;
}

/*
static expression skip_field_and_cast_and_addop_expression(expression exp)
{
  expression exp1=exp;
  if (expression_field_p(exp))
    exp1= EXPRESSION(CAR(call_arguments(expression_call(exp))));
  if (syntax_cast_p(expression_syntax(exp1)))
    exp1 = cast_expression(syntax_cast(expression_syntax(exp1)));
  if (syntax_call_p(expression_syntax(exp1))) {
    call cl = syntax_call(expression_syntax(exp1));
    const char *fun = entity_local_name(call_function(cl));
    if (strcmp(fun, ADDRESS_OF_OPERATOR_NAME) == 0) {
      exp1 = EXPRESSION(CAR(call_arguments(cl)));
    }
  }
  return exp1;
}
*/

// Only to deal with Opengpu cornerturns
// version =0 generates the transposition matrix for cornerturn_xd functions
// version =1 generates the transposition matrix for transpose_xd functions

static void  xml_Transposition(statement s, call c,int d,string_buffer sb_result, int version)
{
  int tab[]={0,0,0,0,0,0,0,0,0,0,0,0};
  int i;
  expression arg1=expression_undefined,arg2=expression_undefined;
  value v;
  list args = call_arguments(c);
  Pmatrix mat = NULL;

  if ((version==0)  && (int) gen_length(args)==3+3*d) {
    for (i=1; i<=d; i++) {
      arg1= EXPRESSION(CAR(args));
      POP(args);
    }
    for (i=1;i<=2*d;i++){
      arg2= EXPRESSION(CAR(args));
      v = EvalExpression(arg2);
      if (value_constant_p(v) && constant_int_p(value_constant(v))) {
	tab[i] = constant_int(value_constant(v));
      }
      POP(args);
    }
    POP(args);
    arg1= EXPRESSION(CAR(args));
    POP(args);
    arg2= EXPRESSION(CAR(args));

    if (d>2 && d<=5) {
      mat = matrix_new(d,d);
      matrix_init(mat,mat->number_of_lines,mat->number_of_columns);
      xml_Transposed_Matrix3_5D(mat,tab, mat->number_of_lines,mat->number_of_columns) ;
    }
    else if (d==2) {
      mat = matrix_new(2,2);
      matrix_init(mat,mat->number_of_lines,mat->number_of_columns);
      xml_Transposed_Matrix2D(mat);
    }
  }
  else if ((version==1)  && (int) gen_length(args)==3+2*d) {
    int j;
    mat = matrix_new(d,d);
    matrix_init(mat,mat->number_of_lines,mat->number_of_columns);
    for (i=1; i<= d; i++) {
      arg1= EXPRESSION(CAR(args));
      v = EvalExpression(arg1);
      if (value_constant_p(v) && constant_int_p(value_constant(v))) {
	j= constant_int(value_constant(v));
	if (0<=j && j<=d-1)
	  MATRIX_ELEM(mat,i,j+1)=1;
      }
      POP(args);
    }
    for (i=1; i<= d; i++)
      POP(args); // strides
    POP(args); // size
    arg1= EXPRESSION(CAR(args));
    POP(args);
    arg2= EXPRESSION(CAR(args));
  }
  else {
    spear_warning(s, "Change the arguments to be consistent with the prototype ",
		  "The prototype of the function %s is not correct ",
		  entity_user_name(call_function(c)));
  }
  // case with array field reference
  if (arg1 != expression_undefined && arg2 != expression_undefined) {
    arg1 = skip_field_and_cast_expression(arg1);
    arg2 = skip_field_and_cast_expression(arg2);
    if (array_argument_p(arg1) && array_argument_p(arg2)) {
      reference r1 = syntax_reference(expression_syntax(arg1));
      reference r2 = syntax_reference(expression_syntax(arg2));
      string_buffer_append_word("Transposition",sb_result);
      global_margin++;
      add_margin(global_margin,sb_result);
      string_buffer_append(sb_result,
			   concatenate(OPENANGLE,"TransposParameters ", "OUT=", QUOTE,NULL));
      string_buffer_append_xml_text(sb_result, (string) entity_user_name(reference_variable(r1)),false);
      string_buffer_append(sb_result,
			   concatenate(QUOTE,BL,
				       "IN=", QUOTE,entity_user_name(reference_variable(r2)),QUOTE,"/",
				       CLOSEANGLE,NL,NULL));
      xml_Matrix(mat,mat->number_of_lines,mat->number_of_columns,sb_result);
      matrix_free(mat);
      global_margin--;
      string_buffer_append_word("/Transposition",sb_result);
    }
  }
}

static void  xml_Task(const char* module_name, int code_tag, string_buffer sb_result)
{
  nest_context_t task_loopnest;
  task_loopnest.loops_for_call = stack_make(statement_domain,0,0);
  task_loopnest.loop_indices = stack_make(entity_domain,0,0);
  task_loopnest.current_stat = stack_make(statement_domain,0,0);
  task_loopnest.testif = stack_make(statement_domain,0,0);
  task_loopnest.nested_loops=  gen_array_make(0);
  task_loopnest.nested_loop_indices =  gen_array_make(0);
  task_loopnest.nested_call=  gen_array_make(0);
  task_loopnest.nested_if=  gen_array_make(0);
  stack nested_loops;
  list pattern_region =NIL;
  Pvecteur paving_indices = VECTEUR_NUL;
  Pvecteur pattern_indices = VECTEUR_NUL;
  bool motif_in_te_p = false;
  entity module = module_name_to_entity(module_name);
  Psysteme prec;
  transformer t;
  statement stat_module=(statement) db_get_memory_resource(DBR_CODE,
							   module_name, true);
  push_statement_on_statement_global_stack(stat_module);
  reset_rw_effects();
  set_rw_effects
    ((statement_effects)
     db_get_memory_resource(DBR_REGIONS, module_name, true));

  push_current_module_statement(stat_module);
  t = first_precondition_of_module(module_name,&prec);
  global_margin++;
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,
				   "Task Name=",QUOTE,
				   module_name,QUOTE,CLOSEANGLE,NL, NULL));
  global_margin++;

  find_loops_and_calls_in_box(stat_module,&task_loopnest);
  pattern_region = regions_dup(load_statement_local_regions(stat_module));

  xml_Library(sb_result);
  xml_Returns(sb_result);
  xml_Timecosts(sb_result);
  xml_GlobalVariables(t,prec,true,sb_result);
  xml_LocalVariables(module,t, prec,sb_result);
  xml_FormalVariables(module,t,prec,sb_result);
  /*  On ne traite qu'une TE : un seul nid de boucles */
  nested_loops = gen_array_item(task_loopnest.nested_loops,0);
  xml_Region_Parameter(pattern_region, sb_result);
  gen_recurse(stat_module, statement_domain, gen_true,motif_in_statement);
  motif_in_te_p = motif_in_statement_p;
  xml_Loops(nested_loops,false,&pattern_region,&paving_indices, &pattern_indices, motif_in_te_p, sb_result);
  xml_TaskParameters(stat_module, false,code_tag, module,pattern_region,paving_indices,sb_result);
  xml_Regions(sb_result);
  xml_CodeSize(sb_result);
  global_margin--;
  string_buffer_append_word("/Task",sb_result);
  global_margin--;

  pop_current_module_statement();
  gen_array_free(task_loopnest.nested_loops);
  gen_array_free(task_loopnest.nested_loop_indices);
  gen_array_free(task_loopnest.nested_call);
  gen_array_free(task_loopnest.nested_if);
  stack_free(&(task_loopnest.testif));
  stack_free(&(task_loopnest.loops_for_call));
  stack_free(&(task_loopnest.loop_indices));
  stack_free(&(task_loopnest.current_stat));
  pop_statement_global_stack();
  regions_free(pattern_region);
  sc_rm(prec);
}

// A completer
// ne traite que les cas ou tout est correctement aligne
// A traiter aussi le cas  ActualArrayDim = NIL
//
static void xml_Connection(list  ActualArrayInd,int ActualArrayDim, int FormalArrayDim, string_buffer sb_result)
{
  Pmatrix mat;
  int i,j;
  Pvecteur pv;
  string_buffer_append_word("Connection",sb_result);
  mat = matrix_new(ActualArrayDim,FormalArrayDim);
  matrix_init(mat,ActualArrayDim,FormalArrayDim);
  if (fortran_appli) {
    for (i=1;i<=ActualArrayDim && i<= FormalArrayDim;i++)
      MATRIX_ELEM(mat,i,i)=1;
  }
  else
    for (i=ActualArrayDim, j=FormalArrayDim;i>=1 && j>=1;i=i-1,j=j-1)
      MATRIX_ELEM(mat,i,j)=1;
  // Normalise les expressions lors du premier parcours
  // Utile aussi a  xml_LoopOffset
  MAP(EXPRESSION, e , {
      if (expression_normalized(e) == normalized_undefined)
	expression_normalized(e)= NormalizeExpression(e);
      pv = (Pvecteur)normalized_linear(expression_normalized(e));
      pv = pv;
    },
    ActualArrayInd);

  xml_Matrix(mat,ActualArrayDim,FormalArrayDim,sb_result);
  string_buffer_append_word("/Connection",sb_result);
}

static void xml_LoopOffset(list  ActualArrayInd,int ActualArrayDim, Pvecteur loop_indices,string_buffer sb_result)
{
  Pmatrix mat;
  Pvecteur loop_indices2 = vect_reversal(loop_indices);
  int nestloop_dim = vect_size(loop_indices2);
  Pvecteur pv, pv2;
  int i,j;

  string_buffer_append_word("LoopOffset",sb_result);
  mat = matrix_new(ActualArrayDim,nestloop_dim);
  matrix_init(mat,ActualArrayDim,nestloop_dim);
  i=1;
  MAP(EXPRESSION, e , {
      pv = (Pvecteur)normalized_linear(expression_normalized(e));
      for (pv2 = loop_indices2, j=1; !VECTEUR_NUL_P(pv2);pv2=pv2->succ,j++)
	MATRIX_ELEM(mat,i,j)=vect_coeff(pv2->var,pv);
      i++;
    },
    ActualArrayInd);

  xml_Matrix(mat,ActualArrayDim,nestloop_dim,sb_result);
  string_buffer_append_word("/LoopOffset",sb_result);
}


static void xml_ConstOffset(list ActualArrayInd, int ActualArrayDim, string_buffer sb_result)
{
  Pmatrix mat;
  Pvecteur pv;
  int i=1;
  string_buffer_append_word("ConstOffset",sb_result);
  mat = matrix_new(ActualArrayDim,1);
  matrix_init(mat,ActualArrayDim,1);
  MAP(EXPRESSION, e , {
      if (expression_normalized(e) == normalized_undefined)
	expression_normalized(e)= NormalizeExpression(e);
      pv = (Pvecteur)normalized_linear(expression_normalized(e));
      MATRIX_ELEM(mat,i,1)=vect_coeff(TCST,pv);
      i++;
    },
    ActualArrayInd);

  xml_Matrix(mat,ActualArrayDim,1,sb_result);
  string_buffer_append_word("/ConstOffset",sb_result);
}


typedef struct {
  reference rf;
  int alias_arg_p;
} alias_in_args;

static int check_alias_args(reference r, alias_in_args* p)
{
  p->alias_arg_p +=(reference_equal_p(r,p->rf))? 1:0;
  return p->alias_arg_p;
}

static bool aliasing_p(call c, reference refname)
{
  alias_in_args p = { refname, 0 };
  list largs = call_arguments(c);
  FOREACH(EXPRESSION, exp, largs) {
    gen_context_recurse(exp, &p, reference_domain, check_alias_args, gen_null2);
  }
  return p.alias_arg_p > 1;
}

static void xml_Argument(
  statement s, entity function, int statnb, bool assign_func,
  expression exp0, entity FormalName, Pvecteur loop_indices,
  transformer t, _UNUSED_ Psysteme prec, string_buffer sb_result)
{
  list call_effect = load_proper_rw_effects_list(s);
  entity ActualName = entity_undefined;
  reference ActualRef = reference_undefined;
  syntax sr;
  effect efr = effect_undefined, efw = effect_undefined;
  ;
  intptr_t iexp;
  int rw_ef = 0;
  string aan = "";
  //  string quote_p = "";
  int valr = 0, min = 0, max = 0;

  expression exp1= skip_cast_and_addop_expression(exp0);
  //skip field, cast and address operator
  //expression exp2 = skip_field_and_cast_and_addop_expression(exp0);
  expression exp2 = skip_cast_expression(exp0);
  expression exp=exp1;
  push_statement_on_statement_global_stack(s);
  sr = expression_syntax(exp);
  if (syntax_reference_p(sr)) {
    ActualRef = syntax_reference(sr);
    ActualName = reference_variable(ActualRef);
    //aan = strdup(entity_user_name(ActualName));
    aan = expression_to_string(exp2);
    rw_ef = find_effect_actions_for_entity(call_effect, &efr, &efw, ActualName);

    if (rw_ef == 3) { // Aliasing checking
      // First, search the Call
      call c = call_undefined;
      if (instruction_call_p(statement_instruction(s))) {
        c = instruction_call(statement_instruction(s));
      } else {
        encapsulated_call = call_undefined;
        gen_recurse(s, call_domain, gen_true, search_1r_function_call);
        c = encapsulated_call;
      }
      if (c == call_undefined)
	pips_internal_error("Unexpected call in statement number %d \n",(int) statement_number(s));

      if (aliasing_p(c, ActualRef))
        spear_warning(s, "Check the IN PLACE condition",
                      "Array %s is read and written into the same function and "
                      "appears twice as actual argument in the Call",
                      entity_user_name(ActualName));
    }
  } else {
    // Actual Parameter could be  an expression
    aan = words_to_string(Words_Syntax(sr));
    rw_ef = 1;
  }
  string_buffer_append_word("Argument", sb_result);
  if (!array_argument_p(exp)) { /* Scalar Argument */
    bool tb = true;
    global_margin++;
    add_margin(global_margin, sb_result);
    /* if (strncmp(aan, "\"", 1) == 0)
      quote_p = "";
    else
    quote_p = QUOTE;*/

    if (!assign_func) {
      string_buffer_append( sb_result,
			    concatenate(OPENANGLE,
					"ScalarArgument ActualName=", QUOTE, NULL));
      string_buffer_append_xml_text(sb_result,aan,false);
      string_buffer_append( sb_result,
			    concatenate(QUOTE, BL,
					"FormalName=", QUOTE,
					(!entity_undefined_p(FormalName)) ? entity_user_name(FormalName) : "LocalExpression",
					QUOTE, BL,
					"AccessMode=", QUOTE,
					(rw_ef >= 2) ? ((rw_ef == 2) ? "DEF" : "DEF_USE") : "USE",
					QUOTE, CLOSEANGLE, NL, NULL));
    }
    
    else {
      string_buffer_append(sb_result,
			   concatenate(OPENANGLE,
				       "ScalarArgument ActualName=", QUOTE, NULL));
      string_buffer_append_xml_text(sb_result,aan,false);
      string_buffer_append(sb_result,
			   concatenate(QUOTE, BL,
				       "AccessMode=", QUOTE,
				       (rw_ef >= 2) ? ((rw_ef == 2) ? "DEF" : "DEF_USE") : "USE",
				       QUOTE, CLOSEANGLE, NL, NULL));
    }
    if (expression_integer_value(exp, &iexp))
      string_buffer_append_numeric(int2a(iexp), sb_result);
    else if (value_constant_p(EvalExpression(exp))) {
      string exps = expression_to_string(exp);
      string_buffer_append_numeric(exps, sb_result);
    }
    else if ((tb = eval_linear_expression(exp1,t, &valr, &min, &max)) == true) {
      if (valr==min && valr==max)
	string_buffer_append_numeric(int2a(valr), sb_result);
      else {
	if (min != INT_MIN) {
	  add_margin(global_margin, sb_result);
	  string_buffer_append(sb_result,
			       concatenate(OPENANGLE,
					   "MinNumeric", CLOSEANGLE, int2a(min), OPENANGLE,
					   "/MinNumeric",
					   CLOSEANGLE, NL, NULL));
	}
	if (max != INT_MAX) {
	  add_margin(global_margin, sb_result);
	  string_buffer_append(sb_result,
			       concatenate(OPENANGLE,
					   "MaxNumeric", CLOSEANGLE, int2a(max), OPENANGLE,
					   "/MaxNumeric",
					   CLOSEANGLE, NL, NULL));
	}
      }
    }
    string_buffer_append_word("/ScalarArgument", sb_result);
    global_margin--;
    if (rw_ef >= 2) {
      Pcallst cst1 = (callst *)malloc(sizeof(callst));
      cst1->func = function;
      cst1->stat_nb = statnb;
      cst1->succ = (Pcallst)NULL;
      update_def_into_tasks_table(ActualName, cst1);
    }
  } else { /* Array Argument */
    int ActualArrayDim = variable_entity_dimension(ActualName);
    char *SActualArrayDim = strdup(i2a(ActualArrayDim));
    int FormalArrayDim = (entity_undefined_p(FormalName))
      ? 0
      : variable_entity_dimension(FormalName);
    list ActualArrayInd = reference_indices(ActualRef);

    global_margin++;
    add_margin(global_margin, sb_result);
    if (!assign_func) {
      string_buffer_append(sb_result,
			   concatenate(OPENANGLE,
				       "ArrayArgument ActualName=", QUOTE,NULL));
      string_buffer_append_xml_text(sb_result, (string) entity_user_name(ActualName),false);
      string_buffer_append(sb_result,
			   concatenate(QUOTE, BL,
				       //Give Array access function indices "ArrayArgument ActualName=", QUOTE, expression_to_string(exp2), QUOTE, BL,
				       "ActualDim=", QUOTE, SActualArrayDim, QUOTE, BL,
				       "FormalName=", QUOTE,
				       (!entity_undefined_p(FormalName)) ? entity_user_name(FormalName) : "LocalExpression",
				       QUOTE, BL,
				       "FormalDim=", QUOTE, i2a(FormalArrayDim), QUOTE, BL,
				       "AccessMode=", QUOTE,
				       (rw_ef >= 2) ? ((rw_ef == 2) ? "DEF" : "DEF_USE") : "USE",
				       QUOTE, CLOSEANGLE, NL, NULL));
    }
    else {
      string_buffer_append(sb_result,
			   concatenate(OPENANGLE,
				       "ArrayArgument ActualName=", QUOTE, NULL));
      string_buffer_append_xml_text(sb_result, (string) entity_user_name(ActualName),false);
      string_buffer_append(sb_result,
			   concatenate(QUOTE, BL,
				       // Give Array access function indices "ArrayArgument ActualName=", QUOTE, expression_to_string(exp2), QUOTE, BL,
				       "ActualDim=", QUOTE, SActualArrayDim, QUOTE, BL,
				       "AccessMode=", QUOTE, (rw_ef >= 2) ? ((rw_ef == 2) ? "DEF" : "DEF_USE") : "USE",
				       QUOTE, CLOSEANGLE, NL, NULL));
    }
    /* Save information to generate Task Graph */
    if (rw_ef >= 2) {
      Pcallst cst1 = (callst *)malloc(sizeof(callst));
      cst1->func = function;
      cst1->stat_nb = statnb;
      cst1->succ = (Pcallst)NULL;
      update_def_into_tasks_table(ActualName, cst1);
    }
    free(SActualArrayDim);
    xml_Connection(ActualArrayInd, ActualArrayDim, FormalArrayDim, sb_result);
    xml_LoopOffset(ActualArrayInd, ActualArrayDim, loop_indices, sb_result);
    xml_ConstOffset(ActualArrayInd, ActualArrayDim, sb_result);
    global_margin--;
    string_buffer_append_word("/ArrayArgument", sb_result);
  }
  string_buffer_append_word("/Argument", sb_result);
  (void) pop_statement_global_stack();
}

static void xml_AssignArgument(_UNUSED_ statement s, entity function, int statnb,
                        bool assign_func, expression exp, entity FormalName,
                        Pvecteur loop_indices, transformer t,
                        _UNUSED_ Psysteme prec, string_buffer sb_result)
{
  entity ActualName = entity_undefined;
  reference ActualRef = reference_undefined;
  syntax sr;
  intptr_t iexp;
  int rw_ef = 0;
  string aan = "";
  //  string quote_p = "";
  int valr = 0, min = 0, max = 0;

  sr = expression_syntax(exp);
  if (syntax_reference_p(sr)) {
    ActualRef = syntax_reference(sr);
    ActualName = reference_variable(ActualRef);
    aan = strdup(entity_user_name(ActualName));
    rw_ef = 2;
  } else
    printf("PB traduction AssignParameter\n");
  string_buffer_append_word("AssignArgument", sb_result);
  if (!array_argument_p(exp)) { /* Scalar Argument */
    global_margin++;
    add_margin(global_margin, sb_result);
    /* if (strncmp(aan, "\"", 1) == 0)
      quote_p = "";
    else
      quote_p = QUOTE;
    */
    string_buffer_append(sb_result,
			 concatenate(OPENANGLE,
				     "ScalarArgument ActualName=", QUOTE, NULL));
    string_buffer_append_xml_text(sb_result, aan, false);
    string_buffer_append(sb_result,
			 concatenate(QUOTE, BL,
				     "AccessMode=", QUOTE, "DEF", QUOTE,
				     CLOSEANGLE, NL, NULL));
    if (expression_integer_value(exp, &iexp))
      string_buffer_append_numeric(int2a(iexp), sb_result);
    else if (value_constant_p(EvalExpression(exp))) {
      string exps = expression_to_string(exp);
      string_buffer_append_numeric(exps, sb_result);
    } else if (eval_linear_expression(exp, t, &valr, &min, &max)) {
      if (valr==min && valr==max)
	string_buffer_append_numeric(int2a(valr), sb_result);
    }
    string_buffer_append_word("/ScalarArgument", sb_result);
    global_margin--;
    Pcallst cst1 = (callst *)malloc(sizeof(callst));
    cst1->func = function;
    cst1->stat_nb = statnb;
    cst1->succ = (Pcallst)NULL;
    update_def_into_tasks_table(ActualName, cst1);
  } else { /* Array Argument */
    int ActualArrayDim = variable_entity_dimension(ActualName);
    char *SActualArrayDim = strdup(i2a(ActualArrayDim));
    int FormalArrayDim = (entity_undefined_p(FormalName))
      ? 0
      : variable_entity_dimension(FormalName);
    list ActualArrayInd = reference_indices(ActualRef);
    global_margin++;
    add_margin(global_margin, sb_result);
    string_buffer_append( sb_result,
			  concatenate(OPENANGLE,
				      "ArrayArgument ActualName=", QUOTE, NULL));
    string_buffer_append_xml_text( sb_result, (string) entity_user_name(ActualName), false);
    string_buffer_append( sb_result,
			  concatenate(QUOTE, BL,
				      "ActualDim=", QUOTE, SActualArrayDim, QUOTE, BL,
				      "AccessMode=", QUOTE, (rw_ef >= 2) ? ((rw_ef == 2) ? "DEF" : "DEF_USE") : "USE", QUOTE,
				      CLOSEANGLE, NL, NULL));

    /* Save information to generate Task Graph */
    Pcallst cst1 = (callst *)malloc(sizeof(callst));
    cst1->func = function;
    cst1->stat_nb = statnb;
    cst1->succ = (Pcallst)NULL;
    update_def_into_tasks_table(ActualName, cst1);
    free(SActualArrayDim);
    if (!assign_func)
      xml_Connection(ActualArrayInd, ActualArrayDim, FormalArrayDim, sb_result);
    xml_LoopOffset(ActualArrayInd, ActualArrayDim, loop_indices, sb_result);
    xml_ConstOffset(ActualArrayInd, ActualArrayDim, sb_result);
    global_margin--;
    string_buffer_append_word("/ArrayArgument", sb_result);
  }
  string_buffer_append_word("/AssignArgument", sb_result);
}

static void  xml_Arguments(statement s, entity function, int statnb, bool assign_func, Pvecteur loop_indices, transformer t, Psysteme prec, string_buffer sb_result )
{
  entity FormalName= entity_undefined;
  intptr_t ith=0;
  call c = call_undefined, rhs_call= call_undefined;
  entity rhs_func=entity_undefined;
  expression lhs_exp;
  bool func_as_rhs_of_assign =false;

  if (instruction_call_p(statement_instruction(s))) {
    c = instruction_call(statement_instruction(s));
  }
  else {
    encapsulated_call =call_undefined;
    gen_recurse(s, call_domain, gen_true,search_1r_function_call);
    c =encapsulated_call;
  }
  if (c==call_undefined)
    pips_internal_error("Unexpected call in statement number %d \n",(int) statement_number(s));

  if (ENTITY_ASSIGN_P(function)) {
    list largs = call_arguments(c);
    if(gen_length(largs)==2) {
      POP(largs);
      expression rhs_exp = EXPRESSION(CAR(largs));
      syntax sr = expression_syntax(rhs_exp);
      if(syntax_call_p(sr)) {
	rhs_call = syntax_call(sr);
	rhs_func=call_function(rhs_call);
	func_as_rhs_of_assign = (entity_subroutine_p(rhs_func)|| entity_function_p(rhs_func)|| (io_intrinsic_p(rhs_func)));
      }
    }
  }
  string_buffer_append_word("Arguments",sb_result);
  global_margin++;
  call final_call = (func_as_rhs_of_assign)? rhs_call:c;
  entity final_func = (func_as_rhs_of_assign)? rhs_func:function;
  bool asb = (!assign_func || (assign_func && func_as_rhs_of_assign &&  !io_intrinsic_p(rhs_func)));
  FOREACH(EXPRESSION,exp,call_arguments(final_call)){
    ith ++;
    if (asb)
      FormalName = find_ith_formal_parameter(call_function(final_call),ith);
    else FormalName = entity_undefined;
    xml_Argument(s,final_func,statnb, (assign_func && !func_as_rhs_of_assign),exp,FormalName, loop_indices,t,prec,sb_result);
  }
  if (func_as_rhs_of_assign) {
    lhs_exp=EXPRESSION(CAR(call_arguments(c)));
    FormalName = reference_variable(syntax_reference(expression_syntax(lhs_exp)));
    xml_AssignArgument(s,final_func,statnb, assign_func,lhs_exp,FormalName, loop_indices,t, prec,sb_result);
  }
  global_margin--;
  string_buffer_append_word("/Arguments",sb_result);
}

static void statement_in_truebranch(statement s)
{
  if (statement_number(test_statement_of_reference) == statement_number(s))
    statement_in_truebranch_p= true;
}


static bool logic_condition_filter(statement s1,statement sx, entity *cond,expression *lhs,expression *rhs )
{
  if ( !statement_undefined_p(sx) &&  instruction_test_p(statement_instruction(sx))) {
    test l = instruction_test(statement_instruction(sx));
    expression exp=test_condition(l);
    if (syntax_call_p(expression_syntax(exp))) {
      call oper=syntax_call(expression_syntax(exp));
      *cond=call_function(oper);
      if (ENTITY_LOGICAL_OPERATOR_P(call_function(oper))) {
	list largs_oper= call_arguments(oper);
	if (gen_length(largs_oper)>=2) {
	  *lhs = EXPRESSION(CAR(largs_oper));
	  *rhs = EXPRESSION(CAR(CDR(largs_oper)));
	  return true;
	}
	else
	  spear_warning(s1,"Change the test or Encapsulate it into a function",
			"NON BINARY OPERATORS in conditional are not accepted outside task");
      }
      else  spear_warning(s1,"Change the test or Encapsulate it into a function",
			  "NON LOGICAL OPERATORS in conditional are not accepted outside task");
    }
    else
      spear_warning(s1,"Change the test or Encapsulate it into a function",
		    "The conditional is not a LOGICAL TEST");
  }
  return false;
}


static void dependencies_filter(statement s1,int *k1)
{
  entity func1=entity_undefined;
  instruction inst;
  // Filtering  function call and another function call or a declaration or a conditional
  if (declaration_statement_p(s1))
    *k1=2;
  else {
    inst = statement_instruction(s1);
    switch(instruction_tag(inst)) {
    case is_instruction_call : {
      func1 = call_function(instruction_call(statement_instruction(s1)));
      //      call_func_p1=((ENTITY_ASSIGN_P(func1)) ||entity_subroutine_p(func1)|| entity_function_p(func1));
      *k1= ENTITY_ASSIGN_P(func1)? 0 : 1;
      break;
    }
    case is_instruction_test : {
      *k1=3;
      break;
    }
    default:break;
    }
  }
}

static bool indice_p(stack indices, entity v)
{
  bool result=false;
  STACK_MAP_X(index,entity,
              {
                if (same_entity_p(index ,v)) result=true;
              }, indices,1);
  return result;
}

static void xml_Chain_Graph(entity module, statement mod_stat,
		     graph mod_graph,nest_context_p nest, string_buffer sb_result)
{
  cons *pv1, *ps, *pc;
  string_buffer buff_computed_by_func1 = string_buffer_make(true);
  string_buffer buff_needed_from_func1 = string_buffer_make(true);
  string_buffer buff_cumul_needed = string_buffer_make(true);
  string_buffer buffer_cond = string_buffer_make(true);
  string string_temp, stn1="", stn2="";
  bool new_temp=false, empty_buff_computed_by_func1=true,new_cond=false;
  bool new_temp2=false, empty_buff_needed_from_func1=true;
  bool empty_buff_cumul_needed=true;
  int taskNumber=0;
  stack statif=STACK_NULL;
  entity func1=entity_undefined;
  entity func2=entity_undefined;
  entity cond;
  expression lhs,rhs;
  statement sc;
  int nb_cond=0;
  int stat_kind1=-1,stat_kind2=-1;
  Pvecteur written_cumul = VECTEUR_UNDEFINED, vr= VECTEUR_UNDEFINED,vw= VECTEUR_UNDEFINED;
  list cumulated_effects_list=NIL, local_effects=NIL;
  string st_nb1, st_nb2;
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,
				   "BoxGraph Name=", QUOTE,entity_user_name(module), QUOTE,
				   CLOSEANGLE,NL, NULL));
  global_margin++;

  // COMPUTATION of the cumulated proper effects for the 2 following lists of NEEDS and COMPUTES
  cumulated_list = NIL;
  gen_recurse(mod_stat, statement_domain, gen_true, cumul_and_update_effects_of_statement);
  cumulated_effects_list= cumulated_list;
  vars_read_and_written(cumulated_effects_list,&vr,&vw);

  ifdebug(8) {
    print_ordering_to_statement( );
  }
  gen_sort_list(graph_vertices(mod_graph), (gen_cmp_func_t)vertex_sort_callback);
  for ( pv1 = graph_vertices(mod_graph); !ENDP(pv1); pv1 = CDR(pv1) ) {
    vertex v1 = VERTEX(CAR(pv1));
    statement s1 = vertex_to_statement( v1 );
    Pvecteur vread_func1= vect_new(TCST,1);
    Pvecteur vwritten_func1 = vect_new(TCST,1); // only 1 "xml COMPUTES information" per reference for each call statement S1
    Pvecteur vread_in_condition= vect_new(TCST,1);
    buffer_cond = string_buffer_make(true);
    buff_computed_by_func1 = string_buffer_make(true);
    gen_sort_list(vertex_successors(v1), (gen_cmp_func_t)successor_sort_callback);
    new_temp=false;
    taskNumber=-1;
    new_cond=false;
    func1=entity_undefined;
    statif = STACK_NULL;
    stack indices= STACK_NULL;;
    //  Recovery of conditions on/in statement s1, if any
    for (int callnumber = 0; callnumber<(int)gen_array_nitems(nest->nested_call); callnumber++) {
      statement s3 = gen_array_item(nest->nested_call,callnumber);
      if (statement_number(s3) == statement_number(s1))
	taskNumber=callnumber;
    }
    if (taskNumber>=0) {
      sc = gen_array_item(nest->nested_call,taskNumber);
      indices = gen_array_item(nest->nested_loop_indices,taskNumber);
      local_effects=regions_dup(load_statement_local_regions(sc));
      statif = gen_array_item(nest->nested_if,taskNumber);
    }
    // Conditional information around the dependencies
    if (statif != STACK_NULL) {
      test_statement_of_reference=s1;
      nb_cond=0; // to restore alignment
      global_margin++;
      STACK_MAP_X(sx, statement,
		  {  if (logic_condition_filter(s1,sx,&cond,&lhs,&rhs)) {
		      test l = instruction_test(statement_instruction(sx));
		      push_statement_on_statement_global_stack(sx);
		      statement_in_truebranch_p=false;
		      if (!statement_undefined_p(test_true(l)))
			gen_recurse(test_true(l), statement_domain, gen_true,statement_in_truebranch);
		      add_margin(global_margin,buffer_cond);
		      //DEBUG -   printf("Condition Branch=%s Test=\n", (statement_in_truebranch_p ? "TRUE":"FALSE"),(string)entity_user_name(cond));
		      string_buffer_append(buffer_cond,
					   concatenate(OPENANGLE,
						       "Condition Branch=",
						       QUOTE, (statement_in_truebranch_p ? "TRUE":"FALSE"),
						       QUOTE,  BL,
						       "Test=", QUOTE, NULL));
		      string_buffer_append_xml_text(buffer_cond,(string)entity_user_name(cond),false);
		      string_buffer_append(buffer_cond,
					   concatenate(QUOTE,  BL,
						       "LHS=",QUOTE, expression_to_string(lhs), QUOTE,  BL,
						       "RHS=",QUOTE, expression_to_string(rhs), QUOTE, BL,
						       "StNumber=",QUOTE,int2a(statement_number(sx)),QUOTE,
						       CLOSEANGLE,NL, NULL));
		      // For special character :  string_buffer_append_xml_text(buffer_cond,exps,false);
		      global_margin++;nb_cond++;

		      { // usefull to add the READ effects on variables referenced into condition
			list l = load_proper_rw_effects_list(sx);
			if (!ENDP(l) && !list_undefined_p(l)) {
			  
			  for (list pc = l; pc != NIL; pc = CDR(pc)) {
			    effect e = EFFECT(CAR(pc));
			    reference r = effect_any_reference(e);
			    action ac = effect_action(e);
			    entity v = reference_variable(r);
			    if (store_effect_p(e)
				&& !effects_package_entity_p(v) && !std_file_entity_p(v) && !variable_heap_p(v)
				// local effect = read and no written effect in the function
				&& action_read_p(ac) && vect_coeff(v,vw)==0 &&
				!(entity_static_variable_p(v) && !top_level_entity_p(v))) {
				vect_add_elem(&vread_in_condition,(Variable)v,statement_number(sx));
			    }
			  }
			  }
		      }
		      
		      (void) pop_statement_global_stack();
		    }
		  },
		  statif, 0);
      global_margin--;
      if (nb_cond>0) new_cond=true;
    }

    // Scan dependences from Call statement S1 to all Call Statement S2
    for ( ps = vertex_successors(v1); !ENDP(ps); ps = CDR(ps) ) {
      successor su = SUCCESSOR(CAR(ps));
      vertex v2 = successor_vertex(su);
      statement s2 = vertex_to_statement( v2 );
      dg_arc_label dal = (dg_arc_label) successor_arc_label(su);
      list cl = dg_arc_label_conflicts(dal);
      int nb_conflicts = gen_length(cl);
      vread_func1 = vect_new(TCST,1);
      buff_needed_from_func1 = string_buffer_make(true);
      new_temp2=false;
      empty_buff_needed_from_func1=true;
      if(get_bool_property("PRETTYPRINT_MEMORY_EFFECTS_ONLY")) {
	FOREACH(CONFLICT, c, cl) {
	  effect efsrc = conflict_source(c);
	  if(!store_effect_p(efsrc))
	    nb_conflicts--;
	}
      }
      if(nb_conflicts==0)
	continue;
      if ( nb_conflicts > 1 ) { //SORT
	gen_array_t conflicts_array = gen_array_make( 20 );
        list_to_array( dg_arc_label_conflicts(dal), conflicts_array );
        qsort( gen_array_pointer( conflicts_array ),
               gen_array_nitems( conflicts_array ),
               sizeof(void *),
               (gen_cmp_func_t) conflicts_sort_callback);
        list conflicts_list = NIL;
        GEN_ARRAY_FOREACH(conflict, s, conflicts_array)
          conflicts_list = CONS(conflict, s, conflicts_list);
        gen_array_free(conflicts_array);
        dg_arc_label_conflicts(dal)=conflicts_list;
      }

      stat_kind1=-1, stat_kind2=-1;
      dependencies_filter(s1,&stat_kind1);
      dependencies_filter(s2,&stat_kind2);
      if ((( 0<=stat_kind1 && stat_kind1 <=1)
	   && ( 0<=stat_kind2 && stat_kind2 <=1) && !(statement_number(s2) == statement_number(s1)))
	  || ((stat_kind1==2 || stat_kind1==3) && ( 0<=stat_kind2 && stat_kind2 <=1) )
	  || ((stat_kind2==2 || stat_kind2==3) && ( 0<=stat_kind1 && stat_kind1 <=1))) {
	st_nb1=int2a(statement_number(s1));
	st_nb2=int2a(statement_number(s2));
	// DEBUG - printf( "\t\tdependence %s - %s  between %s  and  %s \n",stn1,stn2, st_nb1,st_nb2  );
	switch(stat_kind1) {
	case 1: {
	  func1 = call_function(instruction_call(statement_instruction(s1)));
	  stn1 = strdup(entity_user_name(func1));
	  break;
	}
	case 2: {
	  stn1 = strdup("DeclarationInstruction");
	  break;
	}
	case 0:  {
	  expression rhs_exp = EXPRESSION(CAR(CDR( call_arguments(instruction_call(statement_instruction(s1))))));
	  syntax sr = expression_syntax(rhs_exp);
	  if(syntax_call_p(sr)) {
	    call rhs_call = syntax_call(sr);
	    func2=call_function(rhs_call);
	    if ((entity_subroutine_p(func2)|| entity_function_p(func2)))
	      stn1= (string) entity_local_name(call_function(rhs_call));
	    else
	      stn1 =  strdup("LocalAssignment");
	  }
	  else
	    stn1 =  strdup("LocalAssignment");
	  break;
	}
	case 3:  {
	  stn1 =  strdup("TestInstruction");
	  break;
	}
	default:
	  break;
	}
     	switch(stat_kind2) {
	case 1: {
	  func2 = call_function(instruction_call(statement_instruction(s2)));
	  stn2 = strdup(entity_user_name(func2));
	  break;
	}
	case 2: {
	  stn2 = strdup("DeclarationInstruction");
	  break;
	}
	case 0: {
	  expression rhs_exp = EXPRESSION(CAR(CDR(call_arguments(instruction_call(statement_instruction(s2))))));
	  syntax sr = expression_syntax(rhs_exp);
	  if(syntax_call_p(sr)) {
	    call rhs_call = syntax_call(sr);
	    func2=call_function(rhs_call);
	    if ((entity_subroutine_p(func2)|| entity_function_p(func2)))
	      stn2= (string) entity_local_name(call_function(rhs_call));
	    else
	      stn2 =  strdup("LocalAssignment");
	  }
	  else
	    stn2 =  strdup("LocalAssignment");
	  break;
	  break;
	}
	case 3: {
	  stn2 =  strdup("TestInstruction");
	  break;
	}
	default:
	  break;
	}
	// Create the header for dependencies for TASKREF func1
	if (!new_temp){
	  global_margin ++;
	  add_margin(global_margin,buff_computed_by_func1);
	  string_buffer_append(buff_computed_by_func1,
			       concatenate(OPENANGLE,
					   (stat_kind1>=0 && stat_kind1<=1)?"TaskRef Name=" :"Instruction Name=",QUOTE,stn1,QUOTE, BL,
					   "StNumber=",QUOTE,st_nb1,QUOTE,
					   CLOSEANGLE,NL,
					   NULL));
	  new_temp=true;
	  empty_buff_computed_by_func1=true;
	}
	if (!new_temp2){
	  add_margin(global_margin,buff_needed_from_func1);
	  string_buffer_append(buff_needed_from_func1,
			       concatenate(OPENANGLE,
					   (stat_kind2>=0 && stat_kind2<=1)?"TaskRef Name=" :"Instruction Name=",QUOTE,stn2,QUOTE, BL,
					   "StNumber=",QUOTE,st_nb2,QUOTE,
					   CLOSEANGLE,NL,
					   NULL));
	  new_temp2=true;
	  empty_buff_needed_from_func1=true;
	}
	// Scan all dependences  from Call statement S1 to Call Statement S2
	for ( pc = dg_arc_label_conflicts(dal); !ENDP(pc); pc = CDR(pc) ) {
	  conflict c = CONFLICT(CAR(pc));
	  effect efsrc = conflict_source(c);
	  effect efsrs = conflict_sink(c);
	  action acc = effect_action(efsrc);
	  action acs = effect_action(efsrs);
	  reference rc = effect_any_reference(efsrc);
	  reference rs = effect_any_reference(efsrs);
	  entity vc =  reference_variable(rc);
	  entity vs =  reference_variable(rs);

	  // DEBUG-
	  // if (( 0<=stat_kind1 && stat_kind1 <=3) && ( 0<=stat_kind2 && stat_kind2 <=3))
	  // printf( "\t\tdependence %s (%s)- %s(%s) for %s - %s \n",stn1,st_nb1,stn2,st_nb2, entity_user_name(vc), entity_user_name(vs) );

	  if (store_effect_p(efsrc) 
	      && !effects_package_entity_p(vc) && !std_file_entity_p(vc)
	      && !effects_package_entity_p(vs) && !std_file_entity_p(vs) 
	      && !string_parameter_p(vs) && !string_parameter_p(vc)
	      // && !variable_heap_p(vc) && !variable_heap_p(vs)
	      ) {

	    if (action_write_p(acc) && action_read_p(acs) && vect_coeff(vc,vwritten_func1)==0
		) {
	      //DEBUG- printf( "\t\t%s COMPUTES %s read by %s(%s)\n",stn1, entity_user_name(vc),stn2,st_nb2 );
	      global_margin++;
	      add_margin(global_margin,buff_computed_by_func1);
	      string_buffer_append(buff_computed_by_func1,
				   concatenate(OPENANGLE,
					       "Computes ",(array_entity_p(vc))?"ArrayName=": "ScalarName=",
					       QUOTE,NULL));
	     string_buffer_append_xml_text(buff_computed_by_func1,
					   (string) ((print_name_1_level_p() || reference_undefined_p(rc))?
						     entity_user_name(vc):words_points_to_reference(rc,false,region_undefined)),
					   false);
	     string_buffer_append(buff_computed_by_func1,
				   concatenate(QUOTE, BL,
					       "ReadBy=",QUOTE,stn2,QUOTE, BL,
					       "StNumber=",QUOTE,st_nb2,QUOTE,
					       "/",CLOSEANGLE,NL,
					       NULL));
	      global_margin--;
	      empty_buff_computed_by_func1=false;
	      vect_add_elem(&vwritten_func1,(Variable)vc,1);
	      vect_add_elem(&written_cumul,(Variable)vc,1);
	    }
	    if (action_write_p(acc) && action_read_p(acs)) {
	      if (vect_coeff(vc,vread_func1)==0 ) {
		//DEBUG- printf( "\t\t%s NEEDS %s DefinedBy by %s (%s)\n",stn2, entity_user_name(vc),stn1, st_nb1);

		global_margin++;
		add_margin(global_margin,buff_needed_from_func1);
		string_buffer_append(buff_needed_from_func1,
				     concatenate(OPENANGLE,
						 "Needs ",(array_entity_p(vc))?"ArrayName=": "ScalarName=",
						 QUOTE, NULL));
		string_buffer_append_xml_text(buff_needed_from_func1,
					      (string) ((print_name_1_level_p() || reference_undefined_p(rc)) ?
							entity_user_name(vc):words_points_to_reference(rc,false,region_undefined)),
					      false);
		string_buffer_append(buff_needed_from_func1,
				     concatenate(QUOTE, BL,
						 "DefinedBy=",QUOTE,stn1,QUOTE,BL,
						 "StNumber=",QUOTE,st_nb1,QUOTE,
						 "/",CLOSEANGLE,NL,NULL));
		global_margin--;
		empty_buff_needed_from_func1=false;
		if (!entity_undefined_p(func1))
		  def_to_task_store(vc, func1);
		vect_add_elem(&vread_func1,(Variable)vc,1);
	      }
	    }

	    if (action_write_p(acc) && action_write_p(acs) && !same_string_p(stn1,stn2))
	      spear_warning(s1,"Check the dependencies before mapping",
			    "Elements of Array  %s written into two different functions %s and %s",
			    (print_name_1_level_p() || reference_undefined_p(rc)) ?
			    entity_user_name(vc):words_points_to_reference(rc,false,region_undefined), stn1,stn2);

	    //   ADD R-W Dependances
	    if (action_write_p(acs) && action_read_p(acc)) {
	      //DEBUG- printf( "\t\t%s COMPUTES %s read by %s(%s)\n",stn1, entity_user_name(vc),stn2,st_nb2 );
	      global_margin++;
	      add_margin(global_margin,buff_computed_by_func1);
	      string_buffer_append(buff_computed_by_func1,
				   concatenate(OPENANGLE,
					       "Reads ",(array_entity_p(vc))?"ArrayName=": "ScalarName=",
					       QUOTE,NULL));
	      string_buffer_append_xml_text(buff_computed_by_func1,
					    (string) ((print_name_1_level_p() || reference_undefined_p(rc))?
						      entity_user_name(vc):words_points_to_reference(rc,false,region_undefined)),
					    false);
	      string_buffer_append(buff_computed_by_func1,
				   concatenate(QUOTE, BL,
					       "WrittenAfterBy=",QUOTE,stn2,QUOTE, BL,
					       "StNumber=",QUOTE,st_nb2,QUOTE,
					       "/",CLOSEANGLE,NL,
					       NULL));
	      global_margin--;
	      empty_buff_computed_by_func1=false;
	    }
	  }
	}  // end scanning dependencies
      } // end dependency filter

      if (new_temp2) {
	string_buffer_append_word((stat_kind2>=0 && stat_kind2<=1)?"/TaskRef":"/Instruction",buff_needed_from_func1); 
	if  (!empty_buff_needed_from_func1) {
	  string_temp =string_buffer_to_string(buff_needed_from_func1);
	  string_buffer_append(buff_cumul_needed,string_temp);
	  empty_buff_cumul_needed=false;
	  string_buffer_free(&buff_needed_from_func1);
	}
	new_temp2=false;
	empty_buff_needed_from_func1=true;
      }
    } // end scan func2

    if (new_temp) {
      string_buffer_append_word((stat_kind1>=0 && stat_kind1<=1)?"/TaskRef":"/Instruction",buff_computed_by_func1);
      global_margin--;
    }
    if (new_cond && !new_temp) {
      global_margin--;
    }
    if (!empty_buff_computed_by_func1) {
      if (statif != STACK_NULL) {
	for (int tp=1;tp<=nb_cond;tp++) {
	  string_buffer_append_word("/Condition",buff_computed_by_func1);
	  global_margin--;
	}
	string_temp =string_buffer_to_string(buffer_cond);
	string_buffer_append(sb_result,string_temp);
      }
      string_temp =string_buffer_to_string(buff_computed_by_func1);
      string_buffer_append(sb_result,string_temp);

      string_temp=NULL;
      new_temp=false;
      empty_buff_computed_by_func1=true;
    }
    else  {
      string_buffer_free(&buff_computed_by_func1);
      //  string_buffer_free(&buffer_cond);
    }

    // Add Read effects on variable written outside the function and Read by the local statement (in local_effects=local regions)
    if (taskNumber>=0) {
      call c1=call_undefined;
      if (instruction_call_p(statement_instruction(s1))) {
	c1 = instruction_call(statement_instruction(s1));
      }
      else { // The call is encapsulated
	encapsulated_call =call_undefined;
	gen_recurse(s1, call_domain, gen_true,search_1r_function_call);
	c1 =encapsulated_call;
      }
      if (c1!=call_undefined) {
	//	pips_internal_error("Unexpected call in statement number %d \n",(int) statement_number(s1));

	sc = gen_array_item(nest->nested_call,taskNumber);
	indices = gen_array_item(nest->nested_loop_indices,taskNumber);
	statif = gen_array_item(nest->nested_if,taskNumber);

      
	func1 = call_function(c1);
	const char *temp = (ENTITY_ASSIGN_P(func1))?"LocalAssignment":entity_user_name(func1);
	stn1 = strdup(temp);
	st_nb1=int2a(statement_number(s1));
	for (pc= local_effects;!ENDP(pc); pc = CDR(pc)){
	  effect e2 = EFFECT(CAR(pc));
	  reference r2 = effect_any_reference(e2);
	  action ac2 = effect_action(e2);
	  entity v2 =  reference_variable(r2);
	  Pcallst t=hash_get(hash_entity_def_into_tasks,(char *) v2);
	  bool b=(t!=(Pcallst) HASH_UNDEFINED_VALUE);

	  if ( store_effect_p(e2) && action_read_p(ac2)
	       && !effects_package_entity_p(v2) && !std_file_entity_p(v2) && !variable_heap_p(v2)
	       // variable written outside the function
	       &&  (vect_coeff(v2,vwritten_func1)==0 || (vect_coeff(v2,vwritten_func1)!=0 &&b ))
	       // only if not yet mentioned in the dependencies list or in the local_effects list
	       &&  vect_coeff(v2,vread_func1)==0
	       && !(entity_static_variable_p(v2) && !top_level_entity_p(v2))
	       && vect_coeff(v2,written_cumul)==0 && !(indice_p(indices,v2))
	       && !string_parameter_p(v2)//  && (b && t->stat_nb<statement_number(s1))
	       ) {	

	    // Conditional information around the dependencies
	    string_temp =string_buffer_to_string(buffer_cond);
	    string_buffer_append(sb_result,string_temp);


	    global_margin++;
	    add_margin(global_margin,sb_result);
	    string_buffer_append(sb_result,
				 concatenate(OPENANGLE,
					     "TaskRef Name=",QUOTE, stn1,QUOTE, BL,
					     "StNumber=",QUOTE,st_nb1,QUOTE,
					     CLOSEANGLE,NL,
					     NULL));
	    global_margin++;
	    add_margin(global_margin,sb_result);
	    string_buffer_append(sb_result,
				 concatenate(OPENANGLE,
					     "Needs ",(array_entity_p(v2))?"ArrayName=": "ScalarName=",
					     QUOTE, NULL));
	    string_buffer_append_xml_text(sb_result,
					  (string) ((print_name_1_level_p() || reference_undefined_p(r2))?
						    entity_user_name(v2):words_points_to_reference(r2,false,region_undefined)),
					  false);
	    string_buffer_append(sb_result,
				 concatenate(QUOTE, BL,
					     "DefinedBy=",QUOTE,
					     //(b && t->stat_nb<statement_number(s1))?
					     // - v2 has been updated into a non-call instruction or into a call nested into other instructions.
					     // - v2 has been updated IN_PLACE
					     // - v2 has been updated into a callee
					     // ((t->stat_nb<statement_number(s1)) ? entity_user_name(t->func):"IN_PLACE"):
					     //((t->stat_nb==statement_number(s1)) ?"IN_PLACE":
					     //(!(entity_undefined_p(t->func)) ? entity_user_name(t->func) : "NestedCall")
					     //)
					     //:
					     "IN_VALUE",QUOTE,BL,
					     "StNumber=",QUOTE,(b)?int2a(t->stat_nb):int2a(0),QUOTE,
					     "/",CLOSEANGLE,NL,NULL));

	    vect_add_elem(&vread_func1,(Variable)v2,1); 
	    global_margin--; 
	    string_buffer_append_word("/TaskRef",sb_result);
	    global_margin--;

	    if (statif != STACK_NULL) {
	      for (int tp=1;tp<=nb_cond;tp++) {
		string_buffer_append_word("/Condition",sb_result);
		global_margin--;
	      }
	    }
	  }
	}
      }
      {//begin
	vect_chg_coeff(&vread_in_condition, TCST,0);
	for (Pvecteur pv= vread_in_condition;!VECTEUR_UNDEFINED_P(pv); pv = pv->succ){
	  entity ent = (entity)pv->var;
	 global_margin++;
	  add_margin(global_margin,sb_result);
	  string_buffer_append(sb_result,
			       concatenate(OPENANGLE,
					   "Instruction Name=",QUOTE, "TestInstruction",QUOTE, BL,
					   "StNumber=",QUOTE,int2a(pv->val),QUOTE,
					   CLOSEANGLE,NL,
					   NULL));
	  global_margin++;
	  add_margin(global_margin,sb_result);
	  string_buffer_append(sb_result,
			       concatenate(OPENANGLE,
					   "Needs ","ScalarName=",
					   QUOTE, NULL));
	  string_buffer_append_xml_text(sb_result,
					(string) entity_user_name(ent),
					false);
	  string_buffer_append(sb_result,
			       concatenate(QUOTE, BL,
					   "DefinedBy=",QUOTE,
					   "IN_VALUE",QUOTE,
					   //BL, "StNumber=",QUOTE,int2a(0),QUOTE,
					   "/",CLOSEANGLE,NL,NULL));
	    
	  global_margin--; 
	  string_buffer_append_word("/Instruction",sb_result);
	  global_margin--;

	   
	}
      }//end 
      vect_rm(vread_func1);
      vect_rm(vwritten_func1);
      vect_rm(vread_in_condition);
      string_buffer_free(&buffer_cond);
    }
  } // end toutes les func1
  if  (!empty_buff_cumul_needed) {
    string_temp =string_buffer_to_string(buff_cumul_needed);
    string_buffer_append(sb_result,string_temp);
    string_buffer_free(&buff_cumul_needed);
  }
  //  ADD Write effects on variables that are not used in the function
  //printf("ADD Write effects on variables that are not used in the function\n");

  for (pc= cumulated_effects_list;pc != NIL; pc = CDR(pc)){
    effect e = EFFECT(CAR(pc));
    reference r = effect_any_reference(e);
    action ac = effect_action(e);
    entity v =  reference_variable(r);
    if ( store_effect_p(e)
	 && !effects_package_entity_p(v) && !std_file_entity_p(v) && !variable_heap_p(v)
	 &&!action_read_p(ac) &&  vect_coeff(v,vw) // Write effects in the cumulated effects list
      	 && !(entity_static_variable_p(v) && !top_level_entity_p(v))
	 && vect_coeff(v,written_cumul)==0) {
      Pcallst ct2,ct1=hash_get(hash_entity_def_into_tasks,(char *) v);
      for(ct2=ct1;ct2 !=(Pcallst) HASH_UNDEFINED_VALUE && ct2 !=(Pcallst) NULL; ct2=ct2->succ)
	{
	  print_reference(r);
	  string temp =strdup(int2a(ct2->stat_nb));

	  {
	    taskNumber=-1;
	    statif = STACK_NULL;
	    for (int callnumber = 0; callnumber<(int)gen_array_nitems(nest->nested_call); callnumber++) {
	      statement s3 = gen_array_item(nest->nested_call,callnumber);
	      if (statement_number(s3) == ct2->stat_nb)
		taskNumber=callnumber;
	    }
	    if (taskNumber>=0) { 
	      sc = gen_array_item(nest->nested_call,taskNumber);
	      statif = gen_array_item(nest->nested_if,taskNumber);
	    }
	    // Conditional information around the dependencies
	    if (statif != STACK_NULL) {     
	      test_statement_of_reference=sc;
	      nb_cond=0; // to restore alignment
	      global_margin++;	  
	      STACK_MAP_X(sx, statement,
			  {  if (logic_condition_filter(sc,sx,&cond,&lhs,&rhs)) {
			      test l = instruction_test(statement_instruction(sx));
			      push_statement_on_statement_global_stack(sx);
			      statement_in_truebranch_p=false;
			      if (!statement_undefined_p(test_true(l)))
				gen_recurse(test_true(l), statement_domain, gen_true,statement_in_truebranch);
			      add_margin(global_margin,sb_result);
			      //DEBUG -   printf("Condition Branch=%s Test=\n", (statement_in_truebranch_p ? "TRUE":"FALSE"),(string)entity_user_name(cond));	 
			      string_buffer_append(sb_result,
						   concatenate(OPENANGLE,
							       "Condition Branch=", 
							       QUOTE, (statement_in_truebranch_p ? "TRUE":"FALSE"),
							       QUOTE,  BL,
							       "Test=", QUOTE, NULL));
			      string_buffer_append_xml_text(sb_result,(string)entity_user_name(cond),false);
			      string_buffer_append(sb_result,
						   concatenate(QUOTE, BL, "LHS=",QUOTE, NULL));
			      string_buffer_append_xml_text(sb_result,expression_to_string(lhs), false);
			      string_buffer_append(sb_result,
						   concatenate(QUOTE, BL, "RHS=",QUOTE, NULL));
			      string_buffer_append_xml_text(sb_result,expression_to_string(rhs), false);
			      string_buffer_append(sb_result,
						   concatenate(QUOTE, BL,
							       "StNumber=",QUOTE,int2a(statement_number(sx)),QUOTE,
							       CLOSEANGLE,NL, NULL));
			      // For special character :  string_buffer_append_xml_text(buffer_cond,exps,false);
			      global_margin++;nb_cond++;
			      (void) pop_statement_global_stack();
			    }
			  },
			  statif, 0);
	      global_margin--;	
	      if (nb_cond>0) new_cond=true;
	    }
	 
	    {
	      global_margin++;
	      add_margin(global_margin,sb_result);
	      string_buffer_append(sb_result,
				   concatenate(OPENANGLE,"TaskRef Name=",QUOTE,
					       (!entity_undefined_p(ct2->func)) ?
					       (ENTITY_ASSIGN_P(ct2->func)?"LocalAssignment":entity_user_name(ct2->func)):
					       // Variable assigned in an instruction that is not a Call; in a loop, a nested call,...
					       "NestedCall", QUOTE,
					       BL,"StNumber=",QUOTE,temp,QUOTE,
					       CLOSEANGLE,NL,
					       NULL));
	      global_margin++;
	      add_margin(global_margin,sb_result);
	      string_buffer_append(sb_result,
				   concatenate(OPENANGLE,
					       "Computes ",(array_entity_p(v))?"ArrayName=": "ScalarName=",
					       QUOTE,NULL));
	     string_buffer_append_xml_text(sb_result,
					   (string) ((print_name_1_level_p() || reference_undefined_p(r))?
						     entity_user_name(v):words_points_to_reference(r,false,region_undefined)),
					   false);
	    string_buffer_append(sb_result,
				   concatenate(QUOTE,"/", CLOSEANGLE,NL, NULL));
	       vect_add_elem(&written_cumul,(Variable)v,1);
	      global_margin--;
	      string_buffer_append_word("/TaskRef",sb_result);
	      global_margin--;
	    }
	    if (statif != STACK_NULL) {
	      for (int tp=1;tp<=nb_cond;tp++) {
		string_buffer_append_word("/Condition",sb_result);
		global_margin--;
	      }
	    }
	  }
	}
    }
  }
  global_margin--;
  string_buffer_append_word("/BoxGraph",sb_result);
  vect_rm(written_cumul);
  vect_rm(vr);
  vect_rm(vw);
}

static void xml_Chains(entity module,const char* mod_name, statement mod_stat, nest_context_p nest,string_buffer sb_result)
{
  set_ordering_to_statement(mod_stat);
  dg = (graph) db_get_memory_resource(DBR_DG, mod_name, true);
  xml_Chain_Graph(module,mod_stat,dg,nest,sb_result);
  // reset_current_module_statement();
  //  reset_current_module_entity();
  reset_ordering_to_statement();
}


static void print_call_precondition(Psysteme prec, string_buffer sb_result)
{
  //  fprintf(stdout,"DEBUG - preconditions\n");
  // sc_fprint(stdout,prec, (get_variable_name_t) entity_local_name);
  
  Pcontrainte pc;
  Pvecteur pv;

  string_buffer_append_word("CallPreconditions", sb_result);
  global_margin++;
  for (pc = prec->egalites; pc!=NULL; pc=pc->succ) {
    pv = contrainte_vecteur(pc);
    if (vect_size(pv)<=2 && vect_dimension(pv)==1){
      Pvecteur pv2=vect_copy(pv);
      int coeff = - vect_coeff(TCST,pv2);
      vect_chg_coeff(&pv2,TCST,0);
      if (!VECTEUR_UNDEFINED_P(pv2) && !VECTEUR_NUL_P(pv2)) {
	entity etmp = (entity) pv2->var;
	if (!old_value_entity_p(etmp)) {
	  entity ve=(entity) pv2->var;
	  if (!value_undefined_p(entity_initial(ve)) && value_reference_p(entity_initial(ve))) {
	    reference r = value_reference(entity_initial(ve)); 
	    entity v = reference_variable(r);
	    region reg = region_undefined; 
	    add_margin(global_margin, sb_result);
	    string_buffer_append(sb_result,
				 concatenate(OPENANGLE,
					     "Precondition Param=", QUOTE,entity_user_name(v), QUOTE,
					     " Field=", QUOTE, words_points_to_reference(r,true,reg), QUOTE,
					     " Numeric=", QUOTE,  int2a(coeff), QUOTE, SLASH, CLOSEANGLE, NL, NULL)); 
	  }
	  else {	
	    add_margin(global_margin, sb_result);
	    string_buffer_append(sb_result,
				 concatenate(OPENANGLE,
					     "Precondition Param=", QUOTE,entity_user_name(ve), QUOTE,
					     " Numeric=", QUOTE,  int2a(coeff), QUOTE,SLASH, CLOSEANGLE, NL, NULL));
	  }
	}
      }
      vect_rm(pv2);
    }
  }
  for (pc = prec->inegalites; pc!=NULL; pc=pc->succ) {
    pv = contrainte_vecteur(pc);
    if (vect_size(pv)<=2 && vect_dimension(pv)==1) {
      Pvecteur pv2 = vect_copy(pv);
      int coeff = - vect_coeff(TCST,pv2);
      vect_chg_coeff(&pv2,TCST,0);
      if (!VECTEUR_UNDEFINED_P(pv2) && !VECTEUR_NUL_P(pv2)) {
	entity etmp = (entity) pv2->var;
	if (!old_value_entity_p(etmp)) {
	  entity ve = value_to_variable(etmp);
	  int val = pv2->val;
	  if (!value_undefined_p(entity_initial(ve)) && (value_reference_p(entity_initial(ve)))) {
	    reference r = value_reference(entity_initial(ve));
	    entity v = reference_variable(r);
	    region reg = region_undefined; 
	    add_margin(global_margin, sb_result);
	    string_buffer_append(sb_result,
				 concatenate(OPENANGLE,
					     "Precondition Param=", QUOTE,entity_user_name(v), QUOTE,
					     " Field=", QUOTE, words_points_to_reference(r,true,reg), QUOTE,
					     (val<=0) ? " MinNumeric=":" MaxNumeric=", QUOTE,  int2a(coeff), QUOTE, SLASH,CLOSEANGLE, NL, NULL));
	  }
	  else {	
	    add_margin(global_margin, sb_result);
	    string_buffer_append(sb_result,
				 concatenate(OPENANGLE,
					     "Precondition Param=", QUOTE,entity_user_name(ve), QUOTE,
					     (val<=0)?" MinNumeric=":" MaxNumeric=", QUOTE,  int2a(coeff), QUOTE, SLASH,CLOSEANGLE, NL, NULL));

	  }
	}
      }
    }
  }
  global_margin--;
  string_buffer_append_word("/CallPreconditions", sb_result);
}

static void xml_Call(entity module, int code_tag,int taskNumber, nest_context_p nest, string_buffer sb_result)
{
  statement s = gen_array_item(nest->nested_call,taskNumber);
 push_statement_on_statement_global_stack(s);
   //  if (instruction_call_p(statement_instruction(s))) {
  stack st = gen_array_item(nest->nested_loops,taskNumber);
  stack statif = gen_array_item(nest->nested_if,taskNumber);
  transformer t = load_statement_precondition(s);
  Psysteme prec = sc_dup((Psysteme) predicate_system(transformer_relation(t)));
  call c = call_undefined;
  list pattern_region=NIL;
  Pvecteur paving_indices = VECTEUR_NUL;
  Pvecteur pattern_indices = VECTEUR_NUL;
  bool motif_in_te_p=false;
  bool func_as_rhs_of_assign =false;
  int nb_cond=0;
  entity cond, encapsulated_func,func ;
  expression lhs,rhs;

  if (instruction_call_p(statement_instruction(s))) {
    c = instruction_call(statement_instruction(s));
  }
  else {
    encapsulated_call =call_undefined;
    gen_recurse(s, call_domain, gen_true,search_1r_function_call);
    c =encapsulated_call;
  }
  if (c==call_undefined)
    pips_internal_error("Unexpected call in statement number %d \n",(int) statement_number(s));

  //used by statement_in_truebranch
  test_statement_of_reference=s;
  func= call_function(c);
  const char * strtmp = entity_user_name(func);

  if (ENTITY_ASSIGN_P(func) || !instruction_call_p(statement_instruction(s))) {
    pattern_region =load_proper_rw_effects_list(s);
  }
  else
    pattern_region = regions_dup(load_statement_local_regions(s));

  if (ENTITY_ASSIGN_P(func)) {
    list largs = call_arguments(c);
    expression lhs_exp = EXPRESSION(CAR(largs));
    lhs_exp = skip_field_and_cast_expression(lhs_exp);
    if (array_argument_p(lhs_exp)) // lhs not scalar
      spear_warning(s,"Please use only scalar variable on the left hand side of assignements not included in a MOTIF",
		    "Non scalar variable as LHS part of a LocalAssignment");

    FOREACH(EXPRESSION,expt,POP(largs)){
      expression arg_exp = skip_field_and_cast_expression(expt);
      if (array_argument_p(arg_exp))  // rhs not scalar
	spear_warning(s,"Please use only scalar variable on the right hand side of assignements not included in a MOTIF",
		      "Non scalar variable as RHS part of a LocalAssignment");
    }
    largs = call_arguments(c);
    if(gen_length(largs)>2)
      spear_warning(s,"Please use only one varaible on the right hand side of assignements not included in a MOTIF",
		    "More than 1 variable as RHS part of a LocalAssignment");

    if(gen_length(largs)==2) {
      POP(largs);
      expression rhs_exp = EXPRESSION(CAR(largs));
      syntax sr = expression_syntax(rhs_exp);
      if(syntax_call_p(sr)) {
	call rhs_call = syntax_call(sr);
	encapsulated_func=call_function(rhs_call);
	func_as_rhs_of_assign = (entity_subroutine_p(encapsulated_func)|| entity_function_p(encapsulated_func));
      }
      //spear_warning(s,"Please encapsulate assignments into TASK or into the existing MOTIF","LocalAssignment detected");
    }
  }
  if (statif != STACK_NULL) {
    STACK_MAP_X(sx, statement,
		{  if (logic_condition_filter(s,sx,&cond,&lhs,&rhs)) {
		    test l = instruction_test(statement_instruction(sx));
		   push_statement_on_statement_global_stack(sx);
		    statement_in_truebranch_p=false;
		    if (!statement_undefined_p(test_true(l)))
		      gen_recurse(test_true(l), statement_domain, gen_true,statement_in_truebranch);
		    add_margin(global_margin,sb_result);

		    string_buffer_append(sb_result,
					 concatenate(OPENANGLE,
						     "CallCondition Branch=",
						     QUOTE, (statement_in_truebranch_p ? "TRUE":"FALSE"),
						     QUOTE, BL,
						     "Test=", QUOTE, NULL));
		    string_buffer_append_xml_text(sb_result,(string)entity_user_name(cond),false);
		    string_buffer_append(sb_result,
					 concatenate(QUOTE, BL,
						     "LHS=",QUOTE, NULL));
		    string_buffer_append_xml_text(sb_result,expression_to_string(lhs),false);
		    string_buffer_append(sb_result,
					 concatenate(QUOTE, BL, "RHS=",QUOTE, NULL));
		    string_buffer_append_xml_text(sb_result, expression_to_string(rhs), false);
		    string_buffer_append(sb_result,
					 concatenate(QUOTE,BL,
						     "StNumber=",QUOTE,int2a(statement_number(sx)),QUOTE,
						     CLOSEANGLE,NL, NULL));
		     // For special character :  string_buffer_append_xml_text(buffer_cond,exps,false);
		    global_margin++;nb_cond++;
		    (void) pop_statement_global_stack();
		  }
		},
		statif, 0);
  }
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,
				   "Call Name=",
				   QUOTE,
				   ENTITY_ASSIGN_P(func) ? (
							    (func_as_rhs_of_assign) ? entity_user_name(encapsulated_func):
							    "LocalAssignment")
				   : entity_user_name(func),
				   QUOTE,BL,
				   "StNumber=",QUOTE,int2a(statement_number(s)),QUOTE,
				   CLOSEANGLE,NL, NULL)); 
  global_margin++;
  print_call_precondition(prec, sb_result);
  //  only detect  Opengpu 2D and 3D 4D and 5D cornerturns
  if (strstr(strtmp,"cornerturn_5D")!=NULL)
    xml_Transposition(s,c,5,sb_result,0);
  else if (strstr(strtmp,"cornerturn_4D")!=NULL)
    xml_Transposition(s,c,4,sb_result,0);
  else if (strstr(strtmp,"cornerturn_3D")!=NULL)
    xml_Transposition(s,c,3,sb_result,0);
  else
    if (strstr(strtmp,"cornerturn_2D")!=NULL)
      xml_Transposition(s,c,2,sb_result,0);

  if (strstr(strtmp,"transpose_5D")!=NULL)
    xml_Transposition(s,c,5,sb_result,1);
  else if (strstr(strtmp,"transpose_4D")!=NULL)
    xml_Transposition(s,c,4,sb_result,1);
  else if (strstr(strtmp,"transpose_3D")!=NULL)
    xml_Transposition(s,c,3,sb_result,1);
  else
    if (strstr(strtmp,"transpose_2D")!=NULL)
      xml_Transposition(s,c,2,sb_result,1);
  xml_Region_Parameter(pattern_region, sb_result);
  xml_Loops(st,true,&pattern_region,&paving_indices, &pattern_indices,motif_in_te_p, sb_result);
  if (ENTITY_ASSIGN_P(func) && !func_as_rhs_of_assign)
    xml_TaskParameters(s,true,code_tag, module,pattern_region,paving_indices,sb_result);
  else // it may be an assignment but with a (non intrinsic) function  at the RHS
    xml_Arguments(s,func,statement_number(s),ENTITY_ASSIGN_P(func), paving_indices, t, prec,sb_result);
  global_margin--;
  string_buffer_append_word("/Call",sb_result);

  if (statif != STACK_NULL) {
    for (int tp=1;tp<=nb_cond;tp++) {
      global_margin--;
      string_buffer_append_word("/CallCondition",sb_result);
    }
  }
  pop_statement_global_stack();
  sc_free(prec);
}

static void  xml_Compute_and_Need(
  entity func,list effects_list, Pvecteur vargs,string_buffer sb_result)
{
  string_buffer buffer_needs = string_buffer_make(true);
  string string_needs = "";
  Pvecteur vr = VECTEUR_NUL,vw = VECTEUR_NUL;
  list pc;
  Pvecteur va2 = vect_dup(vargs);

  vars_read_and_written(effects_list,&vr,&vw);

  for (pc= effects_list;pc != NIL; pc = CDR(pc)){
    effect e = EFFECT(CAR(pc));
    reference r = effect_any_reference(e);
    action ac = effect_action(e);
    entity v = reference_variable(r);
    // get last function which modified v, if any...
    entity t = def_to_task_get(v);
    if ( store_effect_p(e)
	 && !effects_package_entity_p(v) && !std_file_entity_p(v) && !variable_heap_p(v)
	 // To avoid the multiple references to the same user array (Array of struct,  Read-Written arrays, ..)
	 && action_read_p(ac) && vect_coeff(v,vr) && ((vect_coeff(v,vw) && (t != NULL)) || !vect_coeff(v,vw) )
	 // to avoid private variables
	 && !(entity_static_variable_p(v) && !top_level_entity_p(v))
	 && !string_parameter_p(v)) {
      vect_chg_coeff(&vr,v,0);
      global_margin++;
      add_margin(global_margin,buffer_needs);
      string_buffer_append(buffer_needs,
			   concatenate(OPENANGLE,
				       "Needs ",(array_entity_p(v))?"ArrayName=": "ScalarName=",
				       QUOTE,NULL));
      string_buffer_append_xml_text(buffer_needs,(string) entity_user_name(v),false);
      string_buffer_append(buffer_needs,
			   concatenate(QUOTE, BL,
				       "DefinedBy=",QUOTE,
				       (t != NULL) ? entity_local_name(t): "IN_VALUE",QUOTE,"/",
				       CLOSEANGLE,NL,NULL));
      global_margin--;
    }
  }
  for (pc= effects_list;pc != NIL; pc = CDR(pc)){
    effect e = EFFECT(CAR(pc));
    reference r = effect_any_reference(e);
    action ac = effect_action(e);
    entity v =  reference_variable(r);
    if ( store_effect_p(e) && !effects_package_entity_p(v) && !std_file_entity_p(v) && !variable_heap_p(v)
	 // to avoid private variables and the multiple references to the same user array (Array of struct, ..)
	 &&!action_read_p(ac) &&  vect_coeff(v,vw)
      	 && !(entity_static_variable_p(v) && !top_level_entity_p(v))) {
      vect_chg_coeff(&vw,v,0);
      global_margin++;
      add_margin(global_margin,sb_result);
      string_buffer_append(sb_result,
			   concatenate(OPENANGLE,
				       "Computes ",(array_entity_p(v))?"ArrayName=": "ScalarName=",
				       QUOTE,NULL));
      string_buffer_append_xml_text(sb_result,(string) entity_user_name(v),false);
     string_buffer_append(sb_result,
			   concatenate(QUOTE,"/", CLOSEANGLE,NL,NULL));
      def_to_task_store(v, func);
      global_margin--;
    }
  }

  vect_rm(va2);
  string_needs =string_buffer_to_string(buffer_needs);
  string_buffer_append(sb_result,string_needs);
  free(string_needs);
  string_needs=NULL;
}

static int find_code_status(const char* module_name)
{
  statement stat=(statement) db_get_memory_resource(DBR_CODE,
						    module_name, true);
  bool wmotif = false;
  bool wbox = false;
  motif_in_statement_p = false;
  gen_recurse(stat, statement_domain, gen_true, motif_in_statement);
  wmotif = motif_in_statement_p;
  box_in_statement_p = false;
  gen_recurse(stat, statement_domain, gen_true, box_in_statement);
  wbox = box_in_statement_p;

  if (same_string_p(module_name, get_string_property("XML_APPLICATION_MAIN")))
    return code_is_a_main;
  else {
    if (wmotif && !wbox)
      return code_is_a_te;
    else
      return code_is_a_box;
  }
}

static void xml_Boxes(const char* module_name, int code_tag,string_buffer sb_result)
{
  entity module = module_name_to_entity(module_name);
  statement stat = get_current_module_statement();
  string_buffer type_buffer = string_buffer_make(true);
  string string_types;
  Psysteme prec = SC_UNDEFINED;
  transformer t = first_precondition_of_module(module_name, &prec);
  nest_context_t nest;
  int st_nb1=0, st_sauv=0;
  Pvecteur pv=VECTEUR_NUL;
  push_statement_on_statement_global_stack(stat);
  nest.loops_for_call = stack_make(statement_domain,0,0);
  nest.loop_indices = stack_make(entity_domain,0,0);
  nest.current_stat = stack_make(statement_domain,0,0);
  nest.testif = stack_make(statement_domain,0,0);
  nest.nested_if=  gen_array_make(0);
  nest.nested_loops=  gen_array_make(0);
  nest.nested_loop_indices =  gen_array_make(0);
  nest.nested_call=  gen_array_make(0);

  global_margin++;
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,
				   "Box Name=", QUOTE,module_name,QUOTE,
				   CLOSEANGLE,NL, NULL));
  global_margin++;
  global_application_variables=VECTEUR_NUL;
  local_application_variables=VECTEUR_NUL;
  if (!entity_main_module_p(module)) {
    xml_GlobalVariables(t,prec,true,sb_result);
    xml_LocalVariables(module,t,prec,sb_result);
    xml_FormalVariables(module,t,prec,sb_result);
  }
  else {
        xml_GlobalVariables(t,prec,false,sb_result);
	//string_buffer_append_word("GlobalVariables/",sb_result);
    xml_LocalVariables(module,t,prec,sb_result);
    string_buffer_append_word("FormalVariables/",sb_result);
  }

  /*CA*/
  vect_erase_var(&global_application_variables, TCST);
  vect_erase_var(&local_application_variables, TCST);
  string_buffer_append_word("GlobalReferencedTypes",type_buffer);
  global_margin++;
  for (pv = global_application_variables;pv!=NULL;pv=pv->succ) {
    xml_Type_Entity((entity)pv->var,type_buffer);
  }
  /* for validation */
  global_margin--;
  string_buffer_append_word("/GlobalReferencedTypes",type_buffer);
  string_buffer_append_word("LocalReferencedTypes",type_buffer);
  global_margin++;

  for (pv = local_application_variables;pv!=NULL;pv=pv->succ) {
    xml_Type_Entity((entity)pv->var,type_buffer);
  }
  global_margin--;
  string_buffer_append_word("/LocalReferencedTypes",type_buffer);
  string_types =string_buffer_to_string(type_buffer);
  string_buffer_append(sb_result,string_types);
  free(string_types);

  /*CA*/
  /* Search calls in Box */
  find_loops_and_calls_in_box(stat,&nest);
  int nb_call = (int)gen_array_nitems(nest.nested_call);
  for (int callnumber = 0; callnumber<nb_call; callnumber++) {
    statement st= gen_array_item(nest.nested_call,callnumber);
    st_nb1 = statement_number(st);
    // to deal with nested calls in the same instruction
    if (callnumber==0 || st_nb1!=st_sauv)
      xml_Call(module, code_tag, callnumber, &nest,sb_result);
    st_sauv=st_nb1;
  }

  // xml_BoxGraph(module,&nest,sb_result);
  xml_Chains(module, module_name,stat,&nest,sb_result);
  global_margin--;
  string_buffer_append_word("/Box",sb_result);

  /* AGGREGATION TRANSFERED TO "tspear"
   *
   * string_buffer_append_word("Tasks",sb_result);
   * insert_xml_callees(module_name);
   * string_buffer_append_word("/Tasks",sb_result);
   */

  global_margin--;
  gen_array_free(nest.nested_loops);
  gen_array_free(nest.nested_loop_indices);
  gen_array_free(nest.nested_call);
  gen_array_free(nest.nested_if);
  stack_free(&(nest.testif));
  stack_free(&(nest.loops_for_call));
  stack_free(&(nest.loop_indices));
  stack_free(&(nest.current_stat));
  pop_statement_global_stack();
  sc_free(prec);
}


static void xml_Application(
  const char* module_name,
  int code_tag,
  string_buffer sb_result)
{
  entity module = module_name_to_entity(module_name);
  statement s = get_current_module_statement();
  Psysteme prec = SC_UNDEFINED;
  transformer t = first_precondition_of_module(module_name, &prec);
  Pvecteur vargs = VECTEUR_NUL;

  pips_assert("code is a main", code_tag == code_is_a_main);

  global_margin = 0;
  // <Application ...>
  string_buffer_append(sb_result, concatenate(
    OPENANGLE, "Application Name=", QUOTE, get_current_module_name(), QUOTE, BL,
    "Language=",QUOTE, (fortran_appli)? "FORTRAN": "C", QUOTE, BL,
    "PassingMode=", QUOTE,(fortran_appli)? "BYREFERENCE": "BYVALUE", QUOTE,
    CLOSEANGLE, NL, NULL));

  global_margin ++;

  //   IncludedFiles will be written here
  add_margin(global_margin, sb_result);
  string_buffer_append(sb_result, "<!-- Included Files -->" NL);

  //   <GlobalVariables>...</GlobalVariables>
  xml_GlobalVariables( t, prec, true, sb_result);

  //   Box/Task will be written here
  add_margin(global_margin, sb_result);
  string_buffer_append(sb_result, "<!-- Main Box -->" NL);

  //   <ApplicationGraph>
  add_margin(global_margin, sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,
				   "ApplicationGraph Name=", QUOTE, module_name, QUOTE,
				   CLOSEANGLE,NL, NULL));

  //     <TaskRef>
  global_margin ++;
  add_margin(global_margin,sb_result);
  string_buffer_append(sb_result,
		       concatenate(OPENANGLE,
				   "TaskRef Name=", QUOTE,entity_user_name(module), QUOTE,
				   CLOSEANGLE,NL,NULL));

  cumulated_list = NIL;
  gen_recurse(s, statement_domain, gen_true, cumul_effects_of_statement);
  xml_Compute_and_Need(module,cumulated_list, vargs, sb_result);

  //     </TaskRef>
  string_buffer_append_word("/TaskRef", sb_result);
  global_margin --;

  //   </ApplicationGraph>
  string_buffer_append_word("/ApplicationGraph", sb_result);
  global_margin --;

  // </Application>
  string_buffer_append_word("/Application", sb_result);

  sc_free(prec);
}

/******************************************************** PIPSMAKE INTERFACE */

static bool generic_print_xml_application(const char* module_name, bool is_app)
{
  FILE * out;
  entity module;
  string dir, filename;
  statement stat;
  string_buffer sb_result = string_buffer_make(true);
  int code_tag;
  string resource = is_app? DBR_SPEAR_APP_FILE : DBR_SPEAR_CODE_FILE;

  // globals...
  hash_entity_def_into_tasks = hash_table_make(hash_pointer,0);

  module = module_name_to_entity(module_name);
  string xml = db_build_file_resource_name
    (resource, module_name, is_app? ".app.xml": ".xml");
  dir = db_get_current_workspace_directory();
  filename = strdup(concatenate(dir, "/", xml, NULL));
  stat = (statement) db_get_memory_resource(DBR_CODE, module_name, true);
  make_statement_global_stack();
  set_current_module_entity(module);
  set_current_module_statement(stat);
  if(statement_undefined_p(stat)) {
    pips_internal_error("No statement for module %s", module_name);
  }
  set_proper_rw_effects((statement_effects)
			db_get_memory_resource(DBR_PROPER_EFFECTS,
					       module_name,true));
  set_cumulated_rw_effects((statement_effects)
		      db_get_memory_resource(DBR_CUMULATED_EFFECTS,
					       module_name,true));
  init_cost_table();
  // set_complexity_map( (statement_mapping)
  //		      db_get_memory_resource(DBR_COMPLEXITIES, module_name, true));

  /* Get the READ and WRITE regions of the module */
  set_rw_effects((statement_effects)
		 db_get_memory_resource(DBR_REGIONS, module_name, true));

  set_precondition_map((statement_mapping)
		       db_get_memory_resource(DBR_PRECONDITIONS,
					      module_name,
					      true));

  module_to_value_mappings(get_current_module_entity());

  debug_on("XMLPRETTYPRINTER_DEBUG_LEVEL");
  out = safe_fopen(filename, "w");
  code_tag = find_code_status(module_name);
  fprintf(out,"%s<!-- XML prettyprint for %s \"%s\" --> \n",
          is_app? "": "  ",
          is_app? "application": code_tag == code_is_a_te? "task": "box",
          module_name);

  if (is_app)
    def_to_task_set((entity_to_entity)
                    db_get_memory_resource(DBR_TASK_VARIABLE_CHANGED_BY,
                                           module_name, true));
  else
    def_to_task_init();

  fortran_appli = fortran_module_p(module);

  if (is_app)
  {
    pips_assert("application is a main", code_tag == code_is_a_main);
    xml_Application(module_name, code_tag, sb_result);
  }
  else
  {
    switch (code_tag)
    {
    case code_is_a_main:
    case code_is_a_box:
      // xml_Boxes(module_name, code_is_a_main, sb_result);
      xml_Boxes(module_name, code_tag, sb_result);
      break;
    case code_is_a_te:
      xml_Task(module_name, code_tag, sb_result);
      break;
    default:
      pips_internal_error("unexpected kind of code for xml_prettyprinter");
    }
  }

  pips_debug(1, "End XML prettyprinter for %s\n", module_name);
  debug_off();

  string sr = string_buffer_to_string(sb_result);
  fputs(sr, out);
  free(sr);
  safe_fclose(out, filename);

  string_buffer_free(&sb_result);
  hash_table_free(hash_entity_def_into_tasks), hash_entity_def_into_tasks = NULL;
  free(dir);
  free(filename);

  DB_PUT_FILE_RESOURCE(resource, module_name, xml);
  if (!is_app)
    DB_PUT_MEMORY_RESOURCE(DBR_TASK_VARIABLE_CHANGED_BY, module_name,
                           def_to_task_mapping);

  def_to_task_reset();
  free_statement_global_stack();
  reset_current_module_statement();
  reset_current_module_entity();
  reset_complexity_map();
  reset_precondition_map();
  reset_rw_effects();
  reset_proper_rw_effects();
  reset_cumulated_rw_effects();
  free_value_mappings();
  return true;
}

bool print_xml_application_with_points_to(const char* module_name)
{
  set_pt_to_list( (statement_points_to)
		  db_get_memory_resource(DBR_POINTS_TO, module_name, true) );
  bool result = generic_print_xml_application(module_name, false);
  reset_pt_to_list();
  return result;
}

bool print_xml_application(const char* module_name)
{
  bool result = generic_print_xml_application(module_name, false);
  return result;
}

bool print_xml_application_main(const char* module_name)
{
  bool result = generic_print_xml_application(module_name, true);
  return result;
}
bool print_xml_application_main_with_points_to(const char* module_name)
{
  set_pt_to_list( (statement_points_to)
		   db_get_memory_resource(DBR_POINTS_TO, module_name, true) );
  bool result = generic_print_xml_application(module_name, true);
  reset_pt_to_list();
  return result;
}
