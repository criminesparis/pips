/*

  $Id: module.c 22599 2015-07-13 07:12:41Z irigoin $

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

// strndup are GNU extensions...
#include <stdio.h>
#include <string.h>

#include "genC.h"
#include "text.h"
#include "constants.h"

#include "text-util.h"
#include "misc.h"
#include "linear.h"
#include "ri.h"
#include "ri-util.h"
#include "pipsdbm.h"
#include "workspace-util.h"

/* High-level functions about modules, using pipsdbm and ri-util and
   some global variables assumed properly set
 */

/* Retrieve all declarations linked to a module, but the local
   variables private to loops. Allocate and build a new list which
   will have to be freed by the caller.

   This function has been implemented twice.

   It may be useless because code_declarations() is supposed to
   contain all module declarations, regardless of where the
   declarations happens.
 */
list module_declarations(entity m)
{
  list dl = get_current_module_declarations();
  if (list_undefined_p(dl))
    {
      dl = code_declarations(value_code(entity_initial(m)));
      set_current_module_declarations(dl);
    }  

  /* FI: maybe we should also look up the declarations in the compilation unit... */

  ifdebug(9) {
    pips_debug(8, "Current module declarations:\n");
    print_entities(dl);
    fprintf(stderr, "\n");
  }

  return gen_copy_seq(dl);
}

list current_module_declarations()
{
  entity m = get_current_module_entity();
  return module_declarations(m);
}

/* Return a list of all variables and functions accessible somewhere in a module. */
list module_entities(entity m)
{
  entity cu = module_entity_to_compilation_unit_entity(m);
  list cudl = gen_copy_seq(code_declarations(value_code(entity_initial(cu))));
  list mdl = module_declarations(m);

  pips_assert("compilation unit is an entity list.",
	      entity_list_p(code_declarations(value_code(entity_initial(cu)))));
  pips_assert("initial cudl is an entity list.", entity_list_p(cudl));
  pips_assert("mdl is an entity list.", entity_list_p(mdl));

  cudl = gen_nconc(cudl, mdl);

  /* Make sure you only have entities in list cudl */
  pips_assert("Final cudl is an entity list.", entity_list_p(cudl));

  return cudl;
}

/* Retrieve the compilation unit containing a module definition.
 *
 * The implementation is clumsy.
 *
 * It would be nice to memoize the information as with
 * get_current_module_entity().
 *
 * It would be much nicer to keep a resource like INPUT_FILE_NAME, say
 * COMPILATION_UNIT_NAME.
 *
 * The entity returned may be undefined.
 */
entity module_entity_to_compilation_unit_entity(entity m)
{
  entity cu = entity_undefined;

  if(compilation_unit_entity_p(m))
    cu = m;
  else if(!db_resource_p(DBR_USER_FILE, module_local_name(m))) {
    /* The resource does not always exist.
     *
     * For Fortran code to start with.
     *
     * For synthesized code too: initializer, outliner... (although
     * pass outline might build a compilation unit...
     *
     * Let's assume that synthesized module "foo" has "foo!" a
     * compilation unit name and it never is a static function.
     */
    string name = strdup(concatenate(entity_name(m), FILE_SEP_STRING, NULL));
    cu = gen_find_tabulated(name, entity_domain);
  }
  else {
    // string aufn = db_get_memory_resource(DBR_USER_FILE, entity_user_name(m), true);
    string aufn = db_get_memory_resource(DBR_USER_FILE, module_local_name(m), true);
    string lufn = strrchr(aufn, '/')+1;

    if(lufn!=NULL) {
      string n = strstr(lufn, PP_C_ED);
      int l = n-lufn;
      string cun = strndup(lufn, l);

      if(static_module_name_p(cun)) {
	string end = strrchr(cun, FILE_SEP_CHAR);
	*(end+1) = '\0';
	cu = local_name_to_top_level_entity(cun);
      }
      else {
	string ncun = strdup(concatenate(cun, FILE_SEP_STRING, NULL));
	cu = local_name_to_top_level_entity(ncun);
	free(ncun);
      }
      free(cun);
    }
    else
      pips_internal_error("Not implemented yet");
  }
  pips_assert("If defined, cu is a compilation unit",
	      entity_undefined_p(cu) || compilation_unit_entity_p(cu));
  return cu;
}

bool language_module_p(entity m, string lid)
{
  bool c_p = false;

  if(entity_module_p(m)) {
    /* FI: does not work with static functions */
    //string aufn = db_get_memory_resource(DBR_USER_FILE, entity_user_name(m), true);
    /* SG: must check if the ressource exist (not always the case) */
    const char* lname= module_local_name(m);
    if( db_resource_p(DBR_USER_FILE,lname) )
    {
        string aufn = db_get_memory_resource(DBR_USER_FILE, module_local_name(m), true);
        string n = strstr(aufn, lid);

        c_p = (n!=NULL);
    }
    else
        c_p = true; /* SG: be positive ! (needed for Hpfc)*/
  }
  return c_p;
}

/** Add an entity to the current's module compilation unit declarations
 * we have to generate its statement if none created before
 * due to limitation of pipsmake, it is not always possible to make sure from pipsmake
 * that this ressource is created.
 * For example in INLINING (!) we would like to tell pipsmake
 * we need the CODE resource from all module callers.
 *
 * @param[in] e is the entity to add
 * @param[in] cu is the compilation unit
 */
void AddEntityToCompilationUnit(entity e, entity cu ) {
    statement s = statement_undefined;
    const char* cum = module_local_name(cu);
    if( c_module_p(cu) ) {
        if(!db_resource_required_or_available_p(DBR_PARSED_CODE,cum))
        {
            bool compilation_unit_parser(const char*);
            entity tmp = get_current_module_entity();
            statement stmt = get_current_module_statement();
            reset_current_module_entity();
            reset_current_module_statement();
            compilation_unit_parser(cum);
            if(!entity_undefined_p(tmp))
                set_current_module_entity(tmp);
            if(!statement_undefined_p(stmt))
                set_current_module_statement(stmt);
        }
        if(!db_resource_required_or_available_p(DBR_CODE,cum))
        {
            bool controlizer(const char*);
            entity tmp = get_current_module_entity();
            statement stmt = get_current_module_statement();
            reset_current_module_entity();
            reset_current_module_statement();
            controlizer(cum);
            if(!entity_undefined_p(tmp))
                set_current_module_entity(tmp);
            if(!statement_undefined_p(stmt))
                set_current_module_statement(stmt);
        }
        s=(statement)db_get_memory_resource(DBR_CODE,cum,true);
    }
    /* SG: when adding a new entity to compilation unit,
     * one should check the entity is not already present
     * but an entity with the same name may already be defined there
     * so check this with a very costly test*/
    list cu_entities = entity_declarations(cu);
    FOREACH(ENTITY,cue,cu_entities)
        if(same_string_p(entity_user_name(e),entity_user_name(cue)))
            return;
    AddLocalEntityToDeclarations(e,cu,s);
    if( c_module_p(cu) ) {
        module_reorder(s);
        db_put_or_update_memory_resource(DBR_CODE,cum,s,true);
        db_touch_resource(DBR_CODE,cum);
        if( typedef_entity_p(e) ) {
	  //keyword_typedef_table = (hash_table)db_get_memory_resource(DBR_DECLARATIONS, cum, true);
	  //put_new_typedef(entity_user_name(e));
	  // FI: I do not see why the global variable of the parsers should be reused here
	  // hash_table keyword_typedef_table = (hash_table)db_get_memory_resource(DBR_DECLARATIONS, cum, true);
	  set_keyword_typedef_table((hash_table) db_get_memory_resource(DBR_DECLARATIONS, cum, true));
	  //hash_put(keyword_typedef_table,strdup(cum),(void *) TK_NAMED_TYPE);
	  // FI; temporary
	  //hash_put(keyword_typedef_table,strdup(cum),(void *) 262);
	  declare_new_typedef((string) entity_user_name(e));
	  //SG: we have to do this behind the back of pipsmake. Not Good for serialization, but otherwise it forces the recompilation of the parsed_code of the associated modules, not good :(
	  //DB_PUT_MEMORY_RESOURCE(DBR_DECLARATIONS, cum, keyword_typedef_table);
        }

    }
}

/** Remove an entity from the current's module compilation unit declarations
 *
 * @param[in] e is the entity to remove
 * @param[in] cu is the compilation unit
 */
void RemoveEntityFromCompilationUnit(entity e, entity cu ) {
    statement s = statement_undefined;
    const char* cum = module_local_name(cu);
    if( c_module_p(cu) ) {
        if(!db_resource_required_or_available_p(DBR_CODE,cum))
        {
            bool controlizer(const char*);
            entity tmp = get_current_module_entity();
            statement stmt = get_current_module_statement();
            reset_current_module_entity();
            reset_current_module_statement();
            controlizer(cum);
            if(!entity_undefined_p(tmp))
                set_current_module_entity(tmp);
            if(!statement_undefined_p(stmt))
                set_current_module_statement(stmt);
        }
        s=(statement)db_get_memory_resource(DBR_CODE,cum,true);
    }

    // Remove entity from global declaration lists
    gen_remove(&entity_declarations(cu),e);
    // FIXME : s is only defined for c_module !!
    gen_remove(&statement_declarations(s),e);

    remove_declaration_statement(s, e);
    if( c_module_p(cu) ) {
        module_reorder(s);
        db_put_or_update_memory_resource(DBR_CODE,cum,s,true);
        db_touch_resource(DBR_CODE,cum);
    }
}



void
AddEntityToModuleCompilationUnit(entity e, entity module)
{
    list tse = type_supporting_entities(NIL,entity_type(e));
    entity cu = module_entity_to_compilation_unit_entity(module);
    FOREACH(ENTITY,se,tse) {
        const char * eln = entity_local_name(se);
        if(strstr(eln, DUMMY_STRUCT_PREFIX) || strstr(eln, DUMMY_UNION_PREFIX) ) {
            continue;
        }
        AddEntityToCompilationUnit(se,cu);
    }
    gen_free_list(tse);
    AddEntityToCompilationUnit(e,cu);
}

/*
   For C, the declaration in the module statements are added.

   Because this function relies on pipsdbm, it should be relocated
   into another library. Prime candidate is preprocessor : - (
 */

list module_to_all_declarations(entity m)
{
  list dl = CONS(ENTITY, m, gen_copy_seq(code_declarations(value_code(entity_initial(m)))));
  bool c_module_p(entity);

  if(c_module_p(m)) {
    //const char* module_name = entity_user_name(m);
    const char* module_name = entity_local_name(m);
    statement s = (statement) db_get_memory_resource(DBR_PARSED_CODE, module_name, true);
    list sdl = statement_to_declarations(s);

    FOREACH(ENTITY, e, sdl) {
      if(!entity_is_argument_p(e, dl))
	dl = gen_nconc(dl, CONS(ENTITY, e, NIL));
    }
    gen_free_list(sdl);
  }

  return dl;
}

/* The output is undefined if the module is referenced but not defined in
 * the workspace, for instance because its code should be synthesized.
 *
 * Fabien Coelho suggests to build a default compilation unit where all
 * synthesized module codes would be located.
 */
string compilation_unit_of_module(const char* module_name)
{
  entity e = module_name_to_entity(module_name);
  pips_assert("only for C modules\n", entity_undefined_p(e) || c_module_p(e));

  // Should only be called for C modules.
  string compilation_unit_name = string_undefined;

  // The guard may not be sufficient...
  // and this may crash in db_get_memory_resource()
  if(db_resource_p(DBR_USER_FILE, module_name)) {
    string source_file_name =
      db_get_memory_resource(DBR_USER_FILE, module_name, true);
    string simpler_file_name = pips_basename(source_file_name, PP_C_ED);

    // It is not clear how robust it is going to be
    // when file name conflicts occur.
    (void) asprintf(&compilation_unit_name, "%s" FILE_SEP_STRING,
                    simpler_file_name);
    free(simpler_file_name);
  }

  return compilation_unit_name;
}

/* To be checked for static functions... */
string module_name_to_input_file_name(const char* module_name)
{
  entity e = module_name_to_entity(module_name);
  pips_assert("only for C modules\n", entity_undefined_p(e) || c_module_p(e));

  // Should only be called for C modules.
  string input_file_name = string_undefined;

  // The guard may not be sufficient...
  // and this may crash in db_get_memory_resource()
  if(db_resource_p(DBR_USER_FILE, module_name)) {
    string source_file_name =
      db_get_memory_resource(DBR_USER_FILE, module_name, true);
    string simpler_file_name = pips_basename(source_file_name, PP_C_ED);

    // It is not clear how robust it is going to be
    // when file name conflicts occur.
    (void) asprintf(&input_file_name, "%s/" WORKSPACE_SRC_SPACE "/%s.c",
                    db_get_current_workspace_directory(), simpler_file_name);
    free(simpler_file_name);
  }

  return input_file_name;
}
