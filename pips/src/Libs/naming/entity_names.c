/*

  $Id:naming.c$

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

#include "genC.h"
#include "misc.h"
#include "naming.h"

/* The names of PIPS entities carry information about their nature. A
 * lot of string-based functions are used to know what an entity is
 * according to its name.
 *
 * The purpose of this file (library?) is to keep together these basic
 * string functions for entity names, with no dependence on ri.newgen.
 *
 * Different kinds of names:
 * - module name
 * - compilation unit name: "file!"
 * - static module name: "file!foo"
 *
 * At execution time, this encoding leads to over using string
 * functions. This was studied by HPC Project and Beatrice
 * Creusillet. She suggested to add a new field to entities, which
 * would carry this information.
 */

/* Check if the given name is a compilation unit internal name.
 *
 * Should be called "compilation_unit_name_p()" to avoid ambiguity about
 * the argument.
 */

bool compilation_unit_p(const char* module_name) {
  /* A module name is a compilation unit if and only if its last character is
     FILE_SEP */
  unsigned int len = strlen(module_name);
  if (len > 0) {
    if (module_name[len - 1] == FILE_SEP) {
      return true;
    }
  }
  return false;
}

/* Check if the given name is the name of a plain module and not of a
 * compilation unit.
 *
 * Argument "name" is supposed to be an internal name.
 */
bool module_name_p(string name) {
  return (!compilation_unit_p(name) && strstr(name, MODULE_SEP_STRING) == NULL);
}

/* Argument "name" is a global name
 *
 * In C, the main module is always called "main".
 *
 * In Fortran, the main module can have any declared name and a
 * special prefix is used.
 *
 * In both cases, they are part of TOP-LEVEL
 */
bool main_module_global_name_p(const char * name)
{
  bool main_p = false;
  /* Look for a C main name */
  main_p = same_string_p(name, TOP_LEVEL_MODULE_NAME MODULE_SEP_STRING "main");
  if(!main_p) {
    /* Look for a Fortran main */
    string prefix = TOP_LEVEL_MODULE_NAME MODULE_SEP_STRING MAIN_PREFIX;
    main_p = strncmp(prefix, name, strlen(prefix)) == 0;
  }
  return main_p;
}

/* Argument "name" is a local name (not a user name)
 *
 * In C, the main module is always called "main".
 *
 * In Fortran, the main module can have any declared name and a
 * special prefix is used.
 *
 * In both cases, they are part of TOP-LEVEL
 */
bool main_module_name_p(const char * name)
{
  bool main_p = false;
  /* Look for a C main name */
  main_p = same_string_p(name, "main");
  if(!main_p) {
    /* Look for a Fortran main */
    main_p = name[0]==MAIN_PREFIX_CHAR;
  }
  return main_p;
}

/* Check if the given name is a static module name.
 */
bool static_module_name_p(const char* name)
{
  /* An entity is a static module if its name contains the FILE_SEP_STRING
     but the last one is not the last character of the name string */
  /* FI: I doubt this is true. Maybe if you're sure name is the name of a module? */
  return (!compilation_unit_p(name) && strstr(name, FILE_SEP_STRING) != NULL);
}
/* functions on strings for entity names */

/* BEGIN_EOLE */ /* - please do not remove this line */
/* Lines between BEGIN_EOLE and END_EOLE tags are automatically included
   in the EOLE project (JZ - 11/98) */

/* Does take care of block scopes */
const char* global_name_to_user_name(const char* global_name)
{
  const char* user_name = string_undefined;
  char lc = global_name[strlen(global_name)-1];
  const char* p;

  /* First, take care of constrant strings and characters, wich may
     contain any of the PIPS special characters and strings.
     And do not forget Fortran format */

  if(lc=='"' || lc=='\'') {
    user_name = strchr(global_name, lc);
  }
  else if(lc==')') {
    user_name = strchr(global_name, '(');
  }
  else {

    /* Then all possible prefixes first */

    if (strstr(global_name,STRUCT_PREFIX) != NULL)
      user_name = strstr(global_name,STRUCT_PREFIX) + 1;
    else if (strstr(global_name,UNION_PREFIX) != NULL) {
      user_name = strstr(global_name,UNION_PREFIX) + 1;
    }
    else if (strstr(global_name,ENUM_PREFIX) != NULL)
      user_name = strstr(global_name,ENUM_PREFIX) + 1;
    else if (strstr(global_name,TYPEDEF_PREFIX) != NULL)
      user_name = strstr(global_name,TYPEDEF_PREFIX) + 1;

    else if (strstr(global_name,MEMBER_SEP_STRING) != NULL)
      user_name = strstr(global_name,MEMBER_SEP_STRING) + 1;

    else if (strstr(global_name,LABEL_PREFIX) != NULL)
      user_name = strstr(global_name,LABEL_PREFIX) + 1;
    else if (strstr(global_name,COMMON_PREFIX) != NULL)
      user_name = strstr(global_name,COMMON_PREFIX) + 1;
    else if (strstr(global_name,BLOCKDATA_PREFIX) != NULL) {
      /* Clash with the address-of C operator */
      user_name = strstr(global_name,BLOCKDATA_PREFIX)+1;
      //string s = strstr(global_name,BLOCKDATA_PREFIX);
      //
      //if(strlen(s)>1)
      //	user_name = s + 1);
      //else
      //user_name = s;
    }
    else if (strstr(global_name,MAIN_PREFIX) != NULL) {
      string s = strstr(global_name,MAIN_PREFIX) + 1;
      pips_debug(8, "name = %s \n", s);
      user_name = s;
    }
    /* Then F95 module separator */
    else if (strstr(global_name,F95MODULE_PREFIX) != NULL)
      user_name = strstr(global_name,F95MODULE_PREFIX) + 1;

    /* Then block seperators */
    else if (strstr(global_name,BLOCK_SEP_STRING) != NULL)
      user_name = strrchr(global_name,BLOCK_SEP_CHAR) + 1;

    /* Then module separator */
    else if (strstr(global_name,MODULE_SEP_STRING) != NULL)
      user_name = strstr(global_name,MODULE_SEP_STRING) + 1;


    /* Then file separator */
    else if (strstr(global_name,FILE_SEP_STRING) != NULL)
      user_name = strstr(global_name,FILE_SEP_STRING) + 1;
    else {
      pips_internal_error("no seperator ?");
      user_name = NULL;
    }

    /* Take care of the special case of static functions, leaving
       compilation unit names untouched */
    if ((p=strstr(user_name,FILE_SEP_STRING)) != NULL && *(p+1)!='\0')
      user_name = p + 1;
  }

  pips_debug(9, "global name = \"%s\", user_name = \"%s\"\n",
	     global_name, user_name);
  return user_name;
}

/* Does not take care of block scopes and returns a pointer */
const char* local_name(const char * s)
{
  char *start_ptr = strchr(s, MODULE_SEP);
  pips_assert("some separator", start_ptr != NULL);
  return start_ptr+1;
}

/* END_EOLE */

string make_entity_fullname(const char* module_name, const char* local_name)
{
    return(concatenate(module_name,
		       MODULE_SEP_STRING,
		       local_name,
		       (char *) 0));
}

//empty_local_label_name_p(s)
bool empty_string_p(const char* s)
{
    return(strcmp(s, "") == 0);
}


bool blank_string_p(const char*s ){
    extern int isspace(int);
    while(*s&&isspace(*s++));
    return !*s;
}

bool return_local_label_name_p(const char* s)
{
    return(strcmp(s, RETURN_LABEL_NAME) == 0);
}

bool empty_label_p(const char* s)
{
  // s must be a local label name
  pips_assert("no separator", strchr(s, MODULE_SEP) == NULL);
  // return(empty_local_label_name_p(local_name(s)+sizeof(LABEL_PREFIX)-1)) ;
  return (strcmp(s, EMPTY_LABEL_NAME) == 0);
}

bool empty_global_label_p(const char* gln)
{
  // gln must be a global label name
  const char* lln = local_name(gln);

  return empty_label_p(lln);
}

bool return_label_p(const char* s)
{
    return(return_local_label_name_p(local_name(s)+sizeof(LABEL_PREFIX)-1)) ;
}

/* Return the module part of an entity name.
 *
 * OK, this function name is pretty misleading: entity_name_to_entity_module_name().
 *
 * Maybe, it should be wrapped up in a higher-level function such as
 * entity_to_module_name().
 *
 * It uses a static buffer and should create trouble with long
 * function names.
 *
 * No memory allocation is performed, but it's result is transient. It
 * must be strdup'ed by the caller if it is to be preserved.
 *
 * To eliminate the static buffer and to allocate the returned string
 * would require lots of changes or add lots of memory leaks in PIPS
 * since the callers do not know they must free the result. Maybe we
 * should stack allocate a buffer of size strlen(s), but we would end
 * up returning a pointer to a popped area of the stack...
 */
const char* module_name(const char * s)
{
  static char *local = NULL;
  static size_t local_size = 0;

  char * sep = strchr(s, MODULE_SEP);
  size_t len = sep? (size_t) (sep-s): strlen(s);

  if (local_size < len + 1)
  {
    if (local) free(local);
    local_size = len + 1 > 100? len + 1: 100;
    local = malloc(local_size);
  }

  strncpy(local, s, len);
  local[len] = '\0';

  return local;
}

/*
 *  that is all
 */
