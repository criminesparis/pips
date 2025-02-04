/*

  $Id: util.c$

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
#include "pipsdbm.h"

/* returns whether there is a main in the database
 */

bool some_main_entity_p(void)
{
  bool some_main_p = false;
  char * main_list = strdup(concatenate(db_get_current_workspace_directory(),
					"/", MAIN_FILE_NAMES, NULL));
  FILE * fm = fopen(main_list, "r");
  if(fm!=NULL) {
    some_main_p = true;
    fclose(fm);
  }
  free(main_list);
  return some_main_p;
}


/* Return the local name of the main module if it is available,
 * or the local name of any module by default.
 *
 * Hopefully, the module names are sorted and the same module of rank
 * 0 is always returned.
 *
 * A new string is allocated.
 *
 * Up to a memory leak:
 * entity get_main_entity(void) == module_name_to_entity(get_main_entity_name())
 */
string get_main_entity_name(void)
{
  string mn = string_undefined;
  char buffer[MAXIMAL_MODULE_NAME_SIZE]; // defined in naming.h
  char * main_list = strdup(concatenate(db_get_current_workspace_directory(),
					"/", MAIN_FILE_NAMES, NULL));
  FILE * fm = fopen(main_list, "r");
  buffer[0] = 0;
  if (fm!=NULL) {
    // FI: we assume here that we have only one main function
    safe_fgets(buffer, MAXIMAL_MODULE_NAME_SIZE, fm, main_list);
    fclose(fm);
    // Drop the final LF
    mn = strndup(buffer, strlen(buffer)-1);
  }
  else {
    // FI: a module list is an array ?
    gen_array_t modules = db_get_module_list();
    int nmodules = gen_array_nitems(modules);

    pips_assert("some modules in the program", nmodules>0);
    /* ??? some default if there is no main...
     *
     * This has an impact on interprocedural analysis and especially
     * semantics and works well if only one function is analyzed.
     */
    pips_user_warning("No main function found, use \"%s\" instead.\n",
		      gen_array_item(modules,0));
    mn = strdup(gen_array_item(modules, 0));

    gen_array_full_free(modules);
  }
  return mn;
}

/** @} */
