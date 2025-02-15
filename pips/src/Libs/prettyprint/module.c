/*

  $Id: module.c 23065 2016-03-02 09:05:50Z coelho $

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

#include "prettyprint.h"

/* High-level functions about modules, using prettyprint, pipsdbm and
   ri-util
 */

static void do_recompile_module(entity module, statement module_statement) {

    /* build and register textual representation */
    text t = text_module(module, module_statement);
    //add_new_module_from_text(module,t,fortran_module_p(modified_module),compilation_unit_of_module(module));
    string dirname = db_get_current_workspace_directory();
    string res = fortran_module_p(module)? DBR_INITIAL_FILE : DBR_C_SOURCE_FILE;
    string filename = db_get_file_resource(res,module_local_name(module),true);
    string fullname = strdup(concatenate(dirname, "/",filename, NULL));
    FILE* f = safe_fopen(fullname,"w");
    free(fullname);
    print_text(f,t);
    fclose(f);
    free_text(t);

    DB_PUT_FILE_RESOURCE(res,module_local_name(module),filename);

    /* the module will be reparsed, so fix(=delete) all its previous entites */
#if 0
    {
        list p = NIL;
        FOREACH(ENTITY, e, entity_declarations(modified_module))
        {
            if( recompile_module_removable_entity_p((gen_chunkp)e))
                gen_clear_tabulated_element((gen_chunk*)e);
            else
                p = CONS(ENTITY,e,p);
        }
        entity_declarations(modified_module) = gen_nreverse(p);
        code_initializations(value_code(entity_initial(modified_module)))=make_sequence(NIL);
    }
#endif
}


/* build a textual representation of the modified module and update db
 */
bool recompile_module(const string module)
{
    entity modified_module = module_name_to_entity(module);
    statement modified_module_statement =
        (statement) db_get_memory_resource(DBR_CODE, module, true);
    do_recompile_module(modified_module,modified_module_statement);
    return true;
}
