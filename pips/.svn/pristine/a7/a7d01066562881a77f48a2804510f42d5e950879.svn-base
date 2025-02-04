/*

  $Id$

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
#include "constants.h"
#include "naming.h"

/* Naming of files in the PIPS database.
 *
 */

string string_codefilename(const char *s)
{
    return(concatenate(TOP_LEVEL_MODULE_NAME MODULE_SEP_STRING,
		       s, SEQUENTIAL_CODE_EXT, NULL));
}

string string_par_codefilename(const char *s)
{
    return(concatenate(TOP_LEVEL_MODULE_NAME MODULE_SEP_STRING,
		       s, PARALLEL_CODE_EXT, NULL));
}

string string_fortranfilename(const char* s)
{
    return(concatenate(TOP_LEVEL_MODULE_NAME MODULE_SEP_STRING,
		       s, SEQUENTIAL_FORTRAN_EXT, NULL));
}

bool string_fortran_filename_p(const char* s)
{
  int fnl = strlen(s);
  int sl = sizeof(SEQUENTIAL_FORTRAN_EXT)-1;
  bool is_fortran = false;

  if(fnl<=sl)
    is_fortran = false;
  else
    is_fortran = strcmp(SEQUENTIAL_FORTRAN_EXT, s+(fnl-sl))==0;

  return is_fortran;
}

string string_par_fortranfilename(const char* s)
{
    return(concatenate(TOP_LEVEL_MODULE_NAME MODULE_SEP_STRING,
		       s, PARALLEL_FORTRAN_EXT, NULL));
}

string string_pp_fortranfilename(const char* s)
{
    return(concatenate(TOP_LEVEL_MODULE_NAME MODULE_SEP_STRING,
		       s, PRETTYPRINT_FORTRAN_EXT, NULL));
}

string string_predicat_fortranfilename(const char* s)
{
    return(concatenate(TOP_LEVEL_MODULE_NAME MODULE_SEP_STRING,
		       s, PREDICAT_FORTRAN_EXT, NULL));
}

string string_entitiesfilename(const char* s)
{
    return(concatenate(TOP_LEVEL_MODULE_NAME MODULE_SEP_STRING,
		       s, ENTITIES_EXT, NULL));
}

/* Keep track of the script directory. It is used to retrieve
   information about old properties, mostly in a non-regression
   setting.

   In case of "source", the auxiliary directory is ignored.

   FI: I do not reset nor free this variable since it is set from
   beginning to end.

 */
static string script_directory_name = string_undefined;

void set_script_directory_name(string dn)
{
  script_directory_name = strdup(dn);
}

string get_script_directory_name(void)
{
  return script_directory_name;
}

/*
 *  that is all
 */
