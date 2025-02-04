/*

  $Id: print_code_as_a_graph.c 23065 2016-03-02 09:05:50Z coelho $

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
/* Define all the entry points to generate the various graph
   sequential view to be viewed later with a graph viewer such as
   daVinci.

   Ronan.Keryell@cri.ensmp.fr, 5/09/1995. */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "genC.h"
#include "linear.h"

#include "misc.h"
#include "properties.h"

#include "ri-util.h"

#include "prettyprint.h"

bool print_code_as_a_graph(const string mod_name)
{
    bool success;

    set_bool_property("PRETTYPRINT_UNSTRUCTURED_AS_A_GRAPH", true);
    success = print_code(mod_name);
    set_bool_property("PRETTYPRINT_UNSTRUCTURED_AS_A_GRAPH", false);

    return success;
}
