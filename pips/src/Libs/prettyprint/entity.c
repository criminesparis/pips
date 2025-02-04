/*

  $Id: entity.c 23065 2016-03-02 09:05:50Z coelho $

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

/* Functions closely related to the prettyprint of entity class
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "linear.h"

#include "genC.h"
#include "misc.h"
#include "properties.h"
#include "ri-util.h"

#include "prettyprint.h"

static void print_dimension(dimension d)
{
    fprintf(stderr,"dimension :\n");
    print_expression(dimension_lower(d));
    print_expression(dimension_upper(d));
}

/* print_entity_variable(e)
 *
 * if it is just a variable, the type is printed,
 * otherwise just the entity name is printed
 */
void print_entity_variable(entity e)
{
    variable v;

    (void) fprintf(stderr,"name: %s\n",entity_name(e));

    if (!type_variable_p(entity_type(e)))
        return;

    v = type_variable(entity_type(e));

    fprintf(stderr,"basic %s\n",basic_to_string(variable_basic(v)));
    gen_map((gen_iter_func_t) print_dimension, variable_dimensions(v));
}
