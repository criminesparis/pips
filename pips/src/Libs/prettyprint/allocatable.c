/*

 $Id: allocatable.c 23065 2016-03-02 09:05:50Z coelho $

 Copyright 1989-2016 MINES ParisTech
 Copyright 2009-2010 HPC Project

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

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "genC.h"
#include "linear.h"
#include "misc.h"
#include "ri.h"

#include "ri-util.h"
#include "prettyprint.h"

/**
 * @brief Helper for creating an allocatable structure. Here we create the
 * field corresponding to the data array.
 */
static entity make_data_field(basic b,
                              const char *struct_name,
                              const char *name,
                              list dimensions) {

  string field ;
  asprintf(&field, "%s" MEMBER_SEP_STRING"%s", struct_name,name);

  pips_assert("Trying to create data for an already existing struct ?",
      FindEntity(TOP_LEVEL_MODULE_NAME,field) == entity_undefined );

  entity data = FindOrCreateTopLevelEntity(field);
  free(field);
  entity_type(data) = make_type_variable(make_variable(b, dimensions, NULL));
  entity_storage(data) = make_storage_rom();
  entity_initial(data) = make_value_unknown();

  return data;
}

static entity make_bound(const char *struct_name, const char *lname, int suffix) {
  entity bound;

  // Create the name
  string name;
  pips_assert("asprintf !",
      asprintf( &name,
          "%s" MEMBER_SEP_STRING "%s%d",
          struct_name,
          lname,
          suffix ));

  pips_assert("Trying to create lower bound but already existing ?",
      gen_find_tabulated( name, entity_domain ) == entity_undefined );

  bound = FindOrCreateTopLevelEntity(name);

  entity_type(bound) = make_type_variable(make_variable(make_basic_int(4),
                                                        NULL,
                                                        NULL));
  entity_storage(bound) = make_storage_rom();
  entity_initial(bound) = make_value_unknown();

  free(name);
  return bound;
}

/**
 * @brief This function try to find the allocatable structure corresponding to
 * the number of dimensions requested, and create it if necessary.
 * @param name is the name of the array (prettyprint name)
 */
entity find_or_create_allocatable_struct(basic b, string name, int ndim) {
  // FI: scaffolding code is not even guarded...
  printf("Creating allocatable struct for dim %d\n", ndim);

  // Create the entity name according to the number of dims
  string struct_name;
  string b_str = STRING(CAR(words_basic(b,NULL)));
  pips_assert("asprintf !",
      asprintf( &struct_name, ALLOCATABLE_PREFIX"%s_%s_%dD", name, b_str,ndim));

  // Here is the internal PIPS name, there is a prefix for struct
  string prefixed_name = strdup(concatenate(STRUCT_PREFIX, struct_name, NULL));

  // Let's try to localize the structure
  entity struct_entity = FindEntity(TOP_LEVEL_MODULE_NAME, prefixed_name);

  // Localization failed, let's create it
  if(struct_entity == entity_undefined) {
    list fields = NULL;
    list dimensions = NULL;
    for (int dim = ndim; dim >= 1; dim--) {
      entity lower = make_bound(struct_name, ALLOCATABLE_LBOUND_PREFIX, dim);
      entity upper = make_bound(struct_name, ALLOCATABLE_UBOUND_PREFIX, dim);

      // Field for struct
      fields = CONS(ENTITY,lower,fields);
      fields = CONS(ENTITY,upper,fields);

      // Dimensions for the data array
      dimension d = make_dimension(entity_to_expression(lower),
                                   entity_to_expression(upper),
				   NIL);
      dimensions = CONS(DIMENSION,d,dimensions );
    }

    // Create data holder
    fields
        = CONS(ENTITY,make_data_field(b, struct_name, name, dimensions),fields);

    // Create the struct
    string field;
    asprintf(&field,STRUCT_PREFIX "%s",struct_name);
    struct_entity = FindOrCreateTopLevelEntity(field);
    free(field);
    entity_type(struct_entity) = make_type_struct(fields);
    entity_storage(struct_entity) = make_storage_rom();
    entity_initial(struct_entity) = make_value_unknown();
  }

  free(prefixed_name);
  free(struct_name);

  return struct_entity;
}
