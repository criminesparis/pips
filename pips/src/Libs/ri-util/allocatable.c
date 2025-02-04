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

/***
 * Handling of ALLOCATABLE (Fortran95)
 *
 * Allocatable are represented internally as structure, for instance :
 *
 * integer, dimension (:,:,:), allocatable :: myarray
 *
 * would be represented as (pseudo code display here) :
 *
 * struct __pips_allocatable__2D myarray;
 *
 * with
 *
 * struct __pips_allocatable__2D {
 *  int lowerbound1;
 *  int upperbound1;
 *  int lowerbound2;
 *  int upperbound2;
 *  int data[lowerbound1:upperbound1][lowerbound2:upperbound2]
 * }
 *
 * The structure is dependent of the number of dimension and is created
 * dynamically when encounting an allocatable declaration.
 *
 * The prettyprint recognize the structure based on the special prefix and
 * display it as an allocatable array in Fortran95.
 *
 */

/**
 * @brief Check if an entity is an allocatable
 */
bool entity_allocatable_p(entity e) {
  type t = entity_type(e);
  if(!type_variable_p(t)) {
    return false;
  }
  variable v = type_variable(t);
  if(!basic_derived_p(variable_basic(v))) {
    return false;
  }
  entity allocatable_struct = basic_derived(variable_basic(v));

  if(!same_stringn_p(entity_local_name(allocatable_struct),
      STRUCT_PREFIX ALLOCATABLE_PREFIX,
      sizeof(STRUCT_PREFIX ALLOCATABLE_PREFIX)-1)) {
    return false;
  }

  return true;
}

/**
 * @brief Check if an expression is a reference to an allocatable array
 */
bool expression_allocatable_data_access_p(expression e) {
  // This must be a call
  if(!expression_call_p(e)) {
    return false;
  }

  entity field_call = call_function(expression_call(e));
  list args_list = call_arguments(expression_call(e));

  // This must be a call to "." and we must have args
  if(!ENTITY_FIELD_P(field_call) || ENDP(args_list)) {
    return false;
  }

  // Check that we deal with an allocatable
  expression allocatable_exp = CAR(args_list).e;
  entity allocatable =
      reference_variable(expression_reference(allocatable_exp));
  if(!entity_allocatable_p(allocatable)) {
    return false;
  } else {
    pips_assert("Allocatable shouldn't have any indices !",
        ENDP(reference_indices(expression_reference(allocatable_exp))));
  }

  // Check that it is the data field
  expression field_exp = CAR(CDR(args_list)).e;
  pips_assert("Allocatable field shouldn't have any indices !",
      ENDP(reference_indices(expression_reference(field_exp))));
  entity field = reference_variable(expression_reference(field_exp));
  if(same_stringn_p(entity_user_name(field),
      ALLOCATABLE_LBOUND_PREFIX,
      strlen(ALLOCATABLE_LBOUND_PREFIX))
      || same_stringn_p(entity_user_name(field),
          ALLOCATABLE_UBOUND_PREFIX,
          strlen(ALLOCATABLE_UBOUND_PREFIX))) {
    return false;
  }

  return true;
}

/**
 * @brief This function produce an expression that is an access to the array
 * inside the allocatable structure.
 */
expression get_allocatable_data_expr(entity e) {
  pips_assert("Entity isn't an allocatable", entity_allocatable_p(e));

  entity data_field = get_allocatable_data_entity(e);

  // Construct the expression e.data
  return MakeBinaryCall(CreateIntrinsic(FIELD_OPERATOR_NAME),
                        entity_to_expression(e),
                        entity_to_expression(data_field));

}

/**
 * @brief Get the entity inside the struct corresponding to the array,
 * mostly for correct prettyprint
 */
entity get_allocatable_data_entity(entity e) {
  pips_assert("Entity isn't an allocatable", entity_allocatable_p(e));

  // Get the data field inside the allocatable struct
  variable v = type_variable(entity_type(e));
  entity allocatable_struct = basic_derived(variable_basic(v));
  entity data_field = CAR(type_struct(entity_type(allocatable_struct))).e;
  return data_field;
}

