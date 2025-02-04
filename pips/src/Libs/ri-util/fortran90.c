/*

  $Id: fortran90.c 23065 2016-03-02 09:05:50Z coelho $

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
/* Prettyprint one FORTRAN 90 loop as an array expression.

   Pierre Jouvelot

   For one level only loop, with one assignment as body. Replaces
   occurences of the index variable by ranges in expressions. Ranges are
   prettyprinted as triplet when they occur as subscript expressions and
   as vectors with implicit DO otherwise. If the replacement cannot occur,
   for instance because subscript expressions are coupled, the loop is
   printed as a loop.

   There are/were memory leaks here since a new expression is constructed.

*/

#include <stdio.h>

#include "linear.h"

#include "genC.h"
#include "ri.h"
#include "misc.h"

#include "ri-util.h"

/* Entity f is supposed to be a binary operator, not always commutative
   but meaningful for a range and a scalar or for two ranges. Boolean
   argument left means that range r appears on the left of f, i.e. as
   first operator.

   No sharing is created between the new expression e and arguments r, lw,
   up or in.
  */

expression update_range(f, r, lw, up, in, left)
entity f ;
range r ;
expression lw, up, in ;
bool left;
{
    range new_r = copy_range(r);
    intptr_t val = 0;
    expression new_up = copy_expression(up);
    expression new_lw = copy_expression(lw);
    expression new_in = copy_expression(in);
    expression e = expression_undefined;

    pips_assert("new_r is consistent before update", range_consistent_p(new_r));

    if(left) {
	range_lower( new_r ) = MakeBinaryCall(f, range_lower(new_r), new_lw);
	range_upper( new_r ) = MakeBinaryCall(f, range_upper(new_r), new_up);
    }
    else {
	range_lower( new_r ) = MakeBinaryCall(f, new_lw, range_lower(new_r));
	range_upper( new_r ) = MakeBinaryCall(f, new_up, range_upper(new_r));
    }

    pips_assert("new_r is consistent", range_consistent_p(new_r));
	
    if( strcmp( entity_local_name( f ), MULTIPLY_OPERATOR_NAME ) == 0 ) {
	/* expression "in" must be integer constant 1 */
	pips_assert("This is a scalar value", lw==up);
	free_expression(range_increment( new_r ));
	range_increment( new_r ) = 
		MakeBinaryCall(f, new_in, copy_expression(range_lower(new_r))) ;
    }
	
    if( !left && (strcmp( entity_local_name( f ), MINUS_OPERATOR_NAME ) == 0) ) {
	entity um = entity_intrinsic(UNARY_MINUS_OPERATOR_NAME);

	range_increment( new_r ) = 
		MakeUnaryCall(um, range_increment(new_r)) ;
    }

    if(expression_integer_value(range_lower(new_r), &val)) {
	free_expression(range_lower(new_r));
	range_lower(new_r) = int_to_expression(val);
    }

    if(expression_integer_value(range_upper(new_r), &val)) {
	free_expression(range_upper(new_r));
	range_upper(new_r) = int_to_expression(val);
    }

    if(expression_integer_value(range_increment(new_r), &val)) {
	free_expression(range_increment(new_r));
	range_increment(new_r) = int_to_expression(val);
    }

    pips_assert("new_r is consistent after simplification", range_consistent_p(new_r));

    e = make_expression(make_syntax(is_syntax_range, new_r),
			normalized_undefined);

    return e;
}
