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

/* Functions using simultaneously pipsdbm, which is based on strings,
   and ri-util, which contains basic methods for the objects of the
   internal representation.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#include "linear.h"

#include "genC.h"
#include "misc.h"
#include "ri.h"
#include "properties.h"
#include "ri-util.h"
//#include "text-util.h"
#include "workspace-util.h"

/* try to parse @p s in the context of module @p module
 * only simple expressions are found */
expression string_to_expression(const char * s,entity module)
{
    entity e = string_to_entity(s,module);
    if(entity_undefined_p(e)) {
        /* try to find simple expression */
        /* unary operators */
        for(const char *iter = s ; *iter ; iter++) {
            if(isspace(*iter)) continue;
            if(*iter=='-') {
                expression etmp = string_to_expression(iter+1, module);
                if(!expression_undefined_p(etmp)) {
                    return MakeUnaryCall(entity_intrinsic(UNARY_MINUS_OPERATOR_NAME),
                            etmp);
                }
            }
        }
        
        /*binary operators*/
        static const char* seeds[] = {   PLUS_OPERATOR_NAME, MINUS_OPERATOR_NAME,MULTIPLY_OPERATOR_NAME, DIVIDE_OPERATOR_NAME};
	for(int i=0; i < (int) (sizeof(seeds)/sizeof(seeds[0])); i++) {
            char *where = strchr(s,seeds[i][0]);
            if(where) {
                char * head = strdup(s);
                char * tail = head + (where -s) +1 ;
                head[where-s]='\0';
                expression e0 = string_to_expression(head,module);
                expression e1 = string_to_expression(tail,module);
                free(head);
                if(!expression_undefined_p(e0) &&!expression_undefined_p(e1)) {
                    return MakeBinaryCall(
                            entity_intrinsic(seeds[i]),
                            e0,
                            e1
                            );
                }
                else {
                    free_expression(e0);
                    free_expression(e1);
                }
            }
        }
        return expression_undefined;
    }
    else
        return entity_to_expression(e);
}
/* split a string using @p seed as separator
 * and call string_to_expression on each chunk */
list string_to_expressions(const char * str, const char * seed, entity module) {
    list strings = strsplit(str,seed);
    list expressions = NIL;
    FOREACH(STRING,s,strings) {
        expression expr = string_to_expression(s,module);
        if(!expression_undefined_p(expr)) {
            expressions = CONS(EXPRESSION,
                    expr,
                    expressions);
        }
    }
    gen_map(free,strings);
    gen_free_list(strings);
    return gen_nreverse(expressions);
}
