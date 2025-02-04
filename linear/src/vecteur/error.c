/*

  $Id: error.c 1641 2016-03-02 08:20:19Z coelho $

  Copyright 1989-2016 MINES ParisTech

  This file is part of Linear/C3 Library.

  Linear/C3 Library is free software: you can redistribute it and/or modify it
  under the terms of the GNU Lesser General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  any later version.

  Linear/C3 Library is distributed in the hope that it will be useful, but WITHOUT ANY
  WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.

  See the GNU Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public License
  along with Linear/C3 Library.  If not, see <http://www.gnu.org/licenses/>.

*/

/* package vecteur */

/*LINTLIBRARY*/
#ifdef HAVE_CONFIG_H
    #include "config.h"
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
	

/* void vect_error(va_dcl va_list): 
 * should be called to terminate execution and to core dump
 * when data structures are corrupted or when an undefined operation is
 * requested (zero divide for instance). VECT_ERROR should be called as:
 * 
 *   VECT_ERROR(function_name, format, expression-list)
 * 
 * where function_name is a string containing the name of the function
 * calling VECT_ERROR, and where format and expression-list are passed as
 * arguments to vprintf. VECT_ERROR terminates execution with abort.
 * 
 */
/*VARARGS0*/
void vect_error(char * name, char * fmt, ...)
{
    va_list args;
    va_start(args, fmt);

    /* print name of function causing error */
    (void) fprintf(stderr, "vecteur error in %s: ", name);

    /* print out remainder of message */
    (void) vfprintf(stderr, fmt, args);
    va_end(args);

    /* create a core file for debug */
    (void) abort();
}
