/*

  $Id: arithmetic_errors.h 1641 2016-03-02 08:20:19Z coelho $

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

/*
 * managing arithmetic errors...
 * detecting and managing arithmetic errors on Values should be
 * systematic. These macros gives a C++ look and feel to this
 * management.
 *
 * (c) CA et FC, Sept 1997
 */

#if !defined(linear_arithmetic_error_included)
#define linear_arithmetic_error_included

#include <setjmp.h>

/* callback for timeout
 * expecting: delay, function, file, lineno
 */
typedef void (*timeout_callback_f)(int, const char *, const char *, int);

/* Global constants to designate exceptions.
   To be used in the type field.
*/
typedef enum {
  overflow_error = 1,
  simplex_arithmetic_error = 2,
  user_exception_error = 4,
  parser_exception_error = 8,
  timeout_error = 16,
  /* catch all */
  any_exception_error = ~0
} linear_exception_t;

/* HACK: there is a throw exception in linear and another version in polylib
 * ensure that the one from linear is used...
 */
#define throw_exception linear_throw_exception
#define push_exception_on_stack linear_push_exception_on_stack
#define pop_exception_from_stack linear_pop_exception_from_stack

typedef void (*exception_callback_t)(char const *, char const *, int const);

/* 'const' out because of cproto 4.6. FC 13/06/2003 */
#define EXCEPTION extern unsigned int

#define THROW(what)                                             \
  (throw_exception(what, CURRENT_FUNCTION, __FILE__, __LINE__))

#define CATCH(what)                                           \
  if (setjmp(*push_exception_on_stack(what, CURRENT_FUNCTION,	\
                                       __FILE__, __LINE__)))

#define UNCATCH(what)                               \
  (pop_exception_from_stack(what, CURRENT_FUNCTION,	\
			       __FILE__, __LINE__))

#define TRY else

#define RETHROW() THROW(the_last_just_thrown_exception)

#endif /* linear_arithmetic_error_included */

/* end of it.
 */
