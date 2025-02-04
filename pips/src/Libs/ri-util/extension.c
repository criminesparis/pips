/*

  Copyright 1989-2010 HPC Project

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
/*
  Functions dealing with the Newgen objects "extension", which are
  part of "statement"; they are used to encode pragmas.

  Pierre.Villalon@hpc-project.com
  Ronan.Keryell@hpc-project.com
*/
#ifdef HAVE_CONFIG_H
    #include "pips_config.h"
#endif

#include "linear.h"
#include "genC.h"
#include "ri.h"
#include "ri-util.h"

/*****************************************************A CONSTRUCTOR LIKE PART
 */

/** @return an empty extensions
 */
extensions empty_extensions (void) {
  return make_extensions (NIL);
}

/** @return true if the extensions field is empty
    @param es the extensions to test
*/
bool empty_extensions_p (extensions es) {
  return (extensions_extension (es) == NIL);
}
