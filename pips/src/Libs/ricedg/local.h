/*

  $Id: local.h 23065 2016-03-02 09:05:50Z coelho $

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

#include <stdlib.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include <string.h>
#include <setjmp.h>

#include "linear.h"

#include "genC.h"

#include "text.h"
#include "ri.h"
#include "effects.h"

#include "icfg.h"

#include "misc.h"
#include "properties.h"

#include "text-util.h"
#include "ri-util.h"

#include "control.h" // load_ctrl_graph
#include "effects-util.h"
#include "effects-generic.h" // used
#include "effects-simple.h" // used
#include "semantics.h" // used

#include "pipsdbm.h"

#include "pipsmake.h" // ??? rule_phase hack

#include "ricedg.h"

#include "alias_private.h"
