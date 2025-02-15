/*

  $Id: freia_sigmac.h 23065 2016-03-02 09:05:50Z coelho $

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

/*
 * data structures that describe FREIA SigmaC target.
 */

#ifndef   HWAC_FREIA_SIGMAC_H_
# define  HWAC_FREIA_SIGMAC_H_

#define FREIA_SIGMAC_SC_INCLUDES		\
  "/* C INCLUDES */\n"				\
  "#include <stdio.h>\n"			\
  "\n"						\
  "/* SIGMA-C INCLUDES */\n"			\
  "#include \"sigmacAgents.h\"\n"		\
  "\n"						\
  "\n"

#define FREIA_SIGMAC_INCLUDES			\
  "/* SIGMAC C includes */\n"			\
  "#include <freia.h>\n"			\
  "\n"
//"#include <freia_sigmac_runtime.h>\n"


typedef struct {
  //name of the agent as defined in the .sc files
  string agent_name;
  //prefix shared by all the instances of this agent in order to manipulate its instances
  string inst_prefix;
  //generic agent arguments
  string agent_arg;
  bool mergeable;
  int weight;

} sigmac_hw_t;

#define PIXEL_T "int16_t"
#define PARAM_T "int32_t"


#endif /* !HWAC_FREIA_SIGMAC_H_ */
