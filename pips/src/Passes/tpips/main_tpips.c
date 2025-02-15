/*

  $Id: main_tpips.c 23065 2016-03-02 09:05:50Z coelho $

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
/* 
 * This file contains the main for tpips.
 * Please, do not change anything! do any change to tpips_main().
 */

extern void pips_thanks(char *, char *);
extern int tpips_main(int, char**);

int main(int argc, char ** argv)
{
    pips_thanks("tpips", argv[0]);
    return tpips_main(argc, argv);
}
