/*

  $Id: sc_to_sg_test.c 1641 2016-03-02 08:20:19Z coelho $

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

/* test de la conversion d'un systeme d'equations et d'inequations en
 * un systeme generateur
 *
 * Francois Irigoin, Decembre 1989
 */

#ifdef HAVE_CONFIG_H
    #include "config.h"
#endif

#include <stdio.h>
#include <string.h>

#include "boolean.h"
#include "vecteur.h"
#include "contrainte.h"
#include "sc.h"

#include "ray_dte.h"
#include "sommet.h"
#include "sg.h"

#include "polyedre.h"

/* extern int sc_to_sg_debug_level; */

int main(argc,argv)
int argc;
char * argv[];
{
    Psysteme s;
    /* systeme generateur sg */
    Ptsg sg; 
    FILE * f;
    char * filename = "stdin";

    if(argc==1) {
	f = stdin;
	fprintf(stderr,"Lecture sur stdin\n");
    }
    else if(argc==2) {
	filename = strdup(argv[1]);
	if((f = fopen(filename,"r")) == NULL) {
	    fprintf(stderr,"Ouverture du fichier %s impossible\n",
		    filename);
	    exit(4);
	}
    }
    else {
	fprintf(stderr,"Usage: sc_fscan_print [filename]\n");
	exit(1);
    }

    /* lecture du systeme */
    if(sc_fscan(f,&s)) {
	/* sc_dump(s); */
	fprintf(stderr,"syntaxe correcte dans %s\n",filename);
	sc_fprint(stdout,s, variable_default_name);
    }
    else {
	fprintf(stderr,"erreur de syntaxe dans %s\n",filename);
	exit(1);
    }

    /* conversion */
    /* sc_to_sg_debug_level = 9; */
    sg = sc_to_sg_chernikova(s);
    sg_fprint(stdout, sg, variable_dump_name);

    return 0;
}
