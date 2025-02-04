/*

  $Id: tiling.c 23495 2018-10-24 09:19:47Z coelho $

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
/* package tiling
 *
 * 1. Why?
 *    - memory hierarchy (registers, caches L1/L2/L3, memory, virtual memory, out-of-core,...)
 *    - granularity (amortization of fix costs: synchronization, communication, control,...)
 * 2. Legality
 *    - TO BE IMPLEMENTED
 * 3. Selection
 *    - directions (e.g. communication minimization): Darte/Robert, Hoegsted
 *    - ratios (e.g. critical path minimization)
 *    - volume (fix cost amortization) under memory constraints
 *    - mapping on finite hardware (Robert/...)
 *    restriction to orthogonal tilings: ratios, volume, mapping (Andonov/Rajopadhye)
 * 4. Code Generation (Xue?)
 *    - control and memory addressing overheads
 * 5. Hierarchical Tiling (Ferrante/Carter,...)
 * 6. Data vs Control Tiling
 * 7. Extensions
 *    - perfectly nested loops (IMPLEMENTED)
 *    - non perfectly nested loops (e.g. matrix multiply)
 *    - general nested loops (e.g. ADI)
 *    - sequence of loop nests (signal processing, Thomson-CSF)
 *    - ...
 * See: http://www.irisa.fr/api/Rajopadhye/tiling
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdlib.h>
#include <strings.h>

#include "genC.h"
#include "linear.h"
#include "ri.h"
#include "effects.h"
#include "misc.h"
#include "text.h"
#include "pipsdbm.h"
#include "boolean.h"
#include "vecteur.h"
#include "contrainte.h"
#include "sc.h"
#include "matrice.h"
#include "matrix.h"
#include "sparse_sc.h"
#include "ri-util.h"
#include "effects-util.h"
#include "conversion.h"
#include "dg.h"
typedef dg_arc_label arc_label;
typedef dg_vertex_label vertex_label;
#include "graph.h"
#include "ricedg.h"

#include "graph.h"
#include "transformations.h"
#include "properties.h"
#include "tiling.h"
#include "movements.h"

#include "hyperplane.h"

/* Create a new entity for tile index. Because of the module name, it is easier to postfix
 * by "_t" than to prefix by "t_".
 */
static entity 
make_tile_index_entity(entity old_index)
{
  return make_new_index_entity(old_index, "_t");
}
static entity 
make_local_tile_index_entity(entity old_index)
{
  return make_new_index_entity(old_index, "_l");
}

bool
static_partitioning_matrix(matrice P, int n, const char* serialized_matrix)
{
    pips_assert("interactive_partitioning_matrix", n>=1);
    bool status = false;
    if( serialized_matrix && !string_undefined_p(serialized_matrix) && !empty_string_p(serialized_matrix))
    {
        int row,col;
	string ctxt0 = string_undefined, ctxt1 = string_undefined;
        string saved_ptr,buffer,elem = NULL;
        saved_ptr= buffer = strdup(serialized_matrix);
        string line = strtok_r(buffer,",",&ctxt0);
        DENOMINATOR(P) = VALUE_ONE;
        for(row=1;row<=n;row++){
            elem = strtok_r(line," ",&ctxt1);

            for(col=1;col<=n;col++)
            {
                if(!elem) elem = col==row ? "1" : "0";
                ACCESS(P, n, row, col)=atoi(elem);
                elem = strtok_r(NULL," ",&ctxt1);
            }
            line = strtok_r(NULL,",",&ctxt0);
        }
        status= ( line == NULL ) && (elem == NULL );
        free(saved_ptr);
    }
    return status;
}

/* Query the user for a partitioning matrix P
 */

bool
interactive_partitioning_matrix(matrice P, int n)
{
    int n_read;
    string resp = string_undefined;
    string cn = string_undefined;
    bool return_status = false;
    int row;
    int col;

    DENOMINATOR(P) = VALUE_ONE;
    /* Query the user for P's components */
    pips_assert("interactive_partitioning_matrix", n>=1);
    debug(8, "interactive_partitioning_matrix", "Reading P\n");

    for(row=1; row<=n; row++) {
	resp = user_request("Partitioning matrix (%dx%d)?\n"
			    "(give all its integer coordinates on one line of %d per row): ",
			    n, n, n);
	if (resp[0] == '\0') {
	    user_log("Tiling loop transformation has been cancelled.\n");
	    return_status = false;
	}
	else {    
	    cn = strtok(resp, " \t");

	    return_status = true;
	    for( col = 1; col<=n; col++) {
		if(cn==NULL) {
		    user_log("Too few coordinates. "
			     "Tiling loop transformation has been cancelled.\n");
		    return_status = false;
		    break;
		}
		n_read = sscanf(cn," " VALUE_FMT, &ACCESS(P, n, row, col));
		if(n_read!=1) {
		    user_log("Too few coordinates. "
			     "Hyperplane loop transformation has been cancelled.\n");
		    return_status = false;
		    break;
		}
		cn = strtok(NULL, " \t");
	    }
	}

	if(cn!=NULL) {
	    user_log("Too many coordinates. "
		     "Tiling loop transformation has been cancelled.\n");
	    return_status = false;
	}
    }

    ifdebug(8) {
	if(return_status) {
	    pips_debug(8, "Partitioning matrix:\n");
	    matrice_fprint(stderr, P, n, n);
	    (void) fprintf(stderr,"\n");
	    pips_debug(8, "End\n");
	}
	else {
	    pips_debug(8, "Ends with failure\n");
	}
    }

    return return_status;
}


/* Generate the tile membership constraints between a tile coordinates and
 an iteration coordinate
 */

static Psysteme
tile_membership_constraints(Pbase initial_basis,
			    Pbase tile_basis,
			    matrice HT,
			    Pvecteur tiling_offset)
{
    Psysteme mc = sc_new();
    int dim = base_dimension(initial_basis);
    int row;
    int col;
    Value k = DENOMINATOR(HT);
    Value up = k - VALUE_ONE;
    Pbase civ = BASE_UNDEFINED;
    Pbase ctv = BASE_UNDEFINED;

    ifdebug(8) {
	debug(8, "tile_membership_constraints", "Begin with Matrix HT:\n");
	matrice_fprint(stderr, HT, dim, dim);
    }

    pips_assert("The two bases have the same dimension", dim == base_dimension(tile_basis));

    for(row = 1; row <= dim; row++) {
	Pvecteur upper = VECTEUR_NUL;
	Pvecteur lower = VECTEUR_NUL;
	Pcontrainte cupper = CONTRAINTE_UNDEFINED;
	Pcontrainte clower = CONTRAINTE_UNDEFINED;

	for(col = 1, civ = initial_basis, ctv = tile_basis;
	    col <= dim;
	    col++, civ = vecteur_succ(civ), ctv = vecteur_succ(ctv)) {
	    if(ACCESS(HT, dim, row, col)!=VALUE_ZERO) {
		Value coeff = ACCESS(HT, dim, row, col);
		Value offset = vect_coeff(vecteur_var(civ), tiling_offset);

		vect_add_elem(&upper, vecteur_var(civ), coeff);
		vect_add_elem(&upper, TCST, value_uminus(offset*coeff));
	    }
	    if(col==row) {
		vect_add_elem(&upper, vecteur_var(ctv), value_uminus(k));
	    }
	}
	lower = vect_dup(upper);
	vect_chg_sgn(lower);
	vect_add_elem(&upper, TCST, value_uminus(up));
	cupper = contrainte_make(upper);
	clower = contrainte_make(lower);
	sc_add_inegalite(mc, cupper);
	sc_add_inegalite(mc, clower);
    }

    sc_creer_base(mc);

    ifdebug(8) {
	pips_debug(8, "End with constraint system mc:\n");
	sc_fprint(stderr, mc, (get_variable_name_t)entity_local_name);
    }

    return mc;
}

/* Generate the tile membership constraints between a tile coordinates and
 an iteration coordinate
*/

Psysteme
tile_hyperplane_constraints(Pbase initial_basis,
			     Pbase tile_basis,
			     matrice HT,
			     Pvecteur tiling_offset)
{
  Psysteme mc = sc_new();
  int dim = base_dimension(initial_basis);
  int row;
  int col,col2;
  Value k = DENOMINATOR(HT);
  Value up = k - VALUE_ONE;
  Pbase civ = BASE_UNDEFINED;
  Pbase ctv = BASE_UNDEFINED;
  matrice  G_tile;
  Value *h_tile; // hyperplane direction
  ifdebug(8) {
    debug(8, "tile_membership_constraints", "Begin with Matrix HT:\n");
    matrice_fprint(stderr,HT, dim, dim);
  }
  int n = dim; 
  pips_assert("The two bases have the same dimension", dim == base_dimension(tile_basis));

  ifdebug(8) {
    pips_debug(8,"hyperplane matrix HT:");
    matrice_fprint(stderr, HT, n, n);
    (void) fprintf(stderr,"\n");
  }

  /* computation of the hyperplane tile direction in the tile basis: = sum(hi)= 1H */
  h_tile = (Value*)(malloc(n*sizeof(Value)));
  G_tile = matrice_new(n,n);
 
  string tile_direction = (string) get_string_property("TILE_DIRECTION");
  if(!empty_string_p(tile_direction) && strcmp(tile_direction,"TP") == 0) {
    for(col=0; col<n; col++) {
      h_tile[col]=VALUE_ONE;
    }
    
    ifdebug(8) {
      (void) fprintf(stdout,"The hyperplane direction h_tile is :");
      for(col=0; col<n; col++) 
	(void) printf("%d ;",(int)h_tile[col]);
      (void) printf("\n");
    }
    /* computation of the tile scanning base G.  
     */
   scanning_base_hyperplane(h_tile, n, G_tile);
    ifdebug(8) {
      (void) fprintf(stderr,"The tile scanning base G_tile is :");
      matrice_fprint(stderr, G_tile, n, n);
    }
  }
  else matrice_identite(G_tile,n,0);
  
    /* Build the constraints
       0 <= det(HT).[HT. (i -i0)]<det(HT).1 with 
       i0=P.G_tile.i_tile
     <==> 0 <= det(HT).[HT. (i -P.G_tile.i_tile)]<det(HT).1
     <==> 0 <= det(HT).[HT.i -G_tile.i_tile]<= det(HT)-1
  */
  for(row = 1; row <= dim; row++) {
    Pvecteur upper = VECTEUR_NUL;
    Pvecteur lower = VECTEUR_NUL;
    Pcontrainte cupper = CONTRAINTE_UNDEFINED;
    Pcontrainte clower = CONTRAINTE_UNDEFINED;

    for(col = 1, civ = initial_basis; col <= dim; col++, civ = vecteur_succ(civ)) {
      if(ACCESS(HT, dim, row, col)!=VALUE_ZERO) {
	Value coeff = ACCESS(HT, dim, row, col);
	Value offset = vect_coeff(vecteur_var(civ), tiling_offset);

	vect_add_elem(&upper, vecteur_var(civ), coeff);
	vect_add_elem(&upper, TCST, value_uminus(offset*coeff));
     }
    }
    for(col2 = 1, ctv = tile_basis; col2 <= dim; col2++,ctv = vecteur_succ(ctv)) {

      /* Find the origin of the iteration domain. Use 0 as default coordinate */
      if(ACCESS(G_tile, dim, row, col2)!=VALUE_ZERO) {
	Value coeff2 = ACCESS(G_tile, dim,row, col2);
	vect_add_elem(&upper, vecteur_var(ctv), value_uminus(k) *coeff2);	
      }
    }
  
    lower = vect_dup(upper);
    vect_chg_sgn(lower);
    vect_add_elem(&upper, TCST, value_uminus(up));
    cupper = contrainte_make(upper);
    clower = contrainte_make(lower);
    sc_add_inegalite(mc, cupper);
    sc_add_inegalite(mc, clower);
  }
  sc_creer_base(mc);

  ifdebug(8) {
    pips_debug(8, "End with constraint system mc:\n");
    sc_fprint(stderr, mc, (get_variable_name_t)entity_local_name);
  }

  return mc;
}

static void compute_local_change_of_basis( Value *h_tile, matrice P, matrice G, int option, int dim, int selected_Pdim)
{
  int row;
  int col;
  if (option ==1) {
    /* computation of the hyperplane tile direction in the tile basis: = sum(hi)= 1H */
    for(row=0; row<dim; row++) {
      h_tile[row]=VALUE_ZERO;
      for(col=0; col<dim; col++) {
	h_tile[row]+=ACCESS(P, dim, row+1, col+1);
      }
    }
  }
  else if (option==2)
    { /* The local tile direction is colinear to the (selected_Pdim) partitioning vecteur  */
      for(col=0; col<dim; col++) 
	h_tile[col]=ACCESS(P, dim, col+1, selected_Pdim);
    }
  ifdebug(8) {
    (void) fprintf(stdout,"The first scanning direction h_tile in %s mode is :",(option==1)?"LP":"LS");
    for(col=0; col<dim; col++) 
      (void) printf("%d ;",(int)h_tile[col]);
    (void) printf("\n");
  }
  
  /* computation of the local tile scanning base G according to h_tile 
   */
  scanning_base_hyperplane(h_tile, dim, G);
}

Psysteme
local_tile_constraints(Pbase initial_basis,Pbase local_tile_basis, Psysteme sc, matrice P, Pvecteur *pvch, statement st)
{
  Psysteme mc = sc_dup(sc),mc2;
  int dim = base_dimension(initial_basis);
  int row;
  int col;
  Pbase civ = BASE_UNDEFINED;
  Pbase ctv = BASE_UNDEFINED;
  Value *h_tile; // hyperplane direction
  int n = dim; 
  matrice V = matrice_new(n,n);
  matrice G_tile = matrice_new(n,n);
  bool legal=false;
  
  pips_assert("The two bases have the same dimension", dim == base_dimension(local_tile_basis));

  string local_tile_direction = (string) get_string_property("LOCAL_TILE_DIRECTION");
  if (!empty_string_p(local_tile_direction) && strcmp(local_tile_direction,"LI") != 0) {
    h_tile = (Value*)(malloc(n*sizeof(Value)));
    if(strcmp(local_tile_direction,"LP") == 0) {
      /* computation of the hyperplane tile direction in the tile basis: = sum(hi)= 1H */
      compute_local_change_of_basis(h_tile, P, G_tile, 1 , n, 1);
      matrice_general_inversion(G_tile,V,n);
      legal = check_tiling_legality(st,V,n);
      if (!legal)
	matrice_identite(G_tile,n,0); 
    }
    else // search a valid direction colinear to one of the partitioning vectors
      if(strcmp(local_tile_direction,"LS") == 0) {
	int pdim;
	legal=false;
	for (pdim=1; !legal && pdim<=n; pdim++) {
	  /* The local tile direction is legal and colinear to the partitioning vecteur (pdim) */
	  compute_local_change_of_basis(h_tile, P, G_tile, 2, n, pdim);
	  ifdebug(8) {
	    fprintf(stderr,"Check the legality of the chosen LOCAL basis");
	    (void) fprintf(stderr,"Temporary local tile scanning base G_tile obtained with %d-th Pvecteur :",pdim);
	    matrice_fprint(stderr, G_tile, n, n);
	  }
	  matrice_general_inversion(G_tile,V,n);
	  legal = check_tiling_legality(st,V,n);
	}
	if (pdim>n && !legal)
	  matrice_identite(G_tile,n,0);  
      }
  }
  else // the local tile direction is the original basis
    matrice_identite(G_tile,n,0);
  
  ifdebug(8) {
    (void) fprintf(stderr,"The local tile scanning base G_tile - i = G_tile.i_prime is :");
    matrice_fprint(stderr, G_tile, n, n);
  }
  /* Build the constraints
     0 <= det(HT).[HT. (i -i0)]<det(HT).1 with 
     i0=P.G_tile.i_tile
     <==> 0 <= det(HT).[HT. (i -P.G_tile.i_tile)]<det(HT).1
     <==> 0 <= det(HT).[HT.i -G_tile.i_tile]<= det(HT)-1
  */
  for(ctv = local_tile_basis; !VECTEUR_NUL_P(ctv) ; ctv = vecteur_succ(ctv)) {
    base_add_variable(mc->base,vecteur_var(ctv));
    sc_dimension(mc)++;
  }
  for(row = 1, civ = initial_basis;  row <= dim; row++, civ = vecteur_succ(civ)) {
    Pvecteur veq = vect_new(vecteur_var(civ),VALUE_ONE);
    Pcontrainte ceq = CONTRAINTE_UNDEFINED;

    for(col = 1, ctv = local_tile_basis; col <= dim ; col++, ctv = vecteur_succ(ctv)) {
      if(ACCESS(G_tile, dim, row, col)!=VALUE_ZERO) {
	Value coeff = ACCESS(G_tile, dim, row, col);
	vect_add_elem(&veq, vecteur_var(ctv), -1*coeff);
      }
    }  
    ceq = contrainte_make(veq);
    sc_add_egalite(mc, ceq);
  }

  ifdebug(8) {
    pips_debug(8, "End with constraint system mc:\n");
    sc_fprint(stderr, mc, (get_variable_name_t)entity_local_name);
    fprintf(stderr, "sc dimension = %d \n",mc->dimension);
  }
  mc2=sc_dup(mc);
  sc_projection_along_variables_ofl_ctrl(&mc2,initial_basis , OFL_CTRL);
  ifdebug(8) {
    pips_debug(8, "End with constraint system mc after change of basis:\n");
    sc_fprint(stderr, mc, (get_variable_name_t)entity_local_name);
  }
  scanning_base_to_vect(G_tile, n, local_tile_basis, pvch);
  return mc2;
}


Pvecteur
loop_nest_to_offset(list lls)
{
    Pvecteur origin = VECTEUR_NUL;
    list cs = list_undefined;

    for (cs = lls; cs != NIL; cs = CDR(cs)){
	loop l = instruction_loop(statement_instruction(STATEMENT(CAR(cs))));
	entity ind = loop_index(l);
	range r = loop_range(l);
	expression lower = range_lower(r);
	intptr_t val;

	if(expression_integer_value(lower, &val)) {
	    vect_chg_coeff(&origin, (Variable) ind, (Value) val);
	}
    }

    return origin;
}

/* Generate tiled code for a loop nest, PPoPP'91, p. 46, Figure 15.
 *
 * The row-echelon algorithm is called from new_loop_bound().
 */

statement tiling_transformation(list lls, _UNUSED_ bool (*u)(statement))
{
    Psysteme sci;			/* iteration domain */
    Psysteme sc_tile_scan;
    Psysteme sc_tile;
    Psysteme mc = SC_UNDEFINED; /* Tile membership constraints */
    Psysteme sc_B_prime = SC_UNDEFINED;
    Psysteme sc_B_second = SC_UNDEFINED;
    Pbase initial_basis = NULL;
    Pbase tile_basis = NULL;
    Pbase reverse_tile_basis = NULL;
    /* Pbase local_basis = NULL; */
    Pbase new_basis = NULL;
    matrice P; /* Partitioning matrix */
    matrice HT; /* Transposed matrix of the inverse of P */
    matrice G; /* Change of basis in the tile space to use vector 1 as hyperplane direction */
    int n;				/* number of indices, i.e. loop nest depth */
    Value *h;
    statement s_lhyp;
    Pvecteur *pvg;
    Pbase pb;
    expression lower, upper;
    int col;
    Pvecteur to = VECTEUR_NUL; /* Tiling offset: 0 by default */

    debug_on("TILING_DEBUG_LEVEL");

    pips_debug(8, "Begin with iteration domain:\n");

    /* make the constraint system for the iteration space and find a good
       origin for the tiling */

    const char* smatrix = get_string_property("LOOP_TILING_MATRIX");

    if (get_bool_property("PARTIAL_LOOP_TILING")) {
      int ndim=0;
      if (smatrix && !string_undefined_p(smatrix) && !empty_string_p(smatrix))
	for (int k=1; k <=(int)strlen(smatrix); k++)
	  if (smatrix[k]==',') ndim++;
      if (ndim!=0 && ndim<(int)gen_length(lls)-1) {
	for (int k =1; k< (int)gen_length(lls)-ndim && lls != NIL; k++)
	  lls=CDR(lls);
      }
    }
    
    sci = loop_iteration_domaine_to_sc(lls, &initial_basis);
    n = base_dimension(initial_basis);
    to = loop_nest_to_offset(lls);
    ifdebug(8) {
      sc_fprint(stderr, sci, (get_variable_name_t)entity_local_name);
      pips_debug(8,"And with origin:\n");
      vect_fprint(stderr, to, (get_variable_name_t)entity_local_name);
    }

    /* computation of the partitioning matrix P and its inverse HT */

    P = matrice_new(n, n);
    HT = matrice_new(n, n);
    if(
       !static_partitioning_matrix(P,n,smatrix) &&
       !interactive_partitioning_matrix(P, n)
       ) {
      pips_user_error("A proper partitioning matrix was not provided\n");
    }

    ifdebug(8) {
      pips_debug(8,"Partitioning matrix P:");
      matrice_fprint(stderr, P, n, n);
      (void) fprintf(stderr,"\n");
    }

    matrice_general_inversion(P, HT, n);
    
    ifdebug(8) {
      pips_debug(8,"Inverse partitioning matrix HT:");
      matrice_fprint(stderr, HT, n, n);
      (void) fprintf(stderr,"\n");
    }

    /* Compute B': each iteration i in the iteration space is linked to its tile s */

    derive_new_basis(initial_basis, &tile_basis, make_tile_index_entity);
     mc = tile_membership_constraints(initial_basis, tile_basis, HT, to);
    mc = sc_normalize(mc);
    ifdebug(8) {
	(void) fprintf(stderr,"Tile membership constraints:\n");
	sc_fprint(stderr, mc, (get_variable_name_t)entity_local_name);
    }
    /* mc and SC_B_prime are aliased after this call */
    sc_B_prime = sc_append(mc, sci);
    ifdebug(8) {
	(void) fprintf(stderr,"sc_B_prime after call to sc_append (is the basis ok?):\n");
	sc_fprint(stderr, sc_B_prime, (get_variable_name_t)entity_local_name);
    }

  
    mc = SC_UNDEFINED;
    /* Save a copy to compute B" later */
    sc_B_second = sc_dup(sc_B_prime);

    /* Get constraints on tile coordinates */

    sc_projection_along_variables_ofl_ctrl(&sc_B_prime, initial_basis, OFL_CTRL);
    ifdebug(8) {
	(void) fprintf(stderr,"Tile domain:\n");
	sc_fprint(stderr, sc_B_prime, (get_variable_name_t)entity_local_name);
    }

    /* Build the constraint system to scan the set of tiles */
    sc_tile_scan = new_loop_bound(sc_B_prime, tile_basis);
    ifdebug(8) {
	(void) fprintf(stderr,"Tile domain in echelon format:\n");
	sc_fprint(stderr, sc_tile_scan, (get_variable_name_t)entity_local_name);
    }

    /* CA: Build the new basis (tile_basis+initial_basis)*/
    /* base It, Jt, I, J  pour notre exemple */
    new_basis = vect_add(vect_dup(initial_basis),vect_dup(tile_basis));
    ifdebug(8) {
	(void) fprintf(stderr,"new_basis\n");
	vect_fprint(stderr, new_basis, (get_variable_name_t)entity_local_name);
    }

    /* Build the constraint system sc_tile to scan one tile (BS IN
       PPoPP'91 paper) */
    ifdebug(8) {
	(void) fprintf(stderr,"sc_B_second:\n");
	sc_fprint(stderr, sc_B_second, (get_variable_name_t)entity_local_name);
    }
    sc_tile = new_loop_bound(sc_B_second, new_basis);
    ifdebug(8) {
	(void) fprintf(stderr,"Iteration domain for one tile:\n");
	sc_fprint(stderr, sc_tile, (get_variable_name_t)entity_local_name);
    }

    /* computation of the hyperplane tile direction: let's use the
       default 1 vector */
    h = (Value*)(malloc(n*sizeof(Value)));
    for(col=0; col<n; col++) {
	h[col] = VALUE_ONE;
    }
    /* computation of the tile scanning base G: right now, let's
     * assume it's Id.  This is OK to tile parallel loops... or to
     * scan tiles sequentially on a monoprocessor.
     */
    G = matrice_new(n,n);
    scanning_base_hyperplane(h, n, G);
    ifdebug(8) {
	(void) fprintf(stderr,"The tile scanning base G is before ID:");
	matrice_fprint(stderr, G, n, n);
    }
    matrice_identite(G, n, 0);
    ifdebug(8) {
	(void) fprintf(stderr,"The tile scanning base G is:");
	matrice_fprint(stderr, G, n, n);
    }

    /* generation of code for scanning one tile */

    /* Compute the local coordinate changes: there should be none for the time being
     * because we keep the initial basis to scan iterations within one tile, i.e
     * G must be the identity matrix
     */
    pvg = (Pvecteur *)malloc((unsigned)n*sizeof(Svecteur));
    scanning_base_to_vect(G, n, initial_basis, pvg);
     ifdebug(8) {
      (void) fprintf(stderr,"The local coordinate change vector is:");
      for (int i=1; i<=n; i++)
	vect_fprint(stderr, pvg[i], (get_variable_name_t)entity_local_name);
    }
    /* generation of code to scan one tile, and update of loop body using pvg */

    s_lhyp = code_generation(lls, pvg, initial_basis,
			     new_basis, sc_tile, false);

    /* generation of code for scanning all tiles */

    reverse_tile_basis = base_reversal(tile_basis);
    for (pb = reverse_tile_basis; pb!=NULL; pb=pb->succ) {
	loop tl = loop_undefined;

	make_bound_expression(pb->var, tile_basis, sc_tile_scan, &lower, &upper);
	tl = make_loop((entity) vecteur_var(pb),
		       make_range(copy_expression(lower), copy_expression(upper),
				  int_to_expression(1)),
		       s_lhyp,
		       entity_empty_label(),
		       make_execution(is_execution_sequential, UU),
		       NIL);
	s_lhyp = instruction_to_statement(make_instruction(is_instruction_loop, tl));
    }

    pips_debug(8,"End\n");

    debug_off();

    return(s_lhyp);
}

bool loop_tiling(const char* module_name)
{
    bool return_status = false;

    return_status = interactive_loop_transformation(module_name,  (statement (*)(list, bool (*)(statement)))tiling_transformation);
    
    return return_status;
}



static bool statement_in_loopnest_p = false;
static statement test_statement_of_reference;
static void statement_in_loopnest(statement s)
{
  if (statement_number(test_statement_of_reference) == statement_number(s))
    statement_in_loopnest_p= true;
}

/*
   Check that H.v >0
   v is a dependence vecteur  or a dependence vertex expressed in base b
   Matrice H  is the tiling scanning base, expressed in base b.
 */
static void legal_point_p(Pvecteur v, Ptsg gs, matrice H,int dim, bool *legal)
{
  Pbase b=gs->base;
  Pvecteur coord;
  int row, col, accu;
  if(vect_in_basis_p(v, b)) {
    for (row=1; row<=dim; row++) {
      accu = 0;
      for(coord = b, col=1; !VECTEUR_NUL_P(coord) && col<=dim; coord = coord->succ,col++) {
	Variable var = vecteur_var(coord);
	if(VARIABLE_DEFINED_P(var)) {
	  accu += vect_coeff(var, v)*ACCESS(H, dim, row, col);
	}
      }
      if (accu <0) {
	ifdebug(8) {
	  pips_debug(8,"Tile scanning matrix H:");
	  fprintf(stdout,"NON LEGAL TILING: H(%d,*)*SG =%d <0\n", row,accu);
	  sg_fprint_as_dense(stdout, gs, gs->base );
	}
	*legal=(*legal) && false;
      }
      else  {
	ifdebug(8) {
	  pips_debug(8,"Tile scanning matrix H:");
	  fprintf(stdout,"LEGAL TILING: H(%d,*)*SG =%d >=0\n", row,accu);
	  sg_fprint_as_dense(stdout, gs, gs->base );
	}
      }			
    }		      
  }
}

static void check_positive_dependence(Ptsg gs, matrice H,int dim, bool *legal)
{
  if( sg_nbre_rayons(gs) > 0) {
    for (Pray_dte e = sg_rayons(gs); e != NULL; e = e->succ) {
      legal_point_p(e->vecteur, gs, H,dim, legal);
    }
  }
  if( legal && sg_nbre_droites(gs) > 0) {
    for (Pray_dte e = sg_droites(gs); e != NULL; e = e->succ) {
      Pvecteur v=vect_copy(e->vecteur);
      legal_point_p(e->vecteur, gs, H,dim, legal);
      vect_chg_sgn(v);
      legal_point_p(e->vecteur, gs, H,dim, legal);
      vect_rm(v);
    }
  }
  if( legal && sg_nbre_sommets(gs) > 0) {
    for (Psommet e = sg_sommets(gs); e != NULL; e = e->succ) {
      legal_point_p(e->vecteur, gs, H,dim, legal);
    }
  }
}
/*
   Test whether H.D >0. 
   Returns TRUE if ok, FALSE otherwise
   D is dependence cone (vertex, rays, lines) in base b 
     among all the dependence conflicts belonging to loopnest
   Matrice H is a squared matrix of dimension dim. 
   It is the tiling scanning base, expressed in base b.
 */
bool check_tiling_legality(statement loopnest_st, matrice H,int dim)
{
  const char * module_name = get_current_module_name();
  graph dg = (graph) db_get_memory_resource(DBR_DG, module_name, true);
   int bl;
   matrice HC;
  // statement mod_stat = get_current_module_statement();
  bool legal=true;
  FOREACH(VERTEX,v,graph_vertices(dg)) {
    statement s = vertex_to_statement(v);
    // Verify s is a statement in the loop nest
    statement_in_loopnest_p= false;
    test_statement_of_reference = s;
    gen_recurse(loopnest_st, statement_domain, gen_true,statement_in_loopnest);
	
    if(statement_in_loopnest_p) {
      FOREACH(SUCCESSOR,su,vertex_successors(v)) {
	      
	vertex v2 = successor_vertex(su);
	statement s2 = vertex_to_statement( v2 );
	// Verify s2 is a statement in the loop nest      
	statement_in_loopnest_p= false;
	test_statement_of_reference = s2;
	gen_recurse(loopnest_st, statement_domain, gen_true,statement_in_loopnest);
	
	if(statement_in_loopnest_p) { // s and s2 are in the loop nest
	  FOREACH(CONFLICT,c,dg_arc_label_conflicts(successor_arc_label(su))) {
                       
	    if ( conflict_cone(c) != cone_undefined ) {
	      //test H.D >0 for sommets, rays, and lines	    
	      Ptsg gs = (Ptsg) cone_generating_system(conflict_cone(c));
	      if( !SG_UNDEFINED_P(gs)) {
		Pbase b=gs->base;
		bl=vect_size(b);
		
		if (bl==dim)
		  check_positive_dependence(gs, H,dim, &legal);
		else {
		  if (bl > dim) {
		    HC=matrice_new(bl,bl);
		    int row,col;
		    ifdebug(8) {
		      fprintf(stdout," Different SIZES for base %d and matrice %d, Partial tiling case ?\n",bl,dim);
		    }
		    // Complete matrix Ht for the first non tiled dimension of the loop nest
		    // for 1<=i<=bl-dim, if di!=0  hji>=loop increment
		    // only loop with increment 1 are tiled ==> hji =1
		    matrice_identite(HC,bl,0);
		    DENOMINATOR(HC)=DENOMINATOR(H);
		    for (row=1; row<=bl; row++) {
		      if (row>=bl-dim+1) {
			for(col=1;  col<bl-dim+1;col++) {
			  ACCESS(HC, bl, row, col)=DENOMINATOR(H) ;
			}
			for(col=bl-dim+1;  col<=bl;col++) {
			  ACCESS(HC, bl, row, col)= ACCESS(H, dim, row-bl+dim, col-bl+dim);
			}
		      }
		      else {
			ACCESS(HC, bl, row, row)=DENOMINATOR(H);
		      }
		    }
		    check_positive_dependence(gs, HC,bl, &legal);
		    matrice_free(HC);
		  }
		  else
		    pips_user_warning(" Different SIZES for dependence cone basis %d and partitioning matrice %d\n",bl,dim);
		}
	      }
	    }
	  }
	}
      }
    }
  }
  return(legal);
}

Psysteme sc_projection_concat_proj_on_variables(
  Psysteme sc,
  Pbase index_base)
{
  Pvecteur lvar_proj;
  Psysteme sc1 = sc_dup(sc);
  int nb=vect_size(index_base);
  // Automatic variables read in a CATCH block need to be declared volatile as
  // specified by the documentation
  volatile Psysteme sc2,sc3;
   sc3=sc_init_with_sc(sc);
   
  if (!VECTEUR_NUL_P(index_base))
  {
    volatile Pvecteur pv1;
    lvar_proj = vect_copy(base_reversal(index_base));
    sc2 = sc_copy(sc);
    for (pv1 = lvar_proj;!VECTEUR_NUL_P(pv1) && nb>1; pv1=pv1->succ, nb--) {
	    
      CATCH(overflow_error) {
	sc_elim_var(sc2, vecteur_var(pv1));
      }
      TRY {// force the overflow forwarding in order to apply sc_elim_var in case of overflow
	sc_projection_along_variable_ofl_ctrl
	  (&sc2,vecteur_var(pv1), FWD_OFL_CTRL);
	UNCATCH(overflow_error);
      }
      sc2 = sc_normalize(sc2);
      if (SC_EMPTY_P(sc2)) {
	sc2 = sc_empty(base_copy(sc->base));
	break;
      }
      else {
        build_sc_nredund_1pass(&sc2);
      }
      // Concatenation of the intermediate system sc2 resulting
      // from the projection of pv1 and the previous concatenated system sc3
      sc3 = sc_append(sc3,sc2);
      if (SC_EMPTY_P(sc3)) {
	sc3 = sc_empty(base_copy(sc->base));
	break;
      }
    }
  }
  sc1 = sc_append(sc1,sc3);
  sc1 = sc_normalize(sc1);
  if (SC_EMPTY_P(sc1))
    sc1 = sc_empty(base_copy(sc->base));     
  return sc1;
}


statement parallel_tiling(list lls, _UNUSED_ bool (*u)(statement))
{
    Psysteme sci;			/* iteration domain */
    Psysteme sc_tile;
    Psysteme sc_local_tile;
    Psysteme mc = SC_UNDEFINED; /* Tile membership constraints */
    Psysteme sc_B_prime = SC_UNDEFINED;
    Psysteme sc_B_prime_2 = SC_UNDEFINED;
    Pbase initial_basis = NULL;
    Pbase tile_basis = NULL;
    Pbase local_tile_basis = NULL;
    Pbase reverse_tile_basis = NULL;
    Pbase new_basis = NULL;
    matrice P; /* Partitioning matrix */
    matrice HT; /* Transposed matrix of the inverse of P */
    int n,i;				/* number of indices, i.e. loop nest depth */
    statement s_lhyp;
    Pvecteur *pvch;
    Pbase pb;
    expression lower, upper;
    Pvecteur to = VECTEUR_NUL; /* Tiling offset: 0 by default */
    statement stmf = statement_undefined;
    list lls2; // first loop in the loop nest;
#define maxscinfosize 100
    int sc_info[maxscinfosize][4];
    Psysteme sc_proj2,sc_tmp;
    int space;
    Psysteme *list_of_systems;
    statement mod_stat = get_current_module_statement();
    set_ordering_to_statement(mod_stat);

    debug_on("TILING_DEBUG_LEVEL");
    pips_debug(8, "Begin with iteration domain:\n");
    const char* smatrix = get_string_property("LOOP_TILING_MATRIX");

    if (get_bool_property("PARTIAL_LOOP_TILING")) {
      int ndim=0;
      if (smatrix && !string_undefined_p(smatrix) && !empty_string_p(smatrix))
	for (int k=1; k <=(int)strlen(smatrix); k++)
	  if (smatrix[k]==',') ndim++;
      if (ndim!=0 && ndim<(int)gen_length(lls)-1) {
	for (int k =1; k< (int)gen_length(lls)-ndim && lls != NIL; k++)
	  lls=CDR(lls);
      }
    }
    // keep the original statement in case of NOT legal tiling
    for (lls2=lls;(int)gen_length(lls2)>1 && lls2 != NIL; lls2=CDR(lls2));
    stmf=STATEMENT(CAR(lls2));

    sci = loop_iteration_domaine_to_sc(lls, &initial_basis);
    n = base_dimension(initial_basis);
    to = loop_nest_to_offset(lls);
    ifdebug(8) {
      sc_fprint(stderr, sci, (get_variable_name_t)entity_user_name);
      pips_debug(8,"And with origin:\n");
      vect_fprint(stderr, to, (get_variable_name_t)entity_user_name);
    }

    /* computation of the partitioning matrix P and its inverse HT */
    P = matrice_new(n, n);
    HT = matrice_new(n, n);
    if(
       !static_partitioning_matrix(P,n,smatrix) &&
       !interactive_partitioning_matrix(P, n)
       ) {
      pips_user_error("A proper partitioning matrix was not provided\n");
    }

    ifdebug(8) {
      pips_debug(8,"Partitioning matrix P:");
      matrice_fprint(stderr, P, n, n);
      (void) fprintf(stderr,"\n");
    }
    matrice_general_inversion(P, HT, n);  
    ifdebug(8) {
      pips_debug(8,"Inverse partitioning matrix HT = P^-1:");
      matrice_fprint(stderr, HT, n, n);
      (void) fprintf(stderr,"\n");
    }  
    /* make the constraint system for the iteration space and find a good
       origin for the tiling if the transformation is legal*/
    if (!get_bool_property("CHECK_TRANSFORMATION_LEGALITY") || check_tiling_legality(STATEMENT(CAR(lls2)),HT,n)) {
      
      derive_new_basis(initial_basis, &tile_basis, make_tile_index_entity);
      derive_new_basis(initial_basis, &local_tile_basis, make_local_tile_index_entity);
      /* Compute B': each iteration i in the iteration space is linked to its tile s */
     
      mc = tile_hyperplane_constraints(initial_basis, tile_basis, HT, to);
      mc = sc_normalize(mc);
      ifdebug(8) {
	(void) fprintf(stderr,"Tile membership constraints:\n");
	sc_fprint(stderr, mc, (get_variable_name_t)entity_user_name);
      }
      /* mc and SC_B_prime are aliased after this call */
      sc_B_prime = sc_append(mc, sci);
      ifdebug(8) {
	(void) fprintf(stderr,"sc_B_prime after call to sc_append :\n");
	sc_fprint(stderr, sc_B_prime, (get_variable_name_t)entity_user_name);
      }

      /* computation of the base scanning local tile elements and its constraints*/
      pvch = (Pvecteur *)malloc((unsigned)n*sizeof(Svecteur));
      sc_B_prime_2= local_tile_constraints(initial_basis,local_tile_basis,sc_B_prime, P, pvch, STATEMENT(CAR(lls2)));

      ifdebug(8) {
	(void) fprintf(stderr,"sc_B_prime2 after change of local basis:\n");
	sc_fprint(stderr, sc_B_prime_2, (get_variable_name_t)entity_user_name);
      }

      /* Build the new basis (tile_basis+local_tile_basis)*/
      new_basis = vect_add(vect_dup(local_tile_basis),vect_dup(tile_basis));
      ifdebug(8) {
	(void) fprintf(stderr,"new_basis\n");
	vect_fprint(stderr, new_basis, (get_variable_name_t)entity_user_name);
      }
      {
	sc_tmp= sc_dup(sc_B_prime_2);
	space = (vect_size(new_basis)+1) * sizeof(Ssysteme);
	list_of_systems = (Psysteme *) malloc((unsigned) space);
	 
	sc_proj2 = sc_dup(sc_B_prime_2);
	// Add redundant constraints on intermediate loop indices to improve the generated code
	sc_proj2 = sc_projection_concat_proj_on_variables(sc_proj2,new_basis);
	sc_integer_projection_information(sc_proj2,new_basis, sc_info,sc_proj2->dimension,sc_proj2->dimension);
	sc_proj2=build_integer_sc_nredund(sc_proj2,new_basis,sc_info,1,sc_proj2->dimension,sc_proj2->dimension);

	// Distribute constraints according to loop nest indices of new_basis
	for (i=1;i<=sc_proj2->dimension;i++)
	  list_of_systems[i] = sc_init_with_sc(sc_proj2);
	constraint_distribution(sc_proj2,list_of_systems,new_basis,sc_info);

	// Remove redundant constraints according to the cumulated constraints from outer to inner loop bounds
	sc_tmp=sc_dup(list_of_systems[1]);
	for (i = 2; sc_tmp != NULL && i <=vect_size(new_basis);i++) {
	  list_of_systems[i] = elim_redund_sc_with_sc(list_of_systems[i],
						      sc_tmp,
						      new_basis,
						      vect_size(new_basis));
	  ifdebug(8) {
	    fprintf(stdout," Constraints on the %d-th var. :\n",i);
	    sc_fprint(stdout,list_of_systems[i],(get_variable_name_t)entity_user_name);
	  }
	  sc_tmp=sc_intersection(sc_tmp,sc_tmp,list_of_systems[i]);	
	}
	sc_rm(sc_tmp);
     
      // Build  system sc_tile to scan one tile
	sc_tile =sc_dup(list_of_systems[1]);
	for (i=2; i<=vect_size(tile_basis);i++)
	  sc_tile =sc_intersection(sc_tile,sc_tile,list_of_systems[i]);
	ifdebug(8) {
	  (void) fprintf(stderr,"Tile domain in echelon format:\n");
	  sc_fprint(stderr, sc_tile, (get_variable_name_t)entity_user_name);
	}
	// Constraint system sc_tile to scan one tile
	sc_local_tile =sc_dup(list_of_systems[i]);
	i++;
	for (; i<=vect_size(tile_basis)+vect_size(local_tile_basis);i++)
	  sc_local_tile =sc_intersection(sc_local_tile,sc_local_tile,list_of_systems[i]);
	ifdebug(8) {
	  (void) fprintf(stderr,"Iteration domain for one tile:\n");
	  sc_fprint(stderr, sc_local_tile, (get_variable_name_t)entity_user_name);
	}
      }
      
      /* generation of code for scanning one tile */
      ifdebug(8) {
	(void) fprintf(stderr,"The local coordonate change vector is:");
	for (int i=1; i<=n; i++)
	  vect_fprint(stderr, pvch[i], (get_variable_name_t)entity_user_name);
      }
      /* generation of code to scan one tile and update of loop body using pvch */
      s_lhyp = code_generation(lls, pvch, initial_basis,
			       local_tile_basis, sc_local_tile, false);

     /* generation of code for scanning all tiles */
     reverse_tile_basis = base_reversal(tile_basis);
     for (pb = reverse_tile_basis; pb!=NULL; pb=pb->succ) {
       loop tl = loop_undefined;

       make_bound_expression(pb->var, tile_basis, sc_tile, &lower, &upper);
       tl = make_loop((entity) vecteur_var(pb),
		      make_range(copy_expression(lower), copy_expression(upper),
				 int_to_expression(1)),
		      s_lhyp,
		      entity_empty_label(),
		      make_execution(is_execution_sequential, UU),
		      NIL);
       s_lhyp = instruction_to_statement(make_instruction(is_instruction_loop, tl));
     }
     stmf =s_lhyp; 
    }
    else pips_user_warning("PIPS legality test for Tiling transformation NOT VERIFIED, Verify data dependencies or simplify array access functions\n");
    
    pips_debug(8,"End\n");

    debug_off();
    reset_ordering_to_statement();
    return(stmf);
}

bool parallel_loop_tiling(const char* module_name)
{
  bool return_status = false;
    return_status = interactive_loop_transformation(module_name, parallel_tiling);
    return return_status;
}
