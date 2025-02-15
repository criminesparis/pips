/*

  $Id: matrix.c 1671 2019-06-26 19:14:11Z coelho $

  Copyright 1989-2016 MINES ParisTech

  This file is part of Linear/C3 Library.

  Linear/C3 Library is free software: you can redistribute it and/or modify it
  under the terms of the GNU Lesser General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  any later version.

  Linear/C3 Library is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
  FITNESS FOR A PARTICULAR PURPOSE.

  See the GNU Lesser General Public License for more details.

  You should have received a copy of the GNU Lesser General Public License
  along with Linear/C3 Library.  If not, see <http://www.gnu.org/licenses/>.

*/

 /* package matrix */

#ifdef HAVE_CONFIG_H
    #include "config.h"
#endif

#include <stdio.h>
#include <stdlib.h>
#include <stdlib.h>
#include "linear_assert.h"

#include "boolean.h"
#include "arithmetique.h"

#include "matrix.h"

Value * matrix_elem_ref(Pmatrix M, int r, int c)
{
  assert(M != NULL && M->coefficients != NULL);
  assert(1 <= r && r <= M->number_of_lines);
  assert(1 <= c && c <= M->number_of_columns);
  return &(MATRIX_ELEM(M, r, c));
}

Value matrix_elem(Pmatrix M, int r, int c)
{
  assert(M != NULL && M->coefficients != NULL);
  assert(1 <= r && r <= M->number_of_lines);
  assert(1 <= c && c <= M->number_of_columns);
  // return M->coefficients[(c-1) * M->number_of_lines + r - 1];
  return MATRIX_ELEM(M, r, c);
}

/* void matrix_transpose(Pmatrix a, Pmatrix a_t):
 * transpose an (nxm) rational matrix a into a (mxn) rational matrix a_t
 *
 *        t
 * At := A ;
 */
void matrix_transpose(const Pmatrix	A, Pmatrix	At)
{
  /* verification step */
  int m = MATRIX_NB_LINES(A);
  int n = MATRIX_NB_COLUMNS(A);
  assert(n >= 0 && m >= 0);

  /* copy from a to a_t */
  MATRIX_DENOMINATOR(At) = MATRIX_DENOMINATOR(A);
  int i, j;
  for(i=1; i<=m; i++)
    for(j=1; j<=n; j++)
	    MATRIX_ELEM(At,j,i) = MATRIX_ELEM(A,i,j);
}

/* void matrix_multiply(Pmatrix a, Pmatrix b, Pmatrix c):
 * multiply rational matrix a by rational matrix b and store result in matrix c
 *
 *	a is a (pxq) matrix, b a (qxr) and c a (pxr)
 *
 *      c := a x b ;
 *
 * Algorithm used is directly from definition, and space has to be
 * provided for output matrix c by caller. Matrix c is not necessarily
 * normalized: its denominator may divide all its elements
 * (see matrix_normalize()).
 *
 * Precondition:	p > 0; q > 0; r > 0;
 *                      c != a; c != b; -- aliasing between c and a or b
 *                                      -- is not supported
 */
void matrix_multiply(const Pmatrix a, const Pmatrix b, Pmatrix c)
{
  /* validate dimensions */
  int	p = MATRIX_NB_LINES(a);
  int	q = MATRIX_NB_COLUMNS(a);
  int	r = MATRIX_NB_COLUMNS(b);
  // should check that all dimensions are compatible & well allocated?!

  assert(p > 0 && q > 0 && r > 0);
  /* simplified aliasing test */
  assert(c != a && c != b);

  /* set denominator */
  MATRIX_DENOMINATOR(c) =
    value_mult(MATRIX_DENOMINATOR(a), MATRIX_DENOMINATOR(b));

  /* use ordinary school book algorithm */
  int i, j, k;
  for(i=1; i<=p; i++) {
    for(j=1; j<=r; j++) {
	    Value v = VALUE_ZERO;
	    for(k=1; k<=q; k++) {
        Value va = MATRIX_ELEM(a, i, k);
        Value vb = MATRIX_ELEM(b, k, j);
        value_addto(v, value_mult(va, vb));
	    }
	    MATRIX_ELEM(c, i, j) = v;
    }
  }
}

/* void matrix_normalize(Pmatrix a)
 *
 *	A rational matrix is stored as an integer one with one extra
 *	integer, the denominator for all the elements. To normalise the
 *	matrix in this sense means to reduce this denominator to the
 *	smallest positive number possible. All elements are also reduced
 *      to their smallest possible value.
 *
 * Precondition: MATRIX_DENOMINATOR(a)!=0
 */
void matrix_normalize(Pmatrix	a)
{
  int m = MATRIX_NB_LINES(a);
  int n = MATRIX_NB_COLUMNS(a);
  assert(MATRIX_DENOMINATOR(a) != 0);

  /* we must find the GCD of all elements of matrix */
  Value factor = MATRIX_DENOMINATOR(a);

  int i, j;
  for(i=1; i<=m; i++)
    for(j=1; j<=n; j++)
	    factor = pgcd(factor, MATRIX_ELEM(a,i,j));

  /* factor out */
  if (value_notone_p(factor)) {
    for(i=1; i<=m; i++)
	    for(j=1; j<=n; j++)
        value_division(MATRIX_ELEM(a,i,j), factor);
    value_division(MATRIX_DENOMINATOR(a),factor);
  }

  /* ensure denominator is positive */
  /* FI: this code is useless because pgcd()always return a positive integer,
     even if a is the null matrix; its denominator CANNOT be 0 */
  assert(value_pos_p(MATRIX_DENOMINATOR(a)));

/*
    if(MATRIX_DENOMINATOR(a) < 0) {
	MATRIX_DENOMINATOR(a) = MATRIX_DENOMINATOR(a)*-1;
	for(loop1=1; loop1<=n; loop1++)
	    for(loop2=1; loop2<=m; loop2++)
		MATRIX_ELEM(a,loop1,loop2) = 
		    -1 * MATRIX_ELEM(a,loop1,loop2);
    }*/
}

/* void matrix_normalizec(Pmatrix MAT):
 *  Normalisation des coefficients de la matrice MAT, i.e. division des
 *  coefficients de la matrice MAT et de son denominateur par leur pgcd
 *
 *  La matrice est modifiee.
 *
 *  Les parametres de la fonction :
 *
 *!int MAT[]	: matrice  de dimension (n,m)
 * int  n	: nombre de lignes de la matrice
 * int  m 	: nombre de colonnes de la matrice
 *
 * ??? matrix is supposed to be positive?
 */
void matrix_normalizec(Pmatrix MAT)
{
  int m = MATRIX_NB_LINES(MAT);
  int n = MATRIX_NB_COLUMNS(MAT);
  assert( n>0 && m>0);

  Value a = MATRIX_DENOMINATOR(MAT);
  int i;
  for (i = 0; i<m*n  && value_gt(a, VALUE_ONE); i++)
    a = pgcd(a, MAT->coefficients[i]);

  if (value_gt(a,VALUE_ONE)) {
    for (i = 0; i<m*n; i++)
	    value_division(MAT->coefficients[i],a);
  }
}

/* void matrix_swap_columns(Pmatrix a, int c1, int c2):
 * exchange columns c1,c2 of an (nxm) rational matrix
 *
 *	Precondition:	n > 0; m > 0; 0 < c1 <= m; 0 < c2 <= m;
 */
void matrix_swap_columns(Pmatrix A, int	c1, int c2)
{
  int m = MATRIX_NB_LINES(A);
  int n = MATRIX_NB_COLUMNS(A);
  assert(n > 0 && m > 0);
  assert(0 < c1 && c1 <= n);
  assert(0 < c2 && c2 <= n);

  int i;
  for(i=1; i<=m; i++) {
    Value temp = MATRIX_ELEM(A,i,c1);
    MATRIX_ELEM(A,i,c1) = MATRIX_ELEM(A,i,c2);
    MATRIX_ELEM(A,i,c2) = temp;
  }
}

/* void matrix_swap_rows(Pmatrix a, int r1, int r2):
 * exchange rows r1 and r2 of an (nxm) rational matrix a
 *
 * Precondition: n > 0; m > 0; 1 <= r1 <= n; 1 <= r2 <= n
 */
void matrix_swap_rows(Pmatrix A, int r1, int r2)
{
  int m = MATRIX_NB_LINES(A);
  int n = MATRIX_NB_COLUMNS(A);
  assert(n > 0);
  assert(m > 0);
  assert(0 < r1 && r1 <= m);
  assert(0 < r2 && r2 <= m);

  int i;
  for(i=1; i<=n; i++) {
    Value temp = MATRIX_ELEM(A,r1,i);
    MATRIX_ELEM(A,r1,i) = MATRIX_ELEM(A,r2,i);
    MATRIX_ELEM(A,r2,i) = temp;
  }
}

/* void matrix_assign(Pmatrix A, Pmatrix B)
 * Copie de la matrice A dans la matrice B
 *
 *  Les parametres de la fonction :
 *
 * int 	A[]	:  matrice
 *!int 	B[]	:  matrice
 * int  n	: nombre de lignes de la matrice
 * int  m 	: nombre de colonnes de la matrice
 *
 * Ancien nom: matrix_dup
 */
void matrix_assign(Pmatrix  A, Pmatrix B)
{
  int m = MATRIX_NB_LINES(A);
  int n = MATRIX_NB_COLUMNS(A);
  int i;
  for (i=0 ; i<m*n; i++)
    B->coefficients[i] = A->coefficients[i];
}

/* bool matrix_equality(Pmatrix A, Pmatrix B)
 * test de l'egalite de deux matrices A et B; elles doivent avoir
 * ete normalisees au prealable pour que le test soit mathematiquement
 * exact
 */
bool matrix_equality(Pmatrix  A, Pmatrix B)
{
  int m = MATRIX_NB_LINES(A);
  int n = MATRIX_NB_COLUMNS(A);
  int i;
  for (i = 0 ; i < m*n; i++)
    if (B->coefficients[i] != A->coefficients[i])
	    return false;
  return true;
}

/* void matrix_nulle(Pmatrix Z):
 * Initialisation de la matrice Z a la valeur matrice nulle
 *
 * Post-condition:
 *
 * QQ i dans [1..n]
 * QQ j dans [1..n]
 *    Z(i,j) == 0
 */
void matrix_nulle(Pmatrix Z)
{
  int m = MATRIX_NB_LINES(Z);
  int n = MATRIX_NB_COLUMNS(Z);
  int i,j;
  for (i=1; i<=m; i++)
    for (j=1; j<=n; j++)
	    MATRIX_ELEM(Z,i,j) = VALUE_ZERO;
  MATRIX_DENOMINATOR(Z) = VALUE_ONE;
}

/* bool matrix_nulle_p(Pmatrix Z):
 * test de nullite de la matrice Z
 *
 * QQ i dans [1..n]
 * QQ j dans [1..n]
 *    Z(i,j) == 0
 */
bool matrix_nulle_p(Pmatrix Z)
{
  int m = MATRIX_NB_LINES(Z);
  int n = MATRIX_NB_COLUMNS(Z);
  int i, j;
  for (i=1; i<=m; i++)
    for (j=1; j<=n; j++)
	    if (MATRIX_ELEM(Z,i,j) != VALUE_ZERO)
        return false;
  return true;
}

/* bool matrix_diagonal_p(Pmatrix Z):
 * test de nullite de la matrice Z
 *
 * QQ i dans [1..n]
 * QQ j dans [1..n]
 *    Z(i,j) == 0 && i != j || i == j
 *
 *  Les parametres de la fonction :
 *
 * int 	Z[]	:  matrice
 * int  n	: nombre de lignes de la matrice
 * int  m 	: nombre de colonnes de la matrice
 */
bool matrix_diagonal_p(Pmatrix Z)
{
  int i,j;
  int m = MATRIX_NB_LINES(Z);
  int n = MATRIX_NB_COLUMNS(Z);
  for (i=1;i<=m;i++)
    for (j=1;j<=n;j++)
	    if(i!=j && MATRIX_ELEM(Z,i,j)!=0)
        return false;
  return true;
}

/* bool matrix_triangular_p(Pmatrix Z, bool inferieure):
 * test de triangularite de la matrice Z
 *
 * si inferieure == true
 * QQ i dans [1..n]
 * QQ j dans [i+1..m]
 *    Z(i,j) == 0
 *
 * si inferieure == false (triangulaire superieure)
 * QQ i dans [1..n]
 * QQ j dans [1..i-1]
 *    Z(i,j) == 0
 *
 *  Les parametres de la fonction :
 *
 * int 	Z[]	:  matrice
 * int  n	: nombre de lignes de la matrice
 * int  m 	: nombre de colonnes de la matrice
 */
bool matrix_triangular_p(Pmatrix Z, bool inferieure)
{
  int m = MATRIX_NB_LINES(Z);
  int n = MATRIX_NB_COLUMNS(Z);
  int i,j;
  for (i=1; i<=m; i++)
    if(inferieure) {
	    for (j=i+1; j<=n; j++)
        if(MATRIX_ELEM(Z,i,j)!=0)
          return false;
    }
    else
	    for (j=1; j<=i-1; j++)
        if(MATRIX_ELEM(Z,i,j)!=0)
          return false;
  return true;
}

/* bool matrix_triangular_unimodular_p(Pmatrix Z, bool inferieure)
 * test de la triangulaire et unimodulaire de la matrice Z.
 * si inferieure == true
 * QQ i dans [1..n]
 * QQ j dans [i+1..n]
 *    Z(i,j) == 0
 * i dans [1..n]
 *   Z(i,i) == 1
 *
 * si inferieure == false (triangulaire superieure)
 * QQ i dans [1..n]
 * QQ j dans [1..i-1]
 *    Z(i,j) == 0
 * i dans [1..n]
 *   Z(i,i) == 1
 * les parametres de la fonction :
 * matrice Z : la matrice entre
 */
bool matrix_triangular_unimodular_p(Pmatrix Z, bool inferieure)
{
  int m = MATRIX_NB_LINES(Z);
  assert(MATRIX_NB_COLUMNS(Z) == m);
  bool triangulaire = matrix_triangular_p(Z,inferieure);
  if (triangulaire) {
    int i;
    for(i=1; i<=m; i++)
	    if (value_notone_p(MATRIX_ELEM(Z,i,i)))
        return false;
    return true;
  }
  else
    return false;
}

/* void matrix_substract(Pmatrix a, Pmatrix b, Pmatrix c):
 * substract rational matrix c from rational matrix b and store result
 * in matrix a
 *
 *	a is a (nxm) matrix, b a (nxm) and c a (nxm)
 *
 *      a = b - c ;
 *
 * Algorithm used is directly from definition, and space has to be
 * provided for output matrix a by caller. Matrix a is not necessarily
 * normalized: its denominator may divide all its elements
 * (see matrix_normalize()).
 *
 * Precondition:	n > 0; m > 0;
 * Note: aliasing between a and b or c is supported
 */
void matrix_substract(Pmatrix a, Pmatrix b, Pmatrix c)
{
  Value d1,d2;   /* denominators of b, c */
  Value lcm;     /* ppcm of b,c */
  int i,j;

  /* precondition */
  int m = MATRIX_NB_LINES(a);
  int n = MATRIX_NB_COLUMNS(a);
  assert(n>0 && m>0);
  assert(value_pos_p(MATRIX_DENOMINATOR(b)));
  assert(value_pos_p(MATRIX_DENOMINATOR(c)));

  d1 = MATRIX_DENOMINATOR(b);
  d2 = MATRIX_DENOMINATOR(c);
  if (value_eq(d1,d2)){
    for (i=1; i<=m; i++)
	    for (j=1; j<=n; j++)
        MATRIX_ELEM(a,i,j) =
          value_minus(MATRIX_ELEM(b,i,j),MATRIX_ELEM(c,i,j));
    MATRIX_DENOMINATOR(a) = d1;
  }
  else {
    lcm = ppcm(d1,d2);
    d1 = value_div(lcm,d1);
    d2 = value_div(lcm,d2);
    for (i=1; i<=m; i++)
      for (j=1; j<=n; j++)
        MATRIX_ELEM(a,i,j) =
          value_minus(value_mult(MATRIX_ELEM(b,i,j),d1),
                      value_mult(MATRIX_ELEM(c,i,j),d2));
    MATRIX_DENOMINATOR(a) = lcm;
  }
}

/* a = b + c */
void matrix_add(Pmatrix a, Pmatrix b, Pmatrix c)
{
  /* precondition */
  int m = MATRIX_NB_LINES(a);
  int n = MATRIX_NB_COLUMNS(a);
  assert(n>0 && m>0);
  assert(value_pos_p(MATRIX_DENOMINATOR(b)));
  assert(value_pos_p(MATRIX_DENOMINATOR(c)));

  Value d1 = MATRIX_DENOMINATOR(b);
  Value d2 = MATRIX_DENOMINATOR(c);
  if (value_eq(d1,d2)){
    int i, j;
    for (i=1; i<=m; i++)
	    for (j=1; j<=n; j++)
        MATRIX_ELEM(a,i,j) =
          value_plus(MATRIX_ELEM(b,i,j),MATRIX_ELEM(c,i,j));
    MATRIX_DENOMINATOR(a) = d1;
  }
  else{
    Value lcm = ppcm(d1, d2);
    d1 = value_div(lcm,d1);
    d2 = value_div(lcm,d2);
    int i, j;
    for (i=1; i<=m; i++) {
	    for (j=1; j<=n; j++) {
        Value t1 = value_mult(MATRIX_ELEM(b,i,j),d1);
        Value t2 = value_mult(MATRIX_ELEM(c,i,j),d2);
        MATRIX_ELEM(a,i,j) = value_plus(t1,t2);
      }
    }
    MATRIX_DENOMINATOR(a) = lcm;
  }
}

/* void matrix_subtraction_column(Pmatrix MAT,int c1,int c2,int x):
 * Soustrait x fois la colonne c2 de la colonne c1
 * Precondition: n > 0; m > 0; 0 < c1, c2 < m;
 * Effet: c1[0..n-1] = c1[0..n-1] - x*c2[0..n-1].
 *
 *  Les parametres de la fonction :
 *
 * int  MAT[]     :  matrice
 * int  c1        :  numero du colonne
 * int  c2        :  numero du colonne
 * int  x         :
 */
void matrix_subtraction_column(Pmatrix MAT, int c1, int c2, Value x)
{
  int m = MATRIX_NB_LINES(MAT);
  int i;
  for (i=1; i<=m; i++)
    value_substract(MATRIX_ELEM(MAT,i,c1),
                    value_mult(x, MATRIX_ELEM(MAT,i,c2)));
}

/* void matrix_subtraction_line(Pmatrix MAT,int r1,int r2,int x):
 * Soustrait x fois la ligne r2 de la ligne r1 
 * Precondition: n > 0; m > 0; 0 < r1, r2 < n;
 * Effet: r1[0..m-1] = r1[0..m-1] - x*r2[0..m-1]
 *
 *  Les parametres de la fonction :
 *
 * int  MAT[]     :  matrice
 * int  n         :  nombre de lignes de la matrice
 * int  m         :  nombre de colonnes de la matrice
 * int  r1        :  numero du ligne
 * int  r2        :  numero du ligne
 * int  x         :
 */
void matrix_subtraction_line(Pmatrix MAT, int r1, int r2, Value x)
{
  int n = MATRIX_NB_COLUMNS(MAT);
  int i;
  for (i=1; i<=n; i++)
    value_substract(MATRIX_ELEM(MAT,r1,i),
                    value_mult(x,MATRIX_ELEM(MAT,r2,i)));
}

/* void matrix_uminus(A, mA)
 *
 * computes mA = - A
 *
 * input: A, larger allocated mA
 * output: none
 * modifies: mA
 */
void matrix_uminus(Pmatrix A, Pmatrix mA)
{
  assert(MATRIX_NB_LINES(mA)>=MATRIX_NB_LINES(A) &&
         MATRIX_NB_COLUMNS(mA)>=MATRIX_NB_COLUMNS(A));

  int i,j;
  for (i=1; i<=MATRIX_NB_LINES(A); i++)
    for (j=1; j<=MATRIX_NB_COLUMNS(A); j++)
	    MATRIX_ELEM(mA, i, j) = value_uminus(MATRIX_ELEM(A, i, j));
}

/* that is all
 */
