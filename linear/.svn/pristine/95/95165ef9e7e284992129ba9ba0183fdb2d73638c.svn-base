#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "linear_assert.h"

//#include "linear.h"
#include "boolean.h"
#include "arithmetique.h"
#include "vecteur.h"
#include "contrainte.h"
#include "sc.h"
//#include "linear.h"


int main(int argc, const char **argv)
{
  if (argc != 2) {
    fprintf(stderr, "Usage: %s sc1\n", argv[0]);
    exit(1);
  }

  const char *n1 = argv[1];

  // open input files
  FILE *f1;
  if ((f1 = fopen(n1,"r")) == NULL) {
    fprintf(stderr, "cannot open file: %s\n", n1);
    exit(4);
  }

 
  Psysteme s1 = sc_new();
  if (sc_fscan(f1, &s1)) {
    fprintf(stderr,"file syntax is ok: %s\n", n1);
    sc_fprint(stdout, s1, *variable_default_name);
    assert(sc_weak_consistent_p(s1));
  }
  else {
    fprintf(stderr, "syntax error in file: %s\n", n1);
    exit(1);
  }

  Value min=0;
  Value max=0;
  Psysteme sc= sc_new();
  Psysteme scd= sc_new();
  Pvecteur pv;
  bool bl;
  Variable v;
  
  sc = sc_copy(s1);
  for (pv =sc->base;!VECTEUR_NUL_P(pv); pv=pv->succ){
    v=pv->var;
    scd=sc_copy(sc);
    min=max=VALUE_ZERO;
    // sc_minmax_of_variable detruit le systeme
	
    if (!(bl = sc_minmax_of_variable(scd,v,&min,&max))) {

      printf("Pb computing loop bounds for v= %s\n",variable_default_name(v));
      sc_fprint(stdout,scd , *variable_default_name);
    }
    else {
      printf("Loop bounds for %s= [%d,%d]\n",variable_default_name(v), (int)min,(int)max);
    }
    sc_rm(scd);
  }

  return 0;
}

