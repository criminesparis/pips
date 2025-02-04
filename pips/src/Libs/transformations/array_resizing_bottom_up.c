/*

  $Id: array_resizing_bottom_up.c 23373 2017-05-11 08:38:19Z ancourt $

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

// do not compile unless required
#include "phases.h"
#ifdef BUILDER_ARRAY_RESIZING_BOTTOM_UP

#ifdef HAVE_CONFIG_H
#include "pips_config.h"
#endif
/******************************************************************
 *
 *		     BOTTOM UP ARRAY RESIZING
 *
 *
 *******************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "genC.h"
#include "linear.h"

#include "ri.h"
#include "effects.h"

#include "ri-util.h"
#include "prettyprint.h"
#include "effects-util.h"

#include "pipsdbm.h"
#include "misc.h"
#include "properties.h"

#include "semantics.h"
#include "effects-generic.h"
#include "effects-simple.h"
#include "effects-convex.h"

#include "text-util.h" /* for words_to_string and get_prettyprint_language_tag */
/* get_prettyprint_language_tag can be replace by macro code_language in ri.h but less flexible */


static int number_of_right_array_declarations = 0;
static string current_mod ="";
static int opt = 0; /* 0 <= opt <= 7*/
static char *file_name = NULL;
static FILE * instrument_file; /*To store new array declarations*/

#define PREFIX "$ARRAY_DECLARATION"

static bool
parameter_p(entity e)
{

  return storage_rom_p(entity_storage(e)) && 
      !(value_undefined_p(entity_initial(e))) &&
      value_symbolic_p(entity_initial(e)) &&
      type_functional_p(entity_type(e));
}

/*La valeur retournée est true si la variable v est un parameter
  ou une variable common. Sinon, elle rend la valeur FALSE.*/

static bool
variable_is_param_common_p(entity e)
{
  if ( (parameter_p(e)) || (variable_in_common_p(e)) )  return (true);
  else 
    return (false);
}

/*Rendre true si la variable v n'est pas un parameter, ni une variable common
  et v, v_phi ne sont pas identiques.
  En vice-versa, retourner la valeur FALSE.*/

static bool
variable_to_project_p(Variable v_phi, Variable v)
{
  if (v!=v_phi) {
    entity e = (entity) v;
    if (variable_is_param_common_p(e) || storage_formal_p(entity_storage(e))) return false;
    return true;
  }
  return false;
}

static bool extract_constraint_on_var(Pvecteur p_var, Variable var, int val,  Pvecteur *ptmp)
{
  bool divisible=true; 
  Pvecteur p_tmp = VECTEUR_NUL,pv;
  for (pv = p_var; !VECTEUR_NUL_P(pv) && divisible; pv=pv->succ) {
    Variable v1=vecteur_var(pv); 
    if (v1 ==TCST) 
      divisible &= value_zero_p(value_mod(vect_coeff(TCST,p_var), val));
    else if (v1!= var)
      divisible &=(basic_int_p(variable_basic(type_variable(entity_type((entity) v1 )))) 
          &&  value_zero_p(value_mod(pv->val, val)));
  }
  if (divisible) {
    p_tmp = vect_dup(p_var);
    vect_erase_var(&p_tmp,var);
    for (pv = p_tmp; !VECTEUR_NUL_P(pv); pv=pv->succ) {
      Variable v1=vecteur_var(pv);
      vect_chg_coeff(&pv,v1, value_uminus(value_div(pv->val, val)));
    }
    *ptmp = p_tmp;
    return(true);
  }
  else {
    *ptmp = VECTEUR_NUL;
    return (false);
  }
}

/* Traiter les égalités d'un système de contraintes ps.
  . Si la variable var apparaît dans ces égalités, *pe va contenir le vecteur
    définissant var. Ex. :
     Equation de la forme: k*var + q1*C1 + ... + p1*N1 + ... == 0
 *pe contient le vecteur : (-q1/k)*C1 + ... + (-p1/k)*N1
  . Sinon, pe est nulle. */

static bool
extract_constraint_from_equalitites(Psysteme ps, Variable var, Pvecteur *pe)
{
  Pcontrainte pc;
  Value v_phi = VALUE_ZERO;
  Pvecteur p_var = VECTEUR_NUL, ptmp= VECTEUR_NUL; 
  bool result=false;   
  if (!SC_UNDEFINED_P(ps) && !CONTRAINTE_UNDEFINED_P(ps->egalites) 
      && CONTRAINTE_NULLE_P(ps->egalites))  {
    *pe = VECTEUR_NUL;
    return(false);
  }
  for (pc = ps->egalites; pc != NULL; pc = pc->succ) {    
    /* équation de la forme: k*var + q1*C1 + ... + p1*N1 + ... == 0 */
    p_var = contrainte_vecteur(pc);
    v_phi = vect_coeff(var,p_var);
    if (v_phi) {
      result =  extract_constraint_on_var(p_var,var,v_phi,&ptmp);
      *pe=ptmp;
      return(result);}
  }
  *pe = VECTEUR_NUL;
  return(false);
}

/*Simplifier le Pvecteur pv et extraire les parametres qui apparaissent dans pv.
  Le Pvecteur résultat ne contient que les entiers et les variables commons.*/
static Pvecteur
vect_partial_eval(Pvecteur pv)
{
  Pvecteur v = VECTEUR_NUL, v_tmp = VECTEUR_NUL, v_p_tmp = VECTEUR_NUL;
  Value v_tcst = VALUE_ZERO;
  while (!VECTEUR_NUL_P(pv)) {
    Variable var = pv->var;
    if (var == TCST)
      v_tcst = value_plus(v_tcst, val_of(pv));
    else if (parameter_p((entity) var)) {
      Value val = int_to_value(expression_to_int(symbolic_expression(value_symbolic(entity_initial((entity) var)))));
      pips_debug(8, "The variable %s is a parameter and its value is %lld\n",
          entity_local_name((entity) var), val);
      v_tcst = value_plus(v_tcst, value_direct_multiply(val, val_of(pv)));
    }
    else {
      v_tmp = vect_new(pv->var, pv->val);
      if (v == VECTEUR_NUL) {
        v_p_tmp = v_tmp;
        v = v_tmp;
      }
      else {
        v_p_tmp->succ = v_tmp;
        v_p_tmp = v_tmp;
      }
    }
    pv = pv->succ;
  }

  if (v_tcst != VALUE_ZERO) {
    v_tmp = vect_new(TCST, v_tcst);
    if (v == VECTEUR_NUL) {
      v_p_tmp = v_tmp;
      v = v_tmp;
    }
    else v_p_tmp->succ = v_tmp;
  }
  return (v);
}

/* Faire la comparaison entre deux Pvecteurs basés sur le système des préconditions ps_prec.
  Cette fonction fait une combinaison sur 8 cas de la faisabilité d'un système des contraintes
  pour déterminer le Pvecteur supérieur et le Pvecteur inférieur.
  Ces 8 cas proviennent des 3 systèmes de contraintes :
    i)   sc_egal = { ps_prec , pv1 - pv2 = 0 }
   ii)   sc_inf  = { ps_prec , pv1 - pv2 < 0 }  =  { ps_prec , pv1 - pv2 + 1 <= 0 }
  iii)   sc_sup  = { ps_prec , pv2 - pv1 < 0 }  =  { ps_prec , pv2 - pv1 + 1 <= 0 }

  et le tableau de résultats est :

  sc_egal    || .T. |     .T.    |     .T.    |    .T.    | .F. |    .F.    |    .F.    | .F.
  --------------------------------------------------------------------------------------------
  sc_inf     || .T. |     .T.    |     .F.    |    .F.    | .T. |    .T.    |    .F.    | .F.
  --------------------------------------------------------------------------------------------
  sc_sup     || .T. |     .F.    |     .T.    |    .F.    | .T. |    .F.    |    .T.    | .F.
  ============================================================================================
  Conclusion ||  *  | pv1 <= pv2 | pv1 >= pv2 | pv1 = pv2 |  *  | pv1 < pv2 | pv1 > pv2 |  *

  ( " * "  correspondant au cas non-determiné )

  Dans le cas non-determiné, le Pvecteur retourné est VECTEUR_UNDEFINED et
  on doit donc traiter le cas de VECTEUR_UNDEFINED avec les autres :

    a-/  VECTEUR_UNDEFINED  et  VECTEUR_UNDEFINED
    b-/  VECTEUR_UNDEFINED  et  VECTEUR_ONE (1)
    c-/  VECTEUR_UNDEFINED  et  un vecteur quelconque sauf VECTEUR_ONE */
static Pvecteur
sc_minmax_of_pvector(Psysteme ps_prec, Pvecteur pv1, Pvecteur pv2, bool is_min)
{
  /* Automatic variables read in a CATCH block need to be declared volatile as
   * specified by the documentation*/
  Psysteme volatile ps_egal = SC_UNDEFINED;
  Psysteme volatile ps_inf = SC_UNDEFINED;
  Psysteme volatile ps_sup = SC_UNDEFINED;

  Psysteme  pt=  SC_UNDEFINED;
  Pcontrainte pc_egal = CONTRAINTE_UNDEFINED, 
      pc_inf = CONTRAINTE_UNDEFINED,
      pc_sup = CONTRAINTE_UNDEFINED;
  Pvecteur p1, p2, p_egal, p_inf, p_sup,pvt,pv_1;
  bool  egal = false, inf = false, sup = false;
  Pvecteur p_one = vect_new(TCST, VALUE_ONE);

  if (VECTEUR_UNDEFINED_P(pv1) && VECTEUR_UNDEFINED_P(pv2)) {
    vect_rm(p_one);
    return VECTEUR_UNDEFINED;
  }
  else if (VECTEUR_UNDEFINED_P(pv1) && !VECTEUR_UNDEFINED_P(pv2)) {
    if (!vect_equal(pv2, p_one)) {
      vect_rm(p_one);
      return (pv2);
    }
    else {
      if (is_min)  
        return(p_one);
      else 
        return VECTEUR_UNDEFINED;
    }
  }
  else if ( VECTEUR_UNDEFINED_P(pv2) && !VECTEUR_UNDEFINED_P(pv1) ) { 
    if (!vect_equal(pv1, p_one)) {
      vect_rm(p_one);
      return (pv1);
    }
    else {
      if (is_min)  
        return(p_one);
      else 
        return VECTEUR_UNDEFINED;
    }
  }
  p1 = vect_partial_eval(pv1);
  p2 = vect_partial_eval(pv2);
  p_egal = vect_substract(p1, p2);
  if (VECTEUR_NUL_P(p_egal)) return(p1);

  /* Creation des trois systemes */
  pvt=vect_dup(p_egal);
  pc_egal = contrainte_make(pvt);
  pt=sc_dup(ps_prec);
  ps_egal = sc_equation_add(pt, pc_egal);
  base_rm(ps_egal->base);
  ps_egal->base = BASE_NULLE;
  sc_creer_base(ps_egal);
  ps_egal = sc_elim_redund(ps_egal);

  pv_1= vect_new(TCST, VALUE_ONE);
  p_inf = vect_add(p_egal,pv_1);
  vect_rm(pv_1);
  pc_inf = contrainte_make(p_inf); 
  pt=sc_dup(ps_prec);
  ps_inf = sc_inequality_add(pt, pc_inf);
  base_rm(ps_inf->base);
  ps_inf->base = BASE_NULLE;
  sc_creer_base(ps_inf);
  ps_inf = sc_elim_redund(ps_inf);

  pv_1= vect_new(TCST, VALUE_ONE);
  p_sup = vect_substract(pv_1,p_egal);
  vect_rm(pv_1);
  pc_sup = contrainte_make(p_sup); 
  pt=sc_dup(ps_prec);
  ps_sup = sc_inequality_add(pt, pc_sup);
  base_rm(ps_sup->base);
  ps_sup->base = BASE_NULLE;
  sc_creer_base(ps_sup);
  ps_sup = sc_elim_redund(ps_sup);

  CATCH (overflow_error) {
    pips_debug(8, "Overflow detected !\n");  
    sc_free(ps_egal);
    sc_free(ps_inf);
    sc_free(ps_sup);
    return VECTEUR_UNDEFINED;     
  }
  TRY {
    egal = !SC_UNDEFINED_P(ps_egal) && 
        sc_rational_feasibility_ofl_ctrl(ps_egal, OFL_CTRL, true);
    inf =  !SC_UNDEFINED_P(ps_inf) && 
        sc_rational_feasibility_ofl_ctrl(ps_inf, OFL_CTRL, true);
    sup =  !SC_UNDEFINED_P(ps_sup) && 
        sc_rational_feasibility_ofl_ctrl(ps_sup, OFL_CTRL, true);
    sc_free(ps_egal);
    sc_free(ps_inf);
    sc_free(ps_sup);
    UNCATCH (overflow_error);
    if (is_min) { /* Recherche du  minimum  */
      if ( (egal && inf && !sup) || (egal && !inf && !sup) || (!egal && inf && !sup) ) {
        pips_debug(8, "p1 is minimum\n");
        return (p1);
      }
      if ( (egal && !inf && sup) || (egal && !inf && !sup) || (!egal && !inf && sup) ) {
        pips_debug(8, "p2 is minimum\n");
        return (p2);
      }
      else {
        pips_debug(8, "Non-determined\n");
        return VECTEUR_UNDEFINED;
      }
    }
    else { /* Recherche du  maximum  */
      if ( (egal && inf && !sup) || (egal && !inf && !sup) || (!egal && inf && !sup) ) {
        pips_debug(8, "p2 is maximum\n");
        return (p2);
      }
      if ( (egal && !inf && sup) || (egal && !inf && !sup) || (!egal && !inf && sup) ) {
        pips_debug(8, "p1 is maximum\n");
        return (p1);
      }
      else {
        pips_debug(8, "Non-determined\n");
        return VECTEUR_UNDEFINED;
      }
    }    
  }
}

/*Traiter les inégalités d'un système de contraintes.
  Si la variable var apparaît dans les inégalités, cette fonction va retourner la borne inférieure et la borne supérieure
  de la variable var sous la forme de Pvecteur pmin et pmax. Sinon, la valeur retournée est false et les Pvecteurs sont nuls.
  Dans cette fonction, il y a des appels à la fonction sc_min_max_of_pvector() pour comparer deux vecteurs. */
static bool
extract_constraint_from_inequalities(Psysteme ps, Variable var, Psysteme ps_prec, Pvecteur *pe, Pvecteur *pmin, Pvecteur *pmax)
{
  Pcontrainte pc;
  Value v_phi = VALUE_ZERO;
  Pvecteur p_var = VECTEUR_NUL, ptmp = VECTEUR_NUL, p_max = VECTEUR_NUL, p_min = VECTEUR_NUL ; 
  p_max = vect_dup(*pe);
  if (VECTEUR_NUL_P(*pe))
    p_min = vect_new(TCST, VALUE_ONE);
  else  p_min = vect_dup(*pe);

  if (!SC_UNDEFINED_P(ps) && !CONTRAINTE_UNDEFINED_P(ps->inegalites) 
      && CONTRAINTE_NULLE_P(ps->inegalites))  {
    *pmax = p_max;
    *pmin = p_min;
    return(false);
  }  
  for (pc = ps->inegalites; pc != NULL; pc = pc->succ) {
    p_var = contrainte_vecteur(pc);
    v_phi = vect_coeff(var,p_var);
    if (v_phi) {
      (void)extract_constraint_on_var(p_var,var,v_phi,&ptmp);

      if (value_pos_p(v_phi)) 
        p_max = sc_minmax_of_pvector(ps_prec, p_max, ptmp, false);
      else if (value_neg_p(v_phi)) {
        p_min = sc_minmax_of_pvector(ps_prec, p_min, ptmp, true);
      }
    }
  }
  *pmax = p_max;
  *pmin = p_min;
  return (true);
}

/*Cette fonction a été écrite pour déterminer les valeurs minimum et maximum d'une variable dans
  un système de contraintes, elle est donc la fonction principale du programme.
  . La valeur retournée est false si le système de contraintes est infaisable ou les valeurs min, max sont
    indéterminables. Et vice-versa, la valeur retournée est TRUE.
  . Les pointeurs pmin et pmax contiennent les valeurs des bornes supérieure et inférieure
    de la variable var dans le système de contraintes ps. Ces valeurs sont des Pvecteurs.
  Cette fonction contient les appels aux fonctions sc_egalites_of_variable() et sc_inegalites_of_variable()
  pour traiter les égalités et les inégalités du système ps.  */
static bool
sc_min_max_of_variable(Psysteme ps, Variable var, Psysteme ps_prec, Pvecteur *min, Pvecteur *max)
{
  Pbase b;
  Pvecteur pe = VECTEUR_NUL;
  Psysteme ps_e, ps_i;
  bool ok2;
  assert(var!=TCST);  
  *min = vect_new(TCST, VALUE_MIN);
  *max = vect_new(TCST, VALUE_MAX);

  /* faire la projection sur toutes les variables sauf var, parametres formels et commons */
  for (b = ps->base; !VECTEUR_NUL_P(b); b = b->succ) {
    Variable v = var_of(b);
    if (variable_to_project_p(var, v)) {
      if (SC_EMPTY_P(ps = sc_projection_pure(ps, v))) 
        return false;
    }
  }
  if (SC_EMPTY_P(ps = sc_normalize(ps)))
    return false;

  if (SC_UNDEFINED_P(ps) || ( sc_nbre_inegalites(ps)==0  && sc_nbre_egalites(ps)==0))
    return(false);

  ps_e = sc_dup(ps);
  ps_i = sc_dup(ps);

  (void)extract_constraint_from_equalitites(ps_e, var, &pe);  
  ok2 = extract_constraint_from_inequalities(ps_i, var, ps_prec, &pe, min, max);
  ifdebug(8) {
    if (ok2)
      pips_debug(8, "The upper bound has been found\n");
    else
      pips_debug(8, "The upper bound has not been found\n");
  }

  vect_rm(pe);
  sc_rm(ps_e);
  sc_rm(ps_i);

  return (ok2);
}

static void new_array_declaration_from_region(region reg, entity e, Psysteme pre)
{
  variable v = type_variable(entity_type(e));   
  list l_dims = variable_dimensions(v);
  int length = gen_length(l_dims);
  // Fortran is last dim/ C is first dim that can be changed without consequence on data structure
  dimension dim = dimension_undefined;
  entity phi = entity_undefined;

  switch(get_prettyprint_language_tag()) {
  case is_language_fortran95:
  case is_language_fortran:
    dim = find_ith_dimension(l_dims,length);
    phi = make_phi_entity(length);
    break;
  case is_language_c:
    dim = find_ith_dimension(l_dims,1);
    phi = make_phi_entity(1);
    break;
  default:
    pips_internal_error("Language unknown !\n");
    break;
  }

  expression upper = expression_undefined;
  Pvecteur min,max;

  if (!region_undefined_p(reg))
  {
    /* there are cases when there is no region for one array */
    Psysteme ps = sc_dup(region_system(reg));
    if (sc_min_max_of_variable(ps, (Variable) phi, pre, &min, &max))
      upper = Pvecteur_to_expression(max);
    sc_rm(ps);
  }

  if (expression_undefined_p(upper)) {
    upper = make_unbounded_expression();
  }

  if (!unbounded_expression_p(upper))
  {
    number_of_right_array_declarations++;
    fprintf(instrument_file,"%s\t%s\t%s\t%s\t%d\t%s\t%s\n",PREFIX,file_name,
        current_mod,entity_local_name(e),length,
        expression_to_string(dimension_upper(dim)),
        expression_to_string(upper));
    dimension_upper(dim) = upper;
  }
}

/**
 * This function finds in the list of regions l_regions,
 * the read and write store regions of e.
 * If there are 2 regions, it returns the union region
 */
static region find_union_store_regions(list l_regions,entity e)
{
  region reg = region_undefined;
  while (!ENDP(l_regions))
  {
    region re = REGION(CAR(l_regions));
    if (store_effect_p(re)) {
      reference ref = effect_any_reference(re);
      entity array = reference_variable(ref);
      if (same_entity_lname_p(array,e))
      {
        if (region_undefined_p(reg))
          reg = region_dup(re);
        else
          reg =  regions_must_convex_hull(reg,re);
      }
    }
    l_regions = CDR(l_regions);
  }
  return reg;
}

/* This phase do array resizing for all kind of arrays: formal or local, 
   unnormalized or not, depending on chosen option.
   This pass can't work for C code. */
bool array_resizing_bottom_up(char* mod_name)
{
  /* instrument_file is used to store new array declarations and will be used by 
   * a script to insert these declarations in the source code in xxx.database/Src/file_name.f
   *
   * file_name gives the file containing the current module in xxx.database/Src/ */
  set_current_module_entity(module_name_to_entity(mod_name));
  entity module = get_current_module_entity();

  list l_decl = code_declarations(entity_code(module)), l_regions = NIL;

  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, mod_name, true) );
  statement stmt = get_current_module_statement();

  transformer mod_pre;
  Psysteme pre;
  string dir_name = db_get_current_workspace_directory();
  string instrument_file_name = strdup(concatenate(dir_name, "/BU_instrument.out", NULL));
  string user_file = db_get_memory_resource(DBR_USER_FILE,mod_name,true);
  string base_name = pips_basename(user_file, NULL);
  instrument_file = safe_fopen(instrument_file_name, "a");  
  file_name = strdup(concatenate(db_get_directory_name_for_module(WORKSPACE_SRC_SPACE), 
      "/",base_name,NULL));
  current_mod = mod_name;  
  set_precondition_map((statement_mapping)
      db_get_memory_resource(DBR_PRECONDITIONS,mod_name,true));
  set_rw_effects((statement_effects) 
      db_get_memory_resource(DBR_REGIONS, mod_name, true));
  regions_init(); 
  debug_on("ARRAY_RESIZING_BOTTOM_UP_DEBUG_LEVEL");
  debug(1," Begin bottom up array resizing for %s\n", mod_name);
  // In C this list is NIL or only contain formal parameter regions
  // due to the local declaration
  l_regions = load_rw_effects_list(stmt);
  mod_pre = load_statement_precondition(stmt);
  pre = predicate_system(transformer_relation(mod_pre));

  opt = get_int_property("ARRAY_RESIZING_BOTTOM_UP_OPTION");
  /* opt in {0,1,2,3} => Do not compute new declarations for instrumented array (I_PIPS_MODULE_ARRAY)
   * opt in {4,5,6,7} => Compute new declarations for instrumented array (I_PIPS_MODULE_ARRAY)
   * => (opt mod 8)<= 3 or not
   *
   * opt in {0,1,4,5} => Compute new declarations for assumed-size and one arrays only
   * opt in {2,3,6,7} => Compute new declarations for all kinds of arrays
   * => (opt mod 4) <= 1 or not || get_bool_property("ARRAY_RESIZING_ASSUMED_SIZE_ONLY")
   *
   * opt in {0,2,4,6} => Do not compute new declarations for local array arguments
   * opt in {1,3,5,7} => Compute new declarations for local array arguments also
   * => (opt mod 2) = 0 or not || get_bool_property("ARRAY_RESIZING_ARGUMENT")
   **/

  FOREACH(ENTITY, e, l_decl) {
    if (opt%8 <= 3)
    {
      /* Do not compute new declarations for instrumented array (I_PIPS_MODULE_ARRAY)*/
      if (opt%4 <= 1 /*|| get_bool_property("ARRAY_RESIZING_ASSUMED_SIZE_ONLY")*/)
      {
        /* Compute new declarations for assumed-size and one arrays only */
        if (opt%2 == 1 /*|| get_bool_property("ARRAY_RESIZING_ARGUMENT")*/)
        {
          /* Compute new declarations for local array arguments also*/
          if (unnormalized_array_p(e))
          {
            region reg = find_union_store_regions(l_regions,e);
            new_array_declaration_from_region(reg,e,pre);
          }
        }
        else
        {
          /* Do not compute new declarations for local array arguments */
          if (unnormalized_array_p(e) && !formal_parameter_p(e))
          {
            region reg = find_union_store_regions(l_regions,e);
            new_array_declaration_from_region(reg,e,pre);
          }
        }
      }
      else
      {
        /* Compute new declarations for all kinds of arrays
         * To be modified, the whole C code: assumed-size bound if not success, ...
         * How about multi-dimensional array ? replace all upper bounds ?
         * => different script, ...*/

        user_log("This option has not been implemented yet\n");

        if (opt%2 == 1 /*|| get_bool_property("ARRAY_RESIZING_ARGUMENT")*/) {
          /* Do not compute new declarations for local array arguments */
          region reg = find_union_store_regions(l_regions,e);
          new_array_declaration_from_region(reg,e,pre);
        }
        else {
          if (!formal_parameter_p(e)) {
            /* Compute new declarations for local array arguments also*/
            region reg = find_union_store_regions(l_regions,e);
            new_array_declaration_from_region(reg,e,pre);
          }
        }
      }
    }
    else
    {
      /* Compute new declarations for instrumented array (I_PIPS_MODULE_ARRAY)
       * Looking for arrays that contain I_PIPS in the last upper bound declaration
       * Attention: this case excludes some other cases */
      //if (pips_instrumented_array_p(e))
      // {
      //	region reg = find_union_regions(l_regions,e);
      //	new_array_declaration_from_region(reg,e,pre);
      // }
      user_log("This option has not been implemented yet\n");
    }
  }
  user_log("* Number of right array declarations replaced: %d *\n"
      ,number_of_right_array_declarations );

  debug(1,"End bottom up array resizing for %s\n", mod_name);
  debug_off();  
  regions_end();

  reset_current_module_statement();
  reset_current_module_entity();
  reset_precondition_map();
  reset_rw_effects();
  safe_fclose(instrument_file,instrument_file_name);
  free(dir_name), dir_name = NULL;
  free(instrument_file_name), instrument_file_name = NULL;
  free(file_name), file_name = NULL;
  current_mod = "";
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, mod_name, stmt);

  return true;
}


/********************************************************
 * linear function to find new min/max for C(/Fortran?) *
 ********************************************************/
// Can replace the similar functions at the beginning of the files?
// Need to test it...

// see extract_constraint_on_var
static bool extract_constraint_on_var_C(Pvecteur p_var, Variable var, int val,  Pvecteur *ptmp)
{
  bool divisible=true;
  Pvecteur p_tmp = VECTEUR_NUL,pv;
  for (pv = p_var; !VECTEUR_NUL_P(pv) && divisible; pv=pv->succ) {
    Variable v1=vecteur_var(pv);
    if (v1 ==TCST)
      divisible &= value_zero_p(value_mod(vect_coeff(TCST,p_var), val));
    else if (v1!= var)
      divisible &=(basic_int_p(variable_basic(type_variable(entity_type((entity) v1 ))))
          &&  value_zero_p(value_mod(pv->val, val)));
  }
  if (divisible) {
    p_tmp = vect_dup(p_var);
    vect_erase_var(&p_tmp,var);
    for (pv = p_tmp; !VECTEUR_NUL_P(pv); pv=pv->succ) {
      Variable v1=vecteur_var(pv);
      vect_chg_coeff(&pv,v1, value_uminus(value_div(pv->val, val)));
    }
    *ptmp = p_tmp;
    return(true);
  }
  else {
    *ptmp = VECTEUR_UNDEFINED;
    return (false);
  }
}

// see extract_constraint_from_equalitites
static bool
extract_constraint_from_equalitites_C(Psysteme ps, Variable var, Pvecteur *pe)
{
  Pcontrainte pc;
  Value v_phi = VALUE_ZERO;
  Pvecteur p_var = VECTEUR_NUL, ptmp= VECTEUR_NUL;
  bool result=false;
  if (!SC_UNDEFINED_P(ps) && !CONTRAINTE_UNDEFINED_P(ps->egalites)
      && CONTRAINTE_NULLE_P(ps->egalites))  {
    *pe = VECTEUR_UNDEFINED;
    return(false);
  }
  for (pc = ps->egalites; pc != NULL; pc = pc->succ) {
    /* équation de la forme: k*var + q1*C1 + ... + p1*N1 + ... == 0 */
    p_var = contrainte_vecteur(pc);
    v_phi = vect_coeff(var,p_var);
    if (v_phi) {
      result =  extract_constraint_on_var_C(p_var,var,v_phi,&ptmp);
      *pe=ptmp;
      return(result);}
  }
  *pe = VECTEUR_UNDEFINED;
  return(false);
}

// see sc_minmax_of_pvector
// There is no test case in validation that really test this function...
static Pvecteur
sc_minmax_of_pvector_C(Psysteme ps_prec, Pvecteur pv1, Pvecteur pv2, bool is_min)
{
  /* Automatic variables read in a CATCH block need to be declared volatile as
   * specified by the documentation*/
  Psysteme volatile ps_egal = SC_UNDEFINED;
  Psysteme volatile ps_inf = SC_UNDEFINED;
  Psysteme volatile ps_sup = SC_UNDEFINED;

  Psysteme  pt=  SC_UNDEFINED;
  Pcontrainte pc_egal = CONTRAINTE_UNDEFINED,
      pc_inf = CONTRAINTE_UNDEFINED,
      pc_sup = CONTRAINTE_UNDEFINED;
  Pvecteur p1, p2, p_egal, p_inf, p_sup,pvt,pv_1;
  bool  egal = false, inf = false, sup = false;
  // No more VECTEUR_UNDEFIED
  // VECTEUR_NUL mean value 0 and no more undefined with the modification
//  Pvecteur p_one = vect_new(TCST, VALUE_ONE);
//
//  if (VECTEUR_UNDEFINED_P(pv1) && VECTEUR_UNDEFINED_P(pv2)) {
//    vect_rm(p_one);
//    return VECTEUR_UNDEFINED;
//  }
//  else if (VECTEUR_UNDEFINED_P(pv1) && !VECTEUR_UNDEFINED_P(pv2)) {
//    if (!vect_equal(pv2, p_one)) {
//      vect_rm(p_one);
//      return (pv2);
//    }
//    else {
//      if (is_min)
//        return(p_one);
//      else
//        return VECTEUR_UNDEFINED;
//    }
//  }
//  else if ( VECTEUR_UNDEFINED_P(pv2) && !VECTEUR_UNDEFINED_P(pv1) ) {
//    if (!vect_equal(pv1, p_one)) {
//      vect_rm(p_one);
//      return (pv1);
//    }
//    else {
//      if (is_min)
//        return(p_one);
//      else
//        return VECTEUR_UNDEFINED;
//    }
//  }
  p1 = vect_partial_eval(pv1);
  p2 = vect_partial_eval(pv2);
  p_egal = vect_substract(p1, p2);
  if (VECTEUR_NUL_P(p_egal)) return(p1);

  /* Creation des trois systemes */
  pvt=vect_dup(p_egal);
  pc_egal = contrainte_make(pvt);
  pt=sc_dup(ps_prec);
  ps_egal = sc_equation_add(pt, pc_egal);
  base_rm(ps_egal->base);
  ps_egal->base = BASE_NULLE;
  sc_creer_base(ps_egal);
  ps_egal = sc_elim_redund(ps_egal);

  pv_1= vect_new(TCST, VALUE_ONE);
  p_inf = vect_add(p_egal,pv_1);
  vect_rm(pv_1);
  pc_inf = contrainte_make(p_inf);
  pt=sc_dup(ps_prec);
  ps_inf = sc_inequality_add(pt, pc_inf);
  base_rm(ps_inf->base);
  ps_inf->base = BASE_NULLE;
  sc_creer_base(ps_inf);
  ps_inf = sc_elim_redund(ps_inf);

  pv_1= vect_new(TCST, VALUE_ONE);
  p_sup = vect_substract(pv_1,p_egal);
  vect_rm(pv_1);
  pc_sup = contrainte_make(p_sup);
  pt=sc_dup(ps_prec);
  ps_sup = sc_inequality_add(pt, pc_sup);
  base_rm(ps_sup->base);
  ps_sup->base = BASE_NULLE;
  sc_creer_base(ps_sup);
  ps_sup = sc_elim_redund(ps_sup);

  CATCH (overflow_error) {
    pips_debug(2, "Overflow detected !\n");
    sc_free(ps_egal);
    sc_free(ps_inf);
    sc_free(ps_sup);
    if (is_min)
      return vect_new(TCST, VALUE_MIN);
    else
      return vect_new(TCST, VALUE_MAX);
  }
  TRY {
    egal = !SC_UNDEFINED_P(ps_egal) &&
        sc_rational_feasibility_ofl_ctrl(ps_egal, OFL_CTRL, true);
    inf =  !SC_UNDEFINED_P(ps_inf) &&
        sc_rational_feasibility_ofl_ctrl(ps_inf, OFL_CTRL, true);
    sup =  !SC_UNDEFINED_P(ps_sup) &&
        sc_rational_feasibility_ofl_ctrl(ps_sup, OFL_CTRL, true);
    sc_free(ps_egal);
    sc_free(ps_inf);
    sc_free(ps_sup);
    UNCATCH (overflow_error);
    if (is_min) { /* Recherche du  minimum  */
      if ( (egal && inf && !sup) || (egal && !inf && !sup) || (!egal && inf && !sup) ) {
        pips_debug(9, "p1 is minimum\n");
        vect_rm(p2);
        return (p1);
      }
      if ( (egal && !inf && sup) || (egal && !inf && !sup) || (!egal && !inf && sup) ) {
        pips_debug(9, "p2 is minimum\n");
        vect_rm(p1);
        return (p2);
      }
      else {
        pips_debug(9, "Non-determined\n");
        vect_rm(p1);
        vect_rm(p2);
        return vect_new(TCST, VALUE_MIN);
      }
    }
    else { /* Recherche du  maximum  */
      if ( (egal && inf && !sup) || (egal && !inf && !sup) || (!egal && inf && !sup) ) {
        pips_debug(9, "p2 is maximum\n");
        vect_rm(p1);
        return (p2);
      }
      if ( (egal && !inf && sup) || (egal && !inf && !sup) || (!egal && !inf && sup) ) {
        pips_debug(9, "p1 is maximum\n");
        vect_rm(p2);
        return (p1);
      }
      else {
        pips_debug(9, "Non-determined\n");
        vect_rm(p1);
        vect_rm(p2);
        return vect_new(TCST, VALUE_MAX);
      }
    }
  }
  pips_internal_error("Never reach this point - dead code\n");
}

// see extract_constraint_from_inequalities
static bool
extract_constraint_from_inequalities_C(Psysteme ps, Variable var, Psysteme ps_prec, bool egalite_p, Pvecteur *pe, Pvecteur *pmin, Pvecteur *pmax)
{
  Pcontrainte pc;
  Value v_phi = VALUE_ZERO;
  Pvecteur p_var = VECTEUR_NUL, ptmp = VECTEUR_NUL, p_max = VECTEUR_NUL, p_min = VECTEUR_NUL ;
  Pvecteur pv_min = vect_new(TCST, VALUE_MIN);
  Pvecteur pv_max = vect_new(TCST, VALUE_MAX);
  bool extract_ok;
  if (egalite_p) {
    p_min = vect_dup(*pe);
    p_max = vect_dup(*pe);
  }
  else {
    p_min = vect_new(TCST, VALUE_MAX);
    p_max = vect_new(TCST, VALUE_MIN);
  }
  ifdebug(9) {
    pips_debug(9, "begin p_min\n");
    vect_print(p_min, (get_variable_name_t) entity_local_name);
    pips_debug(9, "begin p_max\n");
    vect_print(p_max, (get_variable_name_t) entity_local_name);
  }

  if (!SC_UNDEFINED_P(ps) && !CONTRAINTE_UNDEFINED_P(ps->inegalites)
      && CONTRAINTE_NULLE_P(ps->inegalites))  {
    *pmax = p_max;
    *pmin = p_min;
    return(false);
  }

  for (pc = ps->inegalites; pc != NULL; pc = pc->succ) {
    ifdebug(9) {
      pips_debug(9, "work on inequality\n");
      inegalite_fprint(stderr, pc, (get_variable_name_t) entity_local_name);
    }
    p_var = contrainte_vecteur(pc);
    v_phi = vect_coeff(var,p_var);
    if (v_phi) {
      extract_ok = extract_constraint_on_var_C(p_var,var,v_phi,&ptmp);

      if (extract_ok) {
        if (value_pos_p(v_phi)) {
          if (!vect_equal(p_max, pv_min) && !vect_equal(p_max, pv_max))
            p_max = sc_minmax_of_pvector_C(ps_prec, p_max, ptmp, false);
          else if (vect_equal(p_max, pv_min)) {
            vect_rm(p_max);
            p_max = ptmp;
          }
        }
        else if (value_neg_p(v_phi)) {
          if (!vect_equal(p_min, pv_min) && !vect_equal(p_min, pv_max))
            p_min = sc_minmax_of_pvector_C(ps_prec, p_min, ptmp, true);
          else if (vect_equal(p_min, pv_max)) {
            vect_rm(p_min);
            p_min = ptmp;
          }
        }
      }
      else {
        if (value_pos_p(v_phi)) {
          vect_rm(p_max);
          p_max = vect_new(TCST, VALUE_MAX);
        }
        else if (value_neg_p(v_phi)) {
          vect_rm(p_min);
          p_min = vect_new(TCST, VALUE_MIN);
        }
      }

      ifdebug(9) {
        pips_debug(9, "p_min\n");
        vect_print(p_min, (get_variable_name_t) entity_local_name);
        pips_debug(9, "p_max\n");
        vect_print(p_max, (get_variable_name_t) entity_local_name);
      }

      if (vect_equal(p_min, pv_min) && vect_equal(p_max, pv_max)) {
        vect_rm(pv_min);
        vect_rm(pv_max);
        return false;
      }
    }
  }
  ifdebug(9) {
    pips_debug(9, "end p_min\n");
    vect_print(p_min, (get_variable_name_t) entity_local_name);
    pips_debug(9, "end p_max\n");
    vect_print(p_max, (get_variable_name_t) entity_local_name);
  }
  *pmax = p_max;
  *pmin = p_min;
  vect_rm(pv_min);
  vect_rm(pv_max);
  return (true);
}

// see sc_min_max_of_variable
// with some modification the allow VECTEUR_NUL, that will really represent value 0 and not VECTEUR_UNDEFINED
// no more VECTEUR_UNDEFINED, use the return function to know if it's undefined
// min/max can return VALUE_MIN, VALUE_MAX, if failed find new bounds
// can replace sc_min_max_of_variable??? Need to test it...
static bool
sc_min_max_of_variable_C(Psysteme ps, Variable var, Psysteme ps_prec, Pvecteur *min, Pvecteur *max)
{
  // Can this case really occur ?
  //if (ENDP(ps) || list_undefined_p(ps))
  //  return false;

  Pbase b;
  Pvecteur pe = VECTEUR_NUL;
  Psysteme ps_e, ps_i;
  bool ok_eg, ok2;
  assert(var!=TCST);
  //*min = vect_new(TCST, VALUE_MIN);
  //*max = vect_new(TCST, VALUE_MAX);

  ifdebug(9) {
    pips_debug(9, "input system\n");
    sc_print(ps, (get_variable_name_t) entity_local_name);
  }

  // Can this case really occur ?
  //if (ENDP(ps) || list_undefined_p(ps))
  //  return false;

  /* faire la projection sur toutes les variables sauf var, parametres formels et commons */
  for (b = ps->base; !VECTEUR_NUL_P(b); b = b->succ) {
    Variable v = var_of(b);
    if (variable_to_project_p(var, v)) {
      if (SC_EMPTY_P(ps = sc_projection_pure(ps, v)))
        return false;
    }
  }
  if (SC_EMPTY_P(ps = sc_normalize(ps)))
    return false;

  if (SC_UNDEFINED_P(ps) || ( sc_nbre_inegalites(ps)==0  && sc_nbre_egalites(ps)==0))
    return(false);

  ps_e = sc_dup(ps);
  ps_i = sc_dup(ps);

  ifdebug(9) {
    pips_debug(9, "work on system\n");
    sc_print(ps, (get_variable_name_t) entity_local_name);
  }

  ok_eg = extract_constraint_from_equalitites_C(ps_e, var, &pe);
  ok2 = extract_constraint_from_inequalities_C(ps_i, var, ps_prec, ok_eg, &pe, min, max);
  ifdebug(8) {
    if (ok2)
      pips_debug(8, "New bounds have been found\n");
    else
      pips_debug(8, "New bound have not been found\n");
  }

  vect_rm(pe);
  sc_rm(ps_e);
  sc_rm(ps_i);

  return (ok2);
}

/********************************************************
 *       END linear function to find new min/max        *
 ********************************************************/

struct context_resizing
{
  entity array;     // array to resize
  list l_shift;     // list of expression to shift
  // l_shift has the size of variable_dimensions(type_variable(entity_type(e))) list
  // if no shift needed for a dimension put expression_undefined
  // use copy_expression on the expression of the l_shift
  bool need_shift_p; // by default false
};

static struct context_resizing * make_context_resizing (entity e)
{
  struct context_resizing * result = NULL;
  result = (struct context_resizing *) alloc(sizeof(struct context_resizing));
  if (result == NULL) {
    pips_internal_error("array_resizing, alloc failed.\n");
  }
  result->array = e;
  result->l_shift = NIL;
  result->need_shift_p = false;
  return result;
}

static void free_context_resizing(struct context_resizing * str)
{
  free(str);
}

static list init_list_of_array_to_compute(list l_decl)
{
  list result = NIL;
  struct context_resizing * to_add = NULL;
  bool compute_assumed_only = get_bool_property("ARRAY_RESIZING_ASSUMED_SIZE_ONLY");
  bool compute_argument = get_bool_property("ARRAY_RESIZING_ARGUMENT");
  pips_debug(5, "begin\n");

  FOREACH(ENTITY, e, l_decl) {
    if (array_type_p(entity_type(e))) {
      if (compute_argument) {
        /* Compute new declarations for array arguments */
        pips_user_warning("It can impact the caller function with the modification of the structure\n");
        //user_log("Not implemented yet.\n");
        if (compute_assumed_only) {
          /* Compute new declarations for assumed-size and one arrays only */
          // if (unnormalized_array_p(e)) {
          if (assumed_size_array_p(e)) {
            pips_debug(2, "0-add entity %s to analyze list\n", entity_name(e));
            to_add = make_context_resizing(e);
            result = gen_cons((const struct context_resizing *) to_add, result);
          }
        }
        else {
          /* Compute new declarations for all kinds of arrays */
          pips_debug(2, "1-add entity %s to analyze list\n", entity_name(e));
          to_add = make_context_resizing(e);
          result = gen_cons((const struct context_resizing *) to_add, result);
        }
      }
      else {
        /* Do not compute new declarations for array arguments */
        if (!formal_parameter_p(e)) {
          if (compute_assumed_only) {
            /* Compute new declarations for assumed-size and one arrays only */
            // if (unnormalized_array_p(e)) {
            if (assumed_size_array_p(e)) {
              pips_debug(2, "2-add entity %s to analyze list\n", entity_name(e));
              to_add = make_context_resizing(e);
              result = gen_cons((const struct context_resizing *) to_add, result);
            }
          }
          else {
            /* Compute new declarations for all kinds of arrays */
            pips_debug(2, "3-add entity %s to analyze list\n", entity_name(e));
            to_add = make_context_resizing(e);
            result = gen_cons((const struct context_resizing *) to_add, result);
          }
        }
      }
      to_add = NULL;
    }
  }

  pips_debug(5, "end\n");
  return result;
}

static void free_list_of_array_to_compute(list * l_ctx) {
  list l_temp = *l_ctx;
  for(struct context_resizing * elem; !ENDP(l_temp) && (elem= ((struct context_resizing *) (CAR(l_temp).p))); POP(l_temp)) {
    free_context_resizing(elem);
  }
}

static bool modify_array_declaration(statement st, list *ctx) {
  if (declaration_statement_p(st)) {
    ifdebug(5) {
      pips_debug(5, "begin\n");
      print_statement(st);
    }
    list l_decl = statement_declarations(st);
    transformer mod_pre = load_statement_precondition(st);
    Psysteme pre = predicate_system(transformer_relation(mod_pre));
    Pvecteur pv_min = vect_new(TCST, VALUE_MIN);
    Pvecteur pv_max = vect_new(TCST, VALUE_MAX);

    bool c_array_notation = false;
    language lang = get_prettyprint_language();

    // foreach declaration,
    //   if it is an array compute the new lower/upper bound
    //     and remove the entity from the hash table if no shift access need to be done.
    FOREACH(ENTITY, e, l_decl) {
      // The first following if is for optimization, to not have to search into the context list
      if (array_type_p(entity_type(e))) {
        ifdebug(2) {
          pips_debug(2, "work on entity :\n");
          print_entity_variable(e);
        }

        // search entity array e in the context
        // if not present, it's not a array to analyze
        list l_temp = *ctx;
        for(struct context_resizing *compute_array; !ENDP(l_temp) && (compute_array= ((struct context_resizing *) (CAR(l_temp).p))); POP(l_temp)) {
          if (same_entity_p(e, compute_array->array)) {
            // we find the right element into the list

            // Verify that array e is present in useful_variables_regions resources
            if (bound_useful_variables_effects_p(e)) {
              effects rwrg = load_useful_variables_effects(e);
              // filter to only have store effects/regions
              // This filter can also be made in find_union_regions(), with function store_effect_p()
//              rwrg = effects_store_effects(rwrg);
              ifdebug(2) {
                pips_debug(2, "with rwrg :\n");
                print_effects(effects_effects(rwrg));
              }
              // note : rwrg has 0 (make clean declaration), 1 or 2 region for read and write
              //maybe direct convex hull if 2 region better than call find_union_regions
              region rg = find_union_store_regions((effects_effects(rwrg)), e);
              ifdebug(2) {
                pips_debug(2, "with region :\n");
                print_region(rg);
              }

              variable v = type_variable(entity_type(e));
              list l_dims = variable_dimensions(v);

              entity phi = entity_undefined;
              expression lower = expression_undefined;
              expression upper = expression_undefined;
              expression diff = expression_undefined;
              Pvecteur min, max;
              Psysteme ps = SC_UNDEFINED;
              int i=1;  // i use for debug and warning message, AND create some PHI

              FOREACH(DIMENSION, dim, l_dims) {
                // search for new lower/upper bond
                phi = make_phi_entity(i);
                ps = sc_dup(region_system(rg));
                ifdebug(5) {
                  pips_debug(5, "region system\n");
                  sc_print(ps, (get_variable_name_t) entity_local_name);
                  pips_debug(5, "precondition system\n");
                  sc_print(pre, (get_variable_name_t) entity_local_name);
                }
                if (sc_min_max_of_variable_C(ps, (Variable) phi, pre, &min, &max)) {
                  //if (vect_equal(max, pv_min) || vect_equal(min, pv_max))
                  //  pips_internal_error("This case never happens.\n");

                  // TODO: improve lower/upper bound generation if min or/and max is symbolic
                  //       generate a ternary operator expression...
                  if (!vect_equal(max, pv_max) && !vect_equal(max, pv_min))
                    upper = Pvecteur_to_expression(max);
                  else
                    pips_user_warning("don't success to compute new upper bound for dimension index %d\n", i);

                  if (!vect_equal(min, pv_min) && !vect_equal(min, pv_max)) {
                    lower = Pvecteur_to_expression(min);
                    if (!vecteur_nul_p(min)) {
                      if (!vect_equal(max, pv_max) && !vect_equal(max, pv_min))
                        diff = Pvecteur_to_expression(vect_substract(max, min));
                      else {
                        normalized norm_upper = NORMALIZE_EXPRESSION(dimension_upper(dim));
                        if (normalized_linear_p(norm_upper))
                          diff = Pvecteur_to_expression(vect_substract(normalized_linear(norm_upper), min));
                        else {
                          pips_user_warning("Not linear index expression."
                              "No implementation for complex expression yet."
                              "Done nothing for dimension index %d\n", i);
                          free_expression(lower);
                          lower = expression_undefined;
                        }
                      }
                    }
                  }
                  else
                    pips_user_warning("don't success to compute new lower bound for dimension index %d\n", i);
                }
                sc_rm(ps);
                ps = SC_UNDEFINED;
                phi = entity_undefined;

                // modify the new lower bond for dimension dim
                if (!expression_undefined_p(lower)) {
                  pips_debug(2, "new lower bound=%s\n",
                      expression_to_string(lower));
                  switch(language_tag(lang)) {
                  case is_language_fortran95:
                  case is_language_fortran:
                    dimension_lower(dim) = lower;
                    pips_user_error("Not implemented yet.\n");
                    //if (expression_one_p(lower)) {
                    //}
                    break;
                  case is_language_c:
                    if (expression_null_p(lower)) {
                      dimension_lower(dim) = lower;
                      compute_array->l_shift = CONS(EXPRESSION, int_to_expression(0), compute_array->l_shift);
                    }
                    else if (!c_array_notation) {
                      dimension_lower(dim) = make_zero_expression();
                      compute_array->l_shift = CONS(EXPRESSION, lower, compute_array->l_shift);
                      compute_array->need_shift_p = true;
                      // We have to shift all array accesses
                      pips_debug(2, "%s access need to be shift with -%s for dimension %d\n",
                          entity_name(e), expression_to_string(lower), i);
                    }
                    else {
                      pips_user_error("C array notation not implemented yet.\n"
                          "Warning :it's different from Fortran array notation.\n"
                          "In C : a[start:nbr_element] \n");
                      dimension_lower(dim) = lower;
                      // compute_array->l_shift no need, since we don't make any shift
                      //compute_array->l_shift = CONS(EXPRESSION, int_to_expression(0), compute_array->l_shift);
                    }
                    break;
                  default:
                    pips_internal_error("Language unknown !\n");
                    break;
                  }
                }
                else {
                  compute_array->l_shift = CONS(EXPRESSION, int_to_expression(0), compute_array->l_shift);
                }

                // modify the new upper bond for dimension dim
                if (!expression_undefined_p(upper) || !expression_undefined_p(diff)) {
                  ifdebug(2) {
                    if (!expression_undefined_p(upper) && !expression_undefined_p(diff))
                      pips_debug(2, "new upper bound: upper=%s, diff=%s\n",
                          expression_to_string(upper),
                          expression_to_string(diff));
                    else if (!expression_undefined_p(upper))
                      pips_debug(2, "new upper bound: upper=%s\n",
                          expression_to_string(upper));
                    else
                      pips_debug(2, "new upper bound: diff=%s\n",
                          expression_to_string(diff));
                  }
                  if (expression_undefined_p(diff))
                    dimension_upper(dim) = upper;
                  else {
                    if (!(language_fortran_p(lang) || language_fortran95_p(lang) || c_array_notation))
                      // language have not array notation
                      dimension_upper(dim) = diff;
                    else
                      if (!expression_undefined_p(upper))
                        dimension_upper(dim) = upper;
                  }
                }

                i++;
              } // END FOREACH(DIMENSION, dim, l_dims)

              // reorder the index shift at the right place
              if (compute_array->need_shift_p) {
                compute_array->l_shift = gen_nreverse(compute_array->l_shift);
                ifdebug(3) {
                  pips_debug(3, "shifted index factor :\n");
                  FOREACH(EXPRESSION, es, compute_array->l_shift)
                    print_expression(es);
                }
              }
            }
            else {
              //This case never happens
              pips_user_warning("unexpected case. entity %s not compute during useful_variables_regions?\n", entity_name(e));
            }

            ifdebug(2) {
              pips_debug(2, "entity with new bound :\n");
              print_entity_variable(e);
            }
            break;
            // We find the array to compute so no need to continue to iterate on the list
          }
        } // END for (ctx)
      }
    } // END FOREACH(ENTITY, e, l_decl)
    pips_debug(5, "end\n");
    vect_rm(pv_min);
    vect_rm(pv_max);
  }
  return true;
}

static bool shift_array_access(reference ref, list *ctx) {
  pips_debug(5, "begin\n");

  entity e = reference_variable(ref);
  list l_indices = reference_indices(ref);

  // The first following if is for optimization, to not have to search into the context list
  if (array_type_p(entity_type(e))) {
    ifdebug(2) {
      pips_debug(2, "work on reference :\n");
      print_reference(ref);
    }

    // search entity array e in the context
    // if not present, it's not a array to analyze/shift
    list l_temp = *ctx;
    for(struct context_resizing *compute_array; !ENDP(l_temp) && (compute_array= ((struct context_resizing *) (CAR(l_temp).p))); POP(l_temp)) {
      if (same_entity_p(e, compute_array->array)) {
        // we find the right element into the list
        if (compute_array->need_shift_p) {
          list l_shift = compute_array->l_shift;
          // pips_assert("number of shift indices is equal to the number of indices.\n", gen_length(l_shift)==gen_length(l_indices));

          int current_index = 1;
          expression current_exp;

          FOREACH(EXPRESSION, current_shift, l_shift) {
            current_exp = EXPRESSION(CAR(l_indices));
            // Do we need to shift? expression_undefined mean no
            if (!expression_undefined_p(current_shift)) {

              normalized norm_exp = NORMALIZE_EXPRESSION(current_exp);
              normalized norm_shift = NORMALIZE_EXPRESSION(current_shift);

              if (normalized_linear_p(norm_exp) && normalized_linear_p(norm_shift)) {
                // compute new index expression shifted
                Pvecteur pv_exp = normalized_linear(norm_exp);
                Pvecteur pv_shift = normalized_linear(norm_shift);
                expression new_exp = Pvecteur_to_expression(vect_substract(pv_exp, pv_shift));

                // affect new index expression shifted
                free_syntax(expression_syntax(current_exp));
                expression_syntax(current_exp) = expression_syntax(new_exp);
                free_expression_normalized(current_exp);
                //expression_normalized(current_exp) = expression_normalized(new_exp);
              }
              else {
                // normally, never happen
                pips_internal_error("Not linear index expression.\n");
              }
            }
            l_indices = CDR(l_indices);
            current_index++;
          }

          ifdebug(5) {
            pips_debug(5, "new reference of array access shifted:\n");
            print_reference(ref);
          }
        }
        break;
        // We find the array to compute so no need to continue to iterate on the list
      }
    } // END for (ctx)
  }

  pips_debug(2, "end\n");
  return true;
}


bool array_resizing_full_bottom_up(char* mod_name) {
  entity module;
  statement module_statement;
  bool good_result_p = true;

  debug_on("ARRAY_RESIZING_BOTTOM_UP_DEBUG_LEVEL");
  pips_debug(1, "begin\n");

  //-- configure environment --//
  set_current_module_entity(module_name_to_entity(mod_name));
  module = get_current_module_entity();

  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, mod_name, true) );
  module_statement = get_current_module_statement();

  pips_assert("Statement should be OK before...",
      statement_consistent_p(module_statement));

  //-- get dependencies --//
  set_precondition_map((statement_mapping)
      db_get_memory_resource(DBR_PRECONDITIONS, mod_name, true));

  set_useful_variables_effects((entity_effects)
      db_get_memory_resource(DBR_USEFUL_VARIABLES_REGIONS, mod_name, true));

  //-- Make the job -- //
  // 1. list the array variable to analyze
  list l_decl = code_declarations(entity_code(module));
  list l_var = init_list_of_array_to_compute(l_decl);

//  // 2. Compute the new array size, and modify the declaration
//  gen_context_recurse(module_statement, &l_var,
//      statement_domain, gen_true, modify_array_declaration);
//  // 3. Shift the access on the array when necessary
//  gen_context_recurse(module_statement, &l_var,
//      reference_domain, gen_true, shift_array_access);

  // note: since declaration isn't an explicit statement that modify the code
  // we are not force to compute the new array bound and modify the entity (ie the declaration)
  // when we leave the statement.
  // The computation of the new bound and his memorization at the enter of the statement (in gen_recurse)
  // permits to fuse step 2 and 3.
  // Else the solution is to split modify_array_declaration in two function:
  //   1. to compute
  // solution to fuse step 2 and 3
  gen_context_multi_recurse(module_statement, &l_var,
      statement_domain, modify_array_declaration, gen_null,
      reference_domain, gen_true, shift_array_access,
      NULL);

  free_list_of_array_to_compute(&l_var);

  pips_assert("Statement should be OK after...",
      statement_consistent_p(module_statement));

  //-- Save modified code to database --//
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, strdup(mod_name), module_statement);

  reset_precondition_map();
  reset_useful_variables_effects();
  reset_current_module_statement();
  reset_current_module_entity();

  pips_debug(1, "end\n");
  debug_off();

  return (good_result_p);
}

#endif // BUILDER_ARRAY_RESIZING_BOTTOM_UP

