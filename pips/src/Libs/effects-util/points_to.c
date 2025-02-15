/*

  $Id: points_to.c 23412 2017-08-09 15:07:09Z irigoin $

  Copyright 1989-2016 MINES ParisTech
  Copyright 2009-2010 HPC Project

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

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "genC.h"
#include "linear.h"
#include "ri.h"
#include "effects.h"
#include "ri-util.h"
#include "prettyprint.h"

#include "effects-util.h"
#include "text-util.h"

#include "misc.h"
#include "properties.h"

/***************************************/
/* Function storing points to information attached to a statement
 */

/* Generate a global variable holding a statement_points_to, a mapping
 * from statements to lists of points-to arcs. The variable is called
 * "pt_to_list_object".
 *
 * The macro also generates a set of functions used to deal with this global variables.
 *
 * The functions are defined in newgen_generic_function.h:
 *
 * pt_to_list_undefined_p()
 *
 * reset_pt_to_list()
 *
 * error_reset_pt_to_list()
 *
 * set_pt_to_list(o)
 *
 * get_pt_to_list()
 *
 * store_pt_to_list(k, v)
 *
 * update_pt_to_list(k, v)
 *
 * load_pt_to_list(k)
 *
 * delete_pt_to_list(k)
 *
 * bound_pt_to_list_p(k)
 *
 * store_or_update_pt_to_list(k, v)
*/
GENERIC_GLOBAL_FUNCTION(pt_to_list, statement_points_to)

/* Functions specific to points-to analysis
*/

/* 
 */
cell make_anywhere_points_to_cell(type t)
{
  entity n = entity_undefined;
  if(get_bool_property("ALIASING_ACROSS_TYPES"))
    n = entity_all_locations();
  else
    n = entity_all_xxx_locations_typed(ANYWHERE_LOCATION, t);
  reference r = make_reference(n, NIL);
  cell c = make_cell_reference(r);
  return c;
}

bool formal_parameter_points_to_cell_p(cell c)
{
  bool formal_p = true;
  reference r = cell_any_reference(c);
  entity v = reference_variable(r);
  formal_p = formal_parameter_p(v);
  return formal_p;
}

bool stub_points_to_cell_p(cell c)
{
  bool formal_p = true;
  reference r = cell_any_reference(c);
  entity v = reference_variable(r);
  formal_p = entity_stub_sink_p(v); // FI: can be a source too
  return formal_p;
}

bool points_to_cell_in_list_p(cell c, list L)
{
  bool found_p = false;
  FOREACH(CELL, lc, L) {
    if(cell_equal_p(c,lc)) {
      found_p =true;
      break;
    }
  }
  return found_p;
}

/* Add in "l1" elements of "l2" that are not yet in "l1". List "l2" is
 * then destroyed.
 *
 * This is a set union.
 */
list merge_points_to_cell_lists(list l1, list l2)
{
  list lt = NIL;
  FOREACH(CELL, c2, l2) {
    if(!points_to_cell_in_list_p(c2, l1)) {
      lt = CONS(CELL,c2, lt);
    }
  }
  lt = gen_nreverse(lt);
  l1 = gen_nconc(l1, lt);
  gen_free_list(l2);
  return l1;
}

/* Two cells are related if they are based on the same entity */
bool related_points_to_cell_in_list_p(cell c, list L)
{
  bool found_p = false;
  reference rc = cell_any_reference(c);
  entity ec = reference_variable(rc);
  FOREACH(CELL, lc, L) {
    reference rlc = cell_any_reference(lc);
    entity elc = reference_variable(rlc);
    if(ec==elc) {
      found_p =true;
      break;
    }
  }
  return found_p;
}

bool related_points_to_cells_p(cell c1, cell c2)
{
  bool related_p = false;
  reference rc1 = cell_any_reference(c1);
  entity ec1 = reference_variable(rc1);
  reference rc2 = cell_any_reference(c2);
  entity ec2 = reference_variable(rc2);
  related_p = (ec1==ec2);
  return related_p;
}

 /* Debug: print a cell list for points-to. Parameter f is not useful
    in a debugging context. */
void fprint_points_to_cell(FILE * f __attribute__ ((unused)), cell c)
{
  int dn = cell_domain_number(c);

  // For debugging with gdb, dynamic type checking
  if(dn==cell_domain) {
    if(cell_undefined_p(c))
      fprintf(stderr, "cell undefined\n");
    else {
      reference r = cell_any_reference(c);
      print_reference(r);
    }
  }
  else
    fprintf(stderr, "Not a Newgen cell object\n");
}

/* Debug: use stderr */
void print_points_to_cell(cell c)
{
  fprint_points_to_cell(stderr, c);
}

/* Debug */
void print_points_to_cells(list cl)
{
  if(ENDP(cl))
    fprintf(stderr, "Empty cell list");
  else {
    entity m = get_current_module_entity();
    FOREACH(CELL, c, cl) {
      reference r = cell_any_reference(c);
      entity v = reference_variable(r);
      /* *ANY_MODULE* is unfortunately not an entity... */
      entity mv =  module_name_to_entity(entity_module_name(v));
      if(!entity_undefined_p(mv) && m!=mv)
	fprintf(stderr,"%s" MODULE_SEP_STRING, entity_local_name(mv));
      print_points_to_cell(c);
      if(!ENDP(CDR(cl)))
	fprintf(stderr, ", ");
    }
  }
  fprintf(stderr, "\n");
}

/* Check if expression "e" is a reference to a struct field. */
bool field_reference_expression_p(expression e)
{
  bool field_p = false;
  syntax s = expression_syntax(e);
  if(syntax_reference_p(s)) {
    reference r = syntax_reference(s);
    entity f = reference_variable(r);
    field_p = entity_field_p(f);
  }
  return field_p;
}

/* Compute the number of array subscript at the end of a points_to_reference
 *
 * Look for the last field subscript and count the number of
 * subscripts after it. If no field susbcript is found, then all
 * subscripts are final array subscripts.
 *
 * To make thinks easier, the subscript list is reversed.
 */
int points_to_reference_to_final_dimension(reference r)
{
  list sl = reference_indices(r);
  sl = gen_nreverse(sl);
  int d = 0;
  FOREACH(EXPRESSION, e, sl) {
    if(field_reference_expression_p(e))
      break;
    else
      d++;
  }
  sl = gen_nreverse(sl);
  reference_indices(r) = sl;
  return d;
}

/* Substitute the subscripts "sl" in points-to reference "r" just after the
 * last field subscript by "nsl".
 *
 * "sl" must be broken into three parts, possibly empty:
 *
 *  1. The first part that ends up at the last field reference. It may
 *  be empty when no field is referenced.
 *
 *  2. The second part that starts just after the last field reference
 *  and that counts at most as many elements as the new subscript
 *  list, "nsl". This part must be substituted.
 *
 *  3. The third part that is left unchanged after substitution.
 *
 * Issue: how do you know that the initial array subscript must be
 * preserved because it is an implicit dimension added for pointer
 * arithmetics?
 */
void points_to_reference_update_final_subscripts(reference r, list nsl)
{
  list sl = reference_indices(r);
  list sl1 = NIL, sl3 = NIL, sl23 = NIL;

  sl = gen_nreverse(sl); // sl1 and sl23 are built in the right order
  bool found_p = false;
  bool skip_one_p = false; // to skip indices added for pointer arithmetic
  FOREACH(EXPRESSION, e, sl) {
    if(field_reference_expression_p(e)) {
      type et = expression_to_type(e);
      if(pointer_type_p(et))
	skip_one_p = true;
      found_p = true;
      free_type(et);
    }
    if(found_p) {
      /* build sl1 */
      sl1 = CONS(EXPRESSION, e , sl1);
    }
    else
      sl23 = CONS(EXPRESSION, e , sl23);
  }

  if(skip_one_p && ENDP(sl23) && !ENDP(nsl)) {
    pips_internal_error("We are not generating a memory access constant path.\n");
  }

  // FI: place the new indices as early as possible
#if 0
  int n = (int) gen_length(nsl);
  int i = 0;
  FOREACH(EXPRESSION, e, sl23) {
    if(skip_one_p) {
      sl1 = gen_nconc(sl1, CONS(EXPRESSION, e , NIL));
      skip_one_p = false;
    }
    else {
      if(i<n)
	free_expression(e);
      else
	sl3 = gen_nconc(sl3, CONS(EXPRESSION, e, NIL));
      i++;
    }
  }

  sl = gen_nconc(sl1, nsl);
  sl = gen_nconc(sl, sl3);
#endif

  // FI: place the new indices as late as possible
  int n = (int) gen_length(nsl);
  int n23 = (int) gen_length(sl23);
  int i = 0;
  FOREACH(EXPRESSION, e, sl23) {
    if(i>=n23-n)
      free_expression(e);
    else
      sl3 = gen_nconc(sl3, CONS(EXPRESSION, e, NIL));
    i++;
  }

  sl = gen_nconc(sl1, sl3);
  sl = gen_nconc(sl, nsl);

  gen_free_list(sl23);
  reference_indices(r) = sl;

  // We do not want to generate indirection in the reference
  // The exactitude information is not relevant here
  // bool exact_p;
  // pips_assert("The reference is a constant memory access path",
  //             !effect_reference_dereferencing_p( r, &exact_p));
  // Might only work for standard references and not for points-to
  // references: core dumps with points-to references.
}

/* Look for the index in "r" that corresponds to a pointer of type "t"
 * and return the corresponding element list. In other words, the type
 * of "&r" is "t".
 *
 * It is done in a very inefficient way
 */
list points_to_reference_to_typed_index(reference r, type t)
{
  bool to_be_freed;
  type rt = points_to_reference_to_type(r, &to_be_freed);
  list rsl = reference_indices(r); // reference subscript list
  pips_assert("t is a pointer type", C_pointer_type_p(t));
  type pt = C_type_to_pointed_type(t);
  list psl = list_undefined; // pointed subscript list

  if(array_pointer_type_equal_p(rt, pt))
    psl = gen_last(rsl);
  else {
    if(to_be_freed) free_type(rt);
    entity v = reference_variable(r);
    list nl = NIL;
    int i;
    int n = (int) gen_length(rsl);
    reference nr = make_reference(v, nl);
    bool found_p = false;

    for(i=0;i<n;i++) {
      nl = gen_nconc(nl, CONS(EXPRESSION,
			      copy_expression(EXPRESSION(gen_nth(i, rsl))),
			      NIL));
      reference_indices(nr) = nl;
      rt = points_to_reference_to_type(nr, &to_be_freed);
      if(array_pointer_type_equal_p(rt, pt)) {
	found_p = true;
	break;
      }
    }

    free_reference(nr);

    if(found_p)
      psl = gen_nthcdr(i, rsl);
    else {
      // The issue may be due to a user bug, as was the case in
      // Strict_typing.sub/malloc03.c
      if(entity_heap_location_p(v)) {
	// It would be nice to have a current statement stack...
	pips_user_error("The dynamic allocation of \"%s\" is likely "
			"to be inadequate with its use in the current "
			"statement.\n", entity_local_name(v));
      }
      else
	pips_internal_error("Type not found.\n");
    }
  }

  free_type(pt);

  return psl;
}

/* Is it a unique concrete memory location?
 *
 * Plus NULL? No doubt about the value of the pointer...
 *
 * Plus undefined? No doubt about the indeterminate value of the
 * pointer according to C standard...
 */
bool atomic_points_to_cell_p(cell c)
{
  reference r = cell_any_reference(c);
  bool atomic_p = null_cell_p(c)
    || nowhere_cell_p(c) // FI: added for EffectsWithPointsTo/call30.c
    || atomic_points_to_reference_p(r);

  // FI: atomic_p should be false for all abstract locations
  // This is dealt with by atomic_points_to_reference_p()
  /*
  if(atomic_p && (heap_cell_p(c) || all_heap_locations_cell_p(c)))
    atomic_p = false;

  if(atomic_p) {
    atomic_p = !cell_abstract_location_p(c);
  }
  */

  return atomic_p;
}

/* Is it a unique concrete memory location?
 *
 * If strict_p, stubs are not considered atomic, as is the case in an
 * interprocedural setting since they can be associated to several
 * cells in the caller frame.
 *
 * Else, stubs are not considered non atomic per se.
 */
bool generic_atomic_points_to_cell_p(cell c, bool strict_p)
{
  reference r = cell_any_reference(c);
  bool atomic_p = null_cell_p(c)
    || generic_atomic_points_to_reference_p(r, strict_p);

  return atomic_p;
}

/* Is it a unique concrete memory location?
 *
 * No, if it is a reference to an abstract location.
 *
 * No, if the subscripts include an unbounded expression.
 *
 * Very preliminary version. One of the keys to Amira Mensi's work.
 *
 * More about stubs: a stub is not NULL but there is no information to
 * know if they represent one address or a set of addresses. Unless
 * the intraprocedural points-to analysis is performed for each
 * combination of atomic/non-atomic stub, safety implies that
 * stub-based references are not atomic (strict_p=true). In some other
 * cases, you know that a stub does represent a unique location
 * (strict_p=false).
 *
 * Note: it is assumed that the reference is a points-to
 * reference. All subscripts are constants, field references or
 * unbounded expressions.
 *
 * Note: FI, I have a probleme when calling this function from a
 * proper effects environment. In that case, stubs might be assumed to
 * be unique memory locations. The exactness information can be
 * derived from the numer of targets in the matching list.
 *
 * Note 2: FI, I do not understand why the type of the reference is
 * not taken into account.
 */
bool generic_atomic_points_to_reference_p(reference r, bool strict_p)
{
  bool atomic_p = false;
  entity v = reference_variable(r);

  if(!entity_null_locations_p(v) // FI: NULL is considered atomic
     && !entity_typed_nowhere_locations_p(v)
     && !entity_typed_anywhere_locations_p(v)
     && !entity_anywhere_locations_p(v)
     && !entity_heap_location_p(v)) {
    list sl = reference_indices(r);
    //entity v = reference_variable(r);
    if(!entity_stub_sink_p(v) || !strict_p) {
      atomic_p = true;
      FOREACH(EXPRESSION, se, sl) {
	if(unbounded_expression_p(se)) {
	  atomic_p = false;
	  break;
	}
	else if(expression_range_p(se)) {
	  atomic_p = false;
	  break;
	}
      }
    }
  }

  return atomic_p;
}

bool atomic_points_to_reference_p(reference r)
{
  return generic_atomic_points_to_reference_p(r, true);
}

/* points-to cells use abstract addresses, hence the proper comparison
 * is an intersection. simple references are considered to be
 * singleton.
 *
 * Assume no aliasing between variables and within data structures.
 *
 * It is safe to assume intersection...
 */
bool points_to_cells_intersect_p(cell lc, cell rc)
{
  bool intersect_p = false;
  if(cell_equal_p(lc, rc)) {
    // FI: too simple... All the subscript should be checked.
    // unbounded expressions should be used to decide about a possible
    // intersection... Unless this is guarded by
    // atomic_points_to_reference_p(). To be investigated.
    intersect_p = true;
  }
  else {
    // Look for abstract domains
    // Probably pretty complex...
    // Simple first version...
    reference lr = cell_any_reference(lc);
    entity le = reference_variable(lr);
    reference rr = cell_any_reference(rc);
    entity re = reference_variable(rr);
    intersect_p = entities_may_conflict_p(le, re);
  }
  return intersect_p;
}

/* Allocate a cell that is the minimal upper bound of the cells in
 * list "cl" according to the points-to cell lattice...
 *
 * An over-approximation is always safe. So, an anywhere cell, typed
 * or not, can be returned in a first drat implementation.
 *
 * The points-to cell lattice is the product of three lattices, the
 * module lattice, the type lattice and the abstracct reference
 * lattice...
 */
cell points_to_cells_minimal_upper_bound(list cl __attribute__ ((unused)))
{
#if 0
  entity m = points_to_cells_minimal_module_upper_bound(cl);
  type t = points_to_cells_minimal_type_upper_bound(cl);
  reference r = points_to_cells_minimal_reference_upper_bound(m, t, cl);
  cell c = make_cell_reference(r);
#endif
  type t = make_scalar_overloaded_type();
  cell c = make_anywhere_points_to_cell(t);
  return c;
}

entity points_to_cells_minimal_module_upper_bound(list cl __attribute__ ((unused)))
{
  entity m = entity_undefined;
  return m;
}

type points_to_cells_minimal_type_upper_bound(list cl __attribute__ ((unused)))
{
  type t = type_undefined;
  return t;
}

reference points_to_cells_minimal_reference_upper_bound(entity m __attribute__ ((unused)), type t __attribute__ ((unused)), list cl __attribute__ ((unused)))
{
  reference r = reference_undefined;
  return r;
}

/* Is this a reference to an array or a reference to a pointer? This
   is not linked to the type of the reference, as a reference may be a
   pointer, such as "a[10]" when "a" is declared int "a[10][20]".*/
bool points_to_array_reference_p(reference r)
{
  bool array_p = false;
  list sl = reference_indices(r);
  entity v = reference_variable(r);

  if(ENDP(sl)) {
    type t = entity_basic_concrete_type(v);
    array_p = array_type_p(t);
  }
  else {
    /* Look for the last field among the subscript */
    list rsl = gen_nreverse(sl);
    type t = type_undefined;
    int i = 0;
    FOREACH(EXPRESSION, se, rsl) {
      if(field_reference_expression_p(se)) {
	entity f = reference_variable(expression_reference(se));
	t = entity_basic_concrete_type(f);
	break;
      }
      i++;
    }
    if(type_undefined_p(t)) {
      t = entity_basic_concrete_type(v);
      variable vt = type_variable(t);
      list dl = variable_dimensions(vt);
      int d = (int) gen_length(dl);
      int i = (int) gen_length(rsl);
      if(i<d)
	array_p = true;
    }
    else {
      if(i==0) { // FI: could be merged with the "else if" clause
	array_p = array_type_p(t);
      }
      else if(array_type_p(t)) {
	variable vt = type_variable(t);
	list dl = variable_dimensions(vt);
	int d = (int) gen_length(dl);
	if(i<d)
	  array_p = true;
      }
    }
    reference_indices(r) = gen_nreverse(rsl);
  }
  return array_p;
}

/* If this is an array reference, what is the type of the underlying array type?
 *
 * This information cannot be obtained by direct type information
 * because subarrays are typed as pointers to even smaller arrays.
 *
 * If it is not an array reference, the returned type is undefined.
 *
 * No new type is allocated.
 */
type points_to_array_reference_to_type(reference r)
{
  list sl = reference_indices(r);
  entity v = reference_variable(r);
  type t = type_undefined;

  if(ENDP(sl)) {
    t = entity_basic_concrete_type(v);
  }
  else {
    /* Look for the last field among the subscript */
    list rsl = gen_nreverse(sl);
    FOREACH(EXPRESSION, se, rsl) {
      if(field_reference_expression_p(se)) {
	entity f = reference_variable(expression_reference(se));
	t = entity_basic_concrete_type(f);
	break;
      }
    }
    if(type_undefined_p(t)) {
      t = entity_basic_concrete_type(v);
    }
    else {
      ;
    }
    reference_indices(r) = gen_nreverse(rsl);
  }
  return t;
}


/* Add a set of zero subscripts to a constant memory path reference "r" by side effect.
 *
 * Used when a partial array reference must be converted into a
 * reference to the first array element (zero_p==true) or to any
 * element (zero_p==false).
 *
 * The difficulty lies with field subscripts...
 */
void complete_points_to_reference_with_fixed_subscripts(reference r, bool zero_p)
{
  type t = type_undefined;

  // FI: this assert makes sense within the ri-util framework but is
  // too strong for the kind of references used in effects-util
  // pips_assert("scalar type", ENDP(reference_indices(r)));

  /* Find the current number of effective subscripts: is there a field
     subscript somewhere? */
  list sl = reference_indices(r);
  entity v = reference_variable(r);
  list rsl = gen_nreverse(sl); // sl is no longer available
  int i = 0;
  bool field_found_p = false;

  FOREACH(EXPRESSION, se, rsl) {
    if(field_expression_p(se)) {
      reference fr = expression_reference(se);
      entity f = reference_variable(fr);
      t = entity_basic_concrete_type(f); 
      field_found_p = true;
      break;
    }
    i++;
  }

  if(!field_found_p)
    t = entity_basic_concrete_type(v);

  variable vt = type_variable(t);
  list dl = variable_dimensions(vt);
  int d = (int) gen_length(dl);

  /* FI: this may happen when reference "r" is not a constant memory path */
  pips_assert("Not too many subscripts wrt the type.\n", i<=d);

  list nsl = NIL; // subscript list
  int j;
  for(j=i+1;j<=d;j++) {
    expression s = zero_p? int_to_expression(0) : make_unbounded_expression();
    // reference_indices(r) = CONS(EXPRESSION, s, reference_indices(r));
    nsl = CONS(EXPRESSION, s, nsl);
  }

  reference_indices(r) = gen_nreverse(rsl);
  reference_indices(r) = gen_nconc(reference_indices(r), nsl);
}

void complete_points_to_reference_with_zero_subscripts(reference r)
{
  complete_points_to_reference_with_fixed_subscripts(r, true);
}

bool cells_must_point_to_null_p(list cl)
{
  bool must_p = true;
  pips_assert("The input list is not empty", !ENDP(cl));
  FOREACH(CELL, c, cl) {
    if(!null_cell_p(c)) {
      must_p = false;
      break;
    }
  }
  return must_p;
}

bool cells_may_not_point_to_null_p(list cl)
{
  bool may_not_p = true;
  pips_assert("The input list is not empty", !ENDP(cl));
  FOREACH(CELL, c, cl) {
    if(null_cell_p(c) || nowhere_cell_p(c)) {
      may_not_p = false;
      break;
    }
  }
  return may_not_p;
}

/* A set of functions called cell_points_to_xxxx(cell s, set pts)
 * where set pts is a points-to relation set.
 *
 * The definition domain of these functions is key to their use:
 *
 * 1. if the type of the source s is not a pointer type, should we
 * return false or abort because s is not in the definition domain?
 *
 * 2. if source s does not appear at all in pts, should we return
 * false or abort because s is not in the definition domain?
 *
 * If both conditions are selected, the resulting definition domain is
 * the definition domain of the mapping pts.
 *
 * If a more relaxed definition domain is sometimes useful, then
 * strict and non-strict versions of these functions should be
 * provided, with a clear semantics for their true and false results.
 *
 * Because cell s may point to one or many cells in pts, which is a
 * relation and not a mapping, the caller may be interested in a may
 * or must point. The information may be convened directly by using
 * distinct function names, cell_must_points_to_xxxx or
 * cell_may_points_to_xxxx, or by adding a pointer to a boolean,
 * exact_p, in the function profiles, which may save time by not
 * looping twice on pts arcs.
 *
 * This can be implemented using the approximation information of the
 * arcs in pts... if it is trusted. Or recomputed from the arcs in pts.
 *
 * Flexibility is also introduced by the use of cell_equivalent_p()
 * instead of cell_equal_p(). If the former is used, cells derived
 * from cell s are considered when s if not a pointer. This leads to
 * weird behaviors. For instance, if the source s is a struct, s.f1
 * and s.f2 will be considered. If s.f1 points to some concrete
 * location and s.f2 points to nowhere (undefined pointer), what
 * result should be returned? The advantage is that the caller does
 * not have to generate s.f1 and s.f2 which are simply found in set
 * pts.
 */

/* Does cell "source" points toward a non null fully defined cell in
 * points-to set pts?
 *
 * The function name is not well chosen. Something like
 * cell_points_to_defined_cell_p()/
 */
bool cell_points_to_non_null_sink_in_set_p(cell source, set pts)
{
  bool non_null_p = false;
  type st = points_to_cell_to_concrete_type(source);
  pips_assert("The cell is a pointer", !array_type_p(st) && pointer_type_p(st));
  SET_FOREACH(points_to, pt, pts) {
    cell pt_source = points_to_source(pt);
    if(cell_equal_p(pt_source, source)) {
      //if(cell_equivalent_p(pt_source, source)) {
      cell pt_sink = points_to_sink(pt);
      if(null_cell_p(pt_sink))
	;
      else if(nowhere_cell_p(pt_sink))
	;
      else {
	non_null_p = true;
	break;
      }
    }
  }
  return non_null_p;
}

bool cell_points_to_nowhere_sink_in_set_p(cell source, set pts)
{
  bool nowhere_p = false;
  type st = points_to_cell_to_concrete_type(source);
  pips_assert("The cell is a pointer", !array_type_p(st) && pointer_type_p(st));
  SET_FOREACH(points_to, pt, pts) {
    cell pt_source = points_to_source(pt);
    if(cell_equal_p(pt_source, source)) {
    //if(cell_equivalent_p(pt_source, source)) {
      cell pt_sink = points_to_sink(pt);
      if(null_cell_p(pt_sink))
	;
      else if(nowhere_cell_p(pt_sink)) {
	nowhere_p = true;
	break;
      }
      else {
	;
      }
    }
  }
  return nowhere_p;
}

/* How are array handled in pts? do we have arcs "a->a"? */
bool cell_must_point_to_nowhere_sink_in_set_p(cell source, set pts)
{
  bool nowhere_p = false;
  type st = points_to_cell_to_concrete_type(source);
  pips_assert("The cell is a pointer", !array_type_p(st) && pointer_type_p(st));
  //type st = points_to_cell_to_concrete_type(source);
  //if(!array_type_p(st) && pointer_type_p(st)) {
    SET_FOREACH(points_to, pt, pts) {
      cell pt_source = points_to_source(pt);
      if(cell_equal_p(pt_source, source)) {
	//if(cell_equivalent_p(pt_source, source)) {
	cell pt_sink = points_to_sink(pt);
	if(null_cell_p(pt_sink))
	  ;
	else if(nowhere_cell_p(pt_sink)) {
	  approximation ap = points_to_approximation(pt);
	  nowhere_p = approximation_must_p(ap) || approximation_exact_p(ap);
	  break;
	}
	else {
	  ;
	}
      }
    }
    //}
  return nowhere_p;
}

bool cell_points_to_null_sink_in_set_p(cell source, set pts)
{
  bool null_p = false;
  type st = points_to_cell_to_concrete_type(source);
  pips_assert("The cell is a pointer", !array_type_p(st) && pointer_type_p(st));
  SET_FOREACH(points_to, pt, pts) {
    cell pt_source = points_to_source(pt);
    if(cell_equal_p(pt_source, source)) {
      cell pt_sink = points_to_sink(pt);
      if(null_cell_p(pt_sink)) {
	null_p = true;
	break;
      }
    }
  }
  return null_p;
}

bool points_to_cell_equal_p(cell c1, cell c2)
{
  reference r1 = cell_any_reference(c1);
  reference r2 = cell_any_reference(c2);
  return reference_equal_p(r1,r2);
}

/* See if an arc like "spt" exists in set "in", regardless of its
 * approximation. If yes, returns the approximation of the arc found
 * in "in".
 *
 * See also arc_in_points_to_set_p(), which requires full identity
 */
bool similar_arc_in_points_to_set_p(points_to spt, set in, approximation * pa)
{
  bool in_p = false;
  cell spt_source = points_to_source(spt);
  cell spt_sink = points_to_sink(spt);
  SET_FOREACH(points_to, pt, in) {
    if(points_to_cell_equal_p(spt_source, points_to_source(pt))
       && points_to_cell_equal_p(spt_sink, points_to_sink(pt))) {
      *pa = points_to_approximation(pt);
      in_p = true;
      break;
    }
  }
  return in_p;
}

/* Return a list of cells that are larger than cell "c" in the
 * points-to cell lattice.
 *
 * This goal is quite open because a[1][2] is dominated by both
 * a[*][2] and a[1][*], then by a[*][*]. Assuming "a" is variable of
 * function "foo", then we have "foo:*STACK*_b0",
 * "*ANYMODULE*:*STACK*_b0", "foo:*ANYWHERE*_b0",
 * "*ANYMODULE*:*ANYWHERE*_b0", "*ANYMODULE*:*ANYWHERE*".
 *
 * They would all be useful to guarantee the consistency of the
 * points-to information wrt the points-to cell lattice, but we'd
 * rather maintain a partially consistent points-to graph and rely on
 * functions using it to add the necessary points-to arcs.
 *
 * A lattice-consistent points-to graph would contain too many arcs as
 * x->y implies x'->y' for all x' bigger than x and y' bigger then
 * y...
 *
 * For the time being, we only need to convert a[i][j][k] into a[*][*][*]
 * when i, j and k are real subscript expressions, not fields.
 *
 * We return an empty list when cell "c" does not need any upper
 * bound, as is the case with a, a[f] where f is a field, a[*] and all
 * the abstract locations.
 *
 * So, for the time being, this function returns a list with one or
 * zero elements.
 */
list points_to_cell_to_upper_bound_points_to_cells(cell c)
{
  list ubl = NIL; // upper bound list
  reference r = cell_any_reference(c);
  entity v = reference_variable(r);
  if(!entity_abstract_location_p(v)) {
    list sel = reference_indices(r); // subscript expression list
    list nsel = NIL; // new subscript expression list
    bool new_cell_p = false;
    FOREACH(EXPRESSION, se, sel) {
      expression nse = expression_undefined;
      if(integer_expression_p(se)) {
	nse = make_unbounded_expression();
	new_cell_p = true;
      }
      else
	nse = copy_expression(se);
      nsel = CONS(EXPRESSION, nse, nsel);
    }
    if(new_cell_p) {
      nsel = gen_nreverse(nsel);
      reference nr = make_reference(v, nsel);
      cell nc = make_cell_reference(nr);
      ubl = CONS(CELL, nc, ubl);
    }
    else
      gen_full_free_list(nsel);
  }
  return ubl;
}

/* Add to list "l" cells that are upper bound cells of the cells
 * already in list "l" and return list "l".
 */
list points_to_cells_to_upper_bound_points_to_cells(list cl)
{
  list ubl = NIL;
  FOREACH(CELL, c, cl) {
    list cubl = points_to_cell_to_upper_bound_points_to_cells(c);
    ubl = gen_nconc(ubl, cubl);
  }
  ubl = gen_nconc(cl, ubl);
  return ubl;
}

/* See if the subscript list sl is precise, i.e. if is does not
 * contain any unbounded expression.
 *
 * It is assumed that it is a points-to subscript list. Each subscript
 * is either an integer constant, or a field reference or an unbounded
 * expression.
 *
 * This function may have been defined several times...
 */
bool exact_points_to_subscript_list_p(list sl)
{
  bool exact_p = true;
  FOREACH(EXPRESSION, s, sl) {
    if(unbounded_expression_p(s)) {
      exact_p = false;
      break;
    }
  }
  return exact_p;
}

/* Two subscript are compatible if they are equal or if one of them is
   unbounded. */
bool compatible_points_to_subscripts_p(expression s1, expression s2)
{
  bool compatible_p = true;
  bool u1 = unbounded_expression_p(s1);
  if(!u1) {
    bool u2 = unbounded_expression_p(s2);
    if(!u2) {
      /* In the ponts-to context s1 and s2 should be either integer
	 constants or field references. */
      compatible_p = expression_equal_p(s1, s2);
    }
  }
  return compatible_p;
}

/* The value of the source can often be expressed with different
 * subscript lists. For instance, a, a[0], a[0][0] have different
 * types but the same value if a is a 2-D array.
 *
 * This function allocated a new points-to object whose sink has a
 * minimal number of indices.
 *
 * FI: I have added this function to deal with pointers to arrays. It
 * is called from generic_reference_to_points_to_matching_list() to
 * try to adapt the points-to information to the undefined
 * requirements of Beatrice's functions for regions_with_points_to. I
 * do not think the function below is correct when structs are
 * involved... The stripping may be useful, but it should be much more careful.
 *
 * adapt_reference_to_type() might be better here to adjust the
 * subscripts in sink.
 *
 */
points_to points_to_with_stripped_sink(points_to pt,
				       int (*line_number_func)(void))
{
  cell source = points_to_source(pt);
  cell sink = points_to_sink(pt);
  cell new_sink_cell = cell_undefined;

  // FI: first implementation
  if(false) {
    reference source_r = cell_any_reference(source);
    list source_sl = reference_indices(source_r);
    list c_source_sl = list_undefined;

    reference sink_r = cell_any_reference(sink);
    // FI: sink_sl is longer than source_sl if pt is semantically correct
    list sink_sl = reference_indices(sink_r);
    list c_sink_sl = list_undefined;
    entity sink_e = reference_variable(sink_r);

    list new_sink_sl = NIL;
    for(c_source_sl = source_sl, c_sink_sl = sink_sl;
	!ENDP(c_source_sl);
	POP(c_source_sl), POP(c_sink_sl)) {
      expression s = copy_expression(EXPRESSION(CAR(c_sink_sl)));
      new_sink_sl = CONS(EXPRESSION, s, new_sink_sl);
    }
    if(!get_bool_property("POINTS_TO_STRICT_POINTER_TYPES")
       && !anywhere_cell_p(sink)
       && !cell_typed_anywhere_locations_p(sink)
       && !ENDP(c_sink_sl)) {
      /* Add the implicit dimension */
      expression s = copy_expression(EXPRESSION(CAR(c_sink_sl)));
      new_sink_sl = CONS(EXPRESSION, s, new_sink_sl);
    }
    new_sink_sl = gen_nreverse(new_sink_sl);

    new_sink_cell = make_cell_reference(make_reference(sink_e, new_sink_sl));
  }
  else {
    // Second implementation
    if(anywhere_cell_p(sink) || cell_typed_anywhere_locations_p(sink)
       || null_cell_p(sink) || nowhere_cell_p(sink)
       // FI: why is the typed heap cell not handled too?
       || heap_cell_p(sink)) {
      new_sink_cell = copy_cell(sink);
    }
    else {
      new_sink_cell = copy_cell(sink);
      reference n_sink_r = cell_any_reference(new_sink_cell);
      type source_t = points_to_cell_to_concrete_type(source);
      if(pointer_type_p(source_t)) {
	type source_pt = type_to_pointed_type(source_t);
	if(adapt_reference_to_type(n_sink_r, source_pt, line_number_func))
	  ;
	else {
	  /* Dealing with the special case of a constant p -> "foo"
	   *
	   * The other option would be to accept "foo"[0] as a valid
	   * reference... Extending references to constant functions
	   * is a first step...
	   */
	  bool ok_p = false;
	  type sink_t = points_to_reference_to_concrete_type(n_sink_r);
	  if(char_type_p(source_pt)) {
	    if(char_star_constant_function_type_p(sink_t))
	      ok_p = true;
	  }
	  if(!ok_p)
	    pips_internal_error("The type of a sink cell, \"%s\", is not compatible with the source cell, \"%s\".\n",
				safe_type_to_string(sink_t),
				safe_type_to_string(source_t));
	}
      }

      else
	pips_internal_error("The type of a source cell is not a pointer.\n");
    }
  }

  points_to npt = make_points_to(copy_cell(source),
				 new_sink_cell,
				 copy_approximation(points_to_approximation(pt)),
				 make_descriptor_none());
  return npt;
}

/**
 * \param t        any type, but here initial reference type
 * \param sl       remaining subscript list, all subscripts are supposed
 *                 to be store independent
 * \return         true none of the subsequence subscript implies
 *                 a dereferencing
 *
 * Reduce the length of the subscript list
 */
bool recursive_store_independent_points_to_reference_p(type t, list sl){
  bool independent_p = false;

  if(ENDP(sl))
    independent_p = true;
  else if(struct_type_p(t)) {
    expression se = EXPRESSION(CAR(sl));
    reference r = expression_reference(se);
    entity f = reference_variable(r);
    type nt = entity_basic_concrete_type(f);
    independent_p = recursive_store_independent_points_to_reference_p(nt, CDR(sl));
  }
  else if(array_type_p(t)) {
    unsigned int d = array_type_dimension(t); 
    if(gen_length(sl)<=d)
      independent_p = true;
    else {
      type nt = array_type_to_element_type(t);
      list nsl = sl;
      unsigned int i;
      // Skip the array subscripts
      for(i=0;i<d;i++)
	nsl = CDR(nsl);
      independent_p = recursive_store_independent_points_to_reference_p(nt, nsl);
    }
  }
  else if(pointer_type_p(t)) {
    /* There are indices because of the first test on the number of subscripts */
    independent_p = false;
  }
  else {
    // FI: It is more difficult... and it must have been programmed
    // somewhere else.
    pips_internal_error("Not implemented yet");
  }

  return independent_p;
}

/* Functions for points-to references, the kind of references used in
 * points-to cells.
 */

/* Does this points-to reference define the same set of memory locations
 * regardless of the current (environment and) memory state?
 *
 * The reference indices can be used to encode fields in data
 * structures and can be applied to pointers as offset.
 *
 * The types associated to the reference and to prefixes of the index
 * list change. So a pointer dereferencing can be hidden anywhere. For
 * instance, a[i][2] can be:
 *
 *  - a 2-D array element,
 *
 *  - a[i]+2 if a[i] is a 1-D array of pointers,
 *
 *  - a.i[2], the second element of a 1-D array embedded as field i in struct a,
 *
 *  - a.i+2, if field i is a pointer embedded as field i in struct a,
 *
 *  - &a[i][2][0]... if a is an array of dimension 3 or more
 *
 * Remember that *p is equivalent and encoded as p[0].
 *
 * To guarantee store independence, either
 *
 * - the list of indices is empty, which covers abstract locations
 *    such as anywhere, null, etc.
 *
 * or
 *
 * - the list of indices is a list of integer constants and fields and
 *    none of the intermediate types that are still indexed are
 *    pointers unless a multidimensional array is used...
 *
 * Beware of named types...
 */
bool store_independent_points_to_reference_p(reference r)
{
  list il = reference_indices(r);
  bool independent_p = ENDP(il); // any variable is a constant address

  if(!independent_p) {
    if(!store_independent_points_to_indices_p(il))
      independent_p = false; // at least one index is store-dependent
    else {
      entity v = reference_variable(r);
      type t = entity_basic_concrete_type(v);
      if(type_functional_p(t))
	independent_p = true;
      else
	independent_p =
	  recursive_store_independent_points_to_reference_p(t, il);
    }
  }

  return independent_p;
}

/* check that the subscript list il is either empty or made of integers or
 * fields.
 */
bool constant_points_to_indices_p(list sl)
{
  bool constant_p = true;

  FOREACH(EXPRESSION, se, sl) {
    if(!extended_integer_constant_expression_p(se)) {
      syntax s = expression_syntax(se);
      if(syntax_reference_p(s)) {
	reference r = syntax_reference(s);
	entity f = reference_variable(r);
	if(!entity_field_p(f)) {
	  constant_p = false;
	  break;
	}
      }
      else {
	constant_p = false;
	break;
      }
    }
  }
  return constant_p;
}

/* check that the subscript list il is either empty or made of integers or
 * fields or unbounded entity "*".
 *
 * What would you do with a constant range ?
 */
bool store_independent_points_to_indices_p(list sl)
{
  bool constant_p = true;

  FOREACH(EXPRESSION, se, sl) {
    if(!extended_integer_constant_expression_p(se)) {
      syntax s = expression_syntax(se);
      if(syntax_reference_p(s)) {
	reference r = syntax_reference(s);
	entity f = reference_variable(r);
	if(!entity_field_p(f)) {
	  constant_p = false;
	  break;
	}
      }
      else if(syntax_call_p(s)) {
	call c = syntax_call(s);
	entity f = call_function(c);
	if(!unbounded_entity_p(f)) {
	  constant_p = false;
	  break;
	}
      }
      else {
	constant_p = false;
	break;
      }
    }
  }
  return constant_p;
}
