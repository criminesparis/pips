/*

  $Id: locations.c$

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

/* package location. Francois Irigoin, 2016.
 *
 * File: locations.c
 *
 *
 * This file contains various functions to represent specific memory
 * locations, concrete locations, as entities in order to extend the
 * semantics analysis, which is based on scalar entities, for struct fields,
 * pointed struct fields and array elememts.
 *
 * Concrete locations are represented as constant memory access
 * paths. Those are store-independent references, i.e. references
 * based on a variable and several constant indices. An index can be
 * either an array index, a[5], or a structure field s.f represented
 * as s[2] if f is the second field. When struct and array
 * declarations are nested, the subscript list grows.
 *
 * Note that some apparently constant memory access paths such as
 * p[3], may hide a pointer dereferencing and not be
 * store-independent (i.e. not a constant memory access path).
 *
 * Note also that the internal array and struct names include scope
 * information and module information to be unique across a whole
 * program.
 *
 * So we have to allocate new constant entities to represent each
 * location. These entities belong to a specific module, but not to
 * its declarations. It is not clear at first which local name, which
 * module name (an entity name is the concatenation of its module and
 * local names), which type, which storage and which initial value
 * they should have. Their type should be the type of the scalar
 * accessed. The storage is unclear.
 *
 * To decide what a location entity should be, we first define a
 * number of constraints that should be met by the chosen
 * implementation.
 *
 * To perform the semantic analyses, we must be able:
 *
 * C1. to map a constant memory access path reference to a location
 * entity to reuse the semantics analyses; a possible unique local
 * identifier is the character string representing the constant memory
 * access path, maybe plus some scope information to avoid name
 * conflicts, maybe plus some prefix to check the entity kind as for
 * intermediate or old value entities; two equivalent constant memory
 * access paths, such as a[2] and a[4/2], must be linked to the same
 * location entity
 *
 * C2. to map a location entity to its user visible name, e.g. "s.f",
 * to derive and allocate value entities and to print out the results
 * in a readable form;
 *
 * C3. to link a location entity to a constant memory access path to
 * be able to check memory conflicts between aliased locations, for
 * instance, a[*] and a[5], or s.f and s; plus some scope information
 * to distinguish between a in a[*] and a in a[5] since the two a
 * might be declared in different scopes;
 *
 * C4. to import interprocedural information, including information
 * about global variables; so a location entity should be unique no
 * matter where it is needed; the same constant memory path, which is
 * always defined interprocedurally because variable entities have
 * unique names to exploit a multiscope interprocedural symbol table
 * without any renaming, should lead to the same location entity
 * whether it is processed in a global context, a caller or a callee
 * context;
 *
 * C5. to obtain the same location memory global name regardless of
 * the PIPS pass ordering;
 *
 * C6. to type them to decide if their values should be analyzed or
 * not (for instance, integer scalar variables might be the only
 * variables whose values are anayzed; but floating point values might
 * be sought too).
 *
 * To preserve PIPS intermediate representation internal consistency,
 * we must be able:
 *
 * C7. to hide location entities in all printouts, including the
 * symbol table;
 *
 * C8. to (re)perform the memory allocation of static and dynamic
 * variables in any module and not be impacted by location entities
 * (i.e. they are not variables).
 *
 * To minimize the new development necessary to introduce entity
 * location, we must be able:
 *
 * C9. to ignore them without adding new tests about entity kinds in
 * existing passes but the semantic analysis. Or to add a small number
 * of tests at a low level, e.g. library ri-util.
 *
 * C10. to avoid as much as possible modifications of the internal
 * representation delcared in ri.newgen.
 *
 * Location entities are based, by definition of a reference, on one
 * variable entity defined by the variable field, having a uniquely
 * defined name in the PIPS interprocedural symbol tables, and by a
 * list of constant subscripts, numerical or symbolic, by definition
 * of a constant memory access path.
 *
 * The definition of an entity implies the definition of its module
 * name, its local name, its type, its storage, its initial value and
 * its kind:
 *
 * tabulated entity = name:string x type x storage x initial:value x kind:int ;
 *
 * where kind is redundant with information carried by other fields
 * and only intended to accelerate PIPS procesing by replacing string
 * operations by a unique integer comparison. It would be better to
 * have an enum field to keep track of the different kind of entities.
 *
 * Location entities could be defined and managed in many different ways:
 *
 * 1. their module names could be either 1) the module name of their
 * base variable, 2) a special location module name for all locations
 * as is done for values (i.e. the same temporary, old or intermediate
 * value entity may represent differents values in different modules),
 * 3) a special location module name for each module.
 *
 * 2. their local names contain either 1) a prefix to identify the
 * entity as a location entity, or 2) no prefix as the prefix is no
 * longer necessary as entities have now a "kind" field that could be
 * used instead (but this would not be consistent with the past design
 * choices: names are discriminant and kinds are only used to speed up
 * the processing),
 *
 * 3. their local names could be either 1) unique within a module (as
 * usual in PIPS), or 2) unique at the interprocedural level.
 *
 * 4. their local names could be either 1) a unique artificial unique
 * number to disambiguate between different location entities within a
 * module or within the whole symbol table (this may be tricky wrt the
 * pass ordering constraint), 2) a uniquely defined name derived from
 * the base entity local name and the subscripts of the constant
 * memory path (e.g. a print out o the points-to reference), but this might ;
 *
 * 5. Type: it could be either an address, a pointer, or the type of
 * the value at the location. To be compatible with the semantic
 * analysis, the type of a location entity must be the type of the
 * value.
 *
 * 6. Initial value: there is no initial value since the location
 * entities are not declared... except when a data structure or an
 * array is statically initialized; this field could be used to link
 * the location entity to its constant access memory path; but the
 * meaning of initial value would be lost and its type would not match
 * the entity type; a mapping could carry the information, but each
 * module would require its own mapping; these mappings would then
 * have to be resources...
 *
 * 7. Storage some kind of RAM storage is currently expected for all
 * variables wose values at different control points are
 * analyzed. However, the location entities are aliased to some
 * components of programmer variables or memory areas. They should not
 * be taken into account to allocate variables in the different
 * areas. The aliasing information is supposed to be stored implicitly
 * in the offset field of the ram data structure:
 *
 * ram = function:entity x section:entity x offset:int x shared:entity* ;
 *
 * but the offset is currently an int. Additional information is
 * carried by the entities in the field shared. This was designed to
 * manage Fortran 77 static aliasing due to the EQUIVALENCE statement
 * and the multiple declarations of commons. To store the constant
 * memory access path reference, it is possible to redefine the offset
 * field, to add a new field in ram, e.g. virtual_offset or
 * internal_offset, or to add a new kind of storage in:
 *
 * storage = return:entity + ram + formal + rom:unit ;
 *
 * such as 
 *
 * storage = ... + cmap: reference
 * 
 * 8. If all the information needed is not stored in the location
 * entity and accessible thru the symbol table, additional hash tables
 * could be added. The consistency would have to be tackled globally,
 * as bit as if a new interprocedural symbol table had been added.
 *
 * 9. additional hash tables could be added to speed up information
 * access even it all the information is already stored in the symbol
 * table. The consistency would have to be maintained only at the module level.
 *
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
// #include "points_to_private.h"
#include "ri-util.h"
#include "c_syntax.h" // for scope_to_block_scope()
#include "prettyprint.h" // for debugging
#include "effects-util.h"
#include "text.h" // for text-util.h
#include "text-util.h" // for reference_to_string() ?
#include "misc.h" // for pips_internal_error()
// #include "properties.h"

/* The caller is assumed to have checked that cp is a normalized
 * constant memory access path: a[4/2] must have been reduced to a[2]
 */
static string constant_memory_access_path_to_location_name(reference cp)
{
  entity elhs = reference_variable(cp);
  /* Due to global variables and various dereferencing, the module
   * name is linked to the module name of elhs and not of the current
   * module.
   */
  //string module_name = get_current_module_name();
  string module_name = (string) entity_module_name(elhs);

  string cp_name =
      strdup(concatenate(
          module_name, MODULE_SEP_STRING,
          scope_to_block_scope(entity_name(elhs)),
          reference_to_string(cp),
          (char *) NULL));

  return cp_name;
}

/*
 * Location entity
 *
 * If location entities are reused across modules just like value
 * entities, they can be allocated in a specific package and not break
 * the consistency of the user module.
 *
 * But then call site processing has to be carefully programmed so as
 * not to use locations in both caller and callee frames at the same
 * time.
 *
 * It is easier to make them local to a specific module.
 *
 * Note that no entity is created most of the time. Simple scalar
 * references return the variable itself.
 */

entity make_location_entity(reference cp)
{
  entity elhs = reference_variable(cp);

  type t = points_to_reference_to_concrete_type(cp);
  // Evaluation the constant subscript expressions such as a[4/2]
  reference ncp = constant_reference_to_normalized_constant_reference(cp);
  string cp_name = constant_memory_access_path_to_location_name(ncp);

  // Do not make the same entity twice
  entity ecp = gen_find_entity(cp_name);
  if(entity_undefined_p(ecp)) {
    ecp = make_entity(
		      strdup(cp_name),
		      copy_type(t),
		      copy_storage(entity_storage(elhs)),
		      make_value_reference(ncp));

    /* Add the new entity to the module declarations */
    string mn = (string) entity_module_name(elhs);
    entity m = module_name_to_entity(mn);
    value val = entity_initial(m);
    if(value_code_p(val)) {
      code c = value_code(val);
      code_declarations(c) =
	CONS(ENTITY, ecp, code_declarations(c));
    }
    else
      pips_internal_error("Module entity \"%s\" is not a module.\n",
			  entity_name(m));
  }
  else {
    free_reference(ncp);
  }

  // FI: if this is useful to maintain the intermediate
  // representation, then the module owning ecp should be computed. It
  // does not have to be the current module.

  // AddEntityToCurrentModuleWithoutDeclaration(ecp);

  return ecp;
}

/* A constant memory access path may not be considered. An undefined
 * entity is returned and the caller must handle the issue.
 *
 * This occurs, for instance, in the semantics analysis when a wider
 * memory effect contain this constant path. E.g. an untyped anwyhere
 * effect.
 *
 * It also happens when the caller consider a[*] as a constant
 * reference. It is a constant set of references and no entity is
 * returned.
 */
entity constant_memory_access_path_to_location_entity(reference cp)
{
  entity ecp = entity_undefined;
  reference ncp = constant_reference_to_normalized_constant_reference(cp);
  if(!reference_undefined_p(ncp)) {
    string cp_name = constant_memory_access_path_to_location_name(ncp);
    free_reference(ncp);

    // find (or do not create) an entity for the constant path
    // The entity is supposed to have been created earlier explictly
    ecp = gen_find_entity(cp_name);
    if (entity_undefined_p(ecp)) {
      // pips_internal_error("location entity should have been created explictly during an initialization phase\n");
      ; // Let the caller deals with the problem
    }
    free(cp_name);
  }
  return ecp;
}

bool location_entity_p(entity le)
{
  bool location_p = false;
  if(!entity_undefined_p(le)) {
    value v = entity_initial(le);
    if(!value_undefined_p(v))
      location_p = value_reference_p(v);
  }
  return location_p;
}

bool location_entity_of_module_p(entity le, entity m)
{
  bool location_p = false;
  if(!entity_undefined_p(le)) {
    value v = entity_initial(le);
    if(!value_undefined_p(v))
      if(value_reference_p(v))
	// FI: could be checked with a pointer equality via the storage field
	location_p = strcmp(entity_module_name(le), entity_user_name(m))==0;
  }
  return location_p;
}

/* Expanded version of location_entity_of_module_p() */
bool array_location_entity_of_module_p(entity le, entity m)
{
  bool location_p = false;
  if(!entity_undefined_p(le)) {
    value v = entity_initial(le);
    if(!value_undefined_p(v))
      if(value_reference_p(v))
	// FI: could be checked with a pointer equality via the storage field
	if(strcmp(entity_module_name(le), entity_user_name(m))==0) {
	  reference r = value_reference(v);
	  entity a = reference_variable(r);
	  type t = entity_basic_concrete_type(a);
	  location_p = array_type_p(t); 
	}
  }
  return location_p;
}

/* m is supposed to be a module entity */
list module_to_analyzed_array_locations(entity m)
{
  list ll = NIL;
  value v = entity_initial(m);
  code c = value_code(v);
  list dl = code_declarations(c);

  FOREACH(ENTITY, e, dl) {
    if(array_location_entity_of_module_p(e, m))
      ll = CONS(ENTITY, e, ll);
  }
  return ll;
}
