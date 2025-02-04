/*

  $Id: area.c$

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
/* Pot-pourri of utilities for entities of kind "area"
 * 
 */
#include <stdio.h>
#include <string.h>

#include "genC.h"
#include "linear.h"

#include "misc.h"
#include "ri.h"

#include "ri-util.h"

/* functions for areas */

/* Four areas used to allocate variables which are not stored in a
   Fortran common. These areas are just like Fortran commons, but the
   dynamic area is the only non-static area according to Fortran
   standard. The heap and the stack area are used to deal with Fortran
   ANSI extensions and C, pointers and allocatable arrays, and
   adjustable arrays (VLA in C). The dynamic area is stack allocated
   by most compilers but could be statically allocated since the array
   sizes are known.

   Areas are declared for each module. These four global variables are
   managed by the Fortran and C parsers and used to allocate variables
   in the current module. Note that the C parser uses more areas at
   the same time to cope with global variables.
 */
entity DynamicArea = entity_undefined;
entity StaticArea = entity_undefined;
entity HeapArea = entity_undefined;
entity StackArea = entity_undefined;
entity AllocatableArea = entity_undefined;


bool allocatable_area_p(entity aire) {
  return same_string_p(module_local_name(aire), ALLOCATABLE_AREA_LOCAL_NAME);
}

bool dynamic_area_p(entity aire)
{
#ifndef NDEBUG
    bool result = same_string_p(module_local_name(aire), DYNAMIC_AREA_LOCAL_NAME);
    pips_assert("entity_kind is consistent", result == ( (entity_kind(aire) & ENTITY_DYNAMIC_AREA) == ENTITY_DYNAMIC_AREA));
#endif
  return entity_kind(aire) & ENTITY_DYNAMIC_AREA;
}

bool static_area_p(entity aire)
{
#ifndef NDEBUG
    bool result = same_string_p(module_local_name(aire), STATIC_AREA_LOCAL_NAME);
    pips_assert("entity_kind is consistent", result == ( (entity_kind(aire) & ENTITY_STATIC_AREA) == ENTITY_STATIC_AREA));
#endif
  return entity_kind(aire) & ENTITY_STATIC_AREA;
}

bool heap_area_p(entity aire)
{
#ifndef NDEBUG
    bool result = same_string_p(module_local_name(aire), HEAP_AREA_LOCAL_NAME);
    pips_assert("entity_kind is consistent", result == ( (entity_kind(aire) & ENTITY_HEAP_AREA) == ENTITY_HEAP_AREA));
#endif
  return entity_kind(aire) & ENTITY_HEAP_AREA;
}

bool formal_area_p(entity aire)
{
#ifndef NDEBUG
    bool result = same_string_p(module_local_name(aire), FORMAL_AREA_LOCAL_NAME);
    pips_assert("entity_kind is consistent", result == ( (entity_kind(aire) & ENTITY_FORMAL_AREA) == ENTITY_FORMAL_AREA));
#endif
  return entity_kind(aire) & ENTITY_FORMAL_AREA;
}

bool stack_area_p(entity aire)
{
#ifndef NDEBUG
    bool result = same_string_p(module_local_name(aire), STACK_AREA_LOCAL_NAME);
    pips_assert("entity_kind is consistent", result == ( (entity_kind(aire) & ENTITY_STACK_AREA) == ENTITY_STACK_AREA));
#endif
  return entity_kind(aire) & ENTITY_STACK_AREA;
}

bool pointer_dummy_targets_area_p(entity aire)
{
#ifndef NDEBUG
    bool result = same_string_p(module_local_name(aire), POINTER_DUMMY_TARGETS_AREA_LOCAL_NAME);
    pips_assert("entity_kind is consistent", result == ( (entity_kind(aire) & ENTITY_POINTER_DUMMY_TARGETS_AREA) == ENTITY_POINTER_DUMMY_TARGETS_AREA));
#endif
  return entity_kind(aire) & ENTITY_POINTER_DUMMY_TARGETS_AREA;
}



/* Returns the heap area "a" associated to module "f". Area "a" is always a
   defined entity.

   Assumes that f is defined, as well as its heap area.
*/
entity module_to_heap_area(entity f)
{
  entity a = FindEntity(entity_local_name(f), HEAP_AREA_LOCAL_NAME);

  pips_assert("The heap area is defined for module f.\n",
	      !entity_undefined_p(a));

  return a;
}

entity module_to_dynamic_area(entity f)
{
  entity a = FindEntity(entity_local_name(f), DYNAMIC_AREA_LOCAL_NAME);

  pips_assert("The dynamic area is defined for module f.\n",
	      !entity_undefined_p(a));

  return a;
}

bool entity_area_p(entity e)
{
  return !type_undefined_p(entity_type(e)) && type_area_p(entity_type(e));//static_area_p(e) || dynamic_area_p(e) || heap_area_p(e) || stack_area_p(e);
}

bool entity_special_area_p(entity e)
{
  return entity_area_p(e) &&
    ( static_area_p(e) || dynamic_area_p(e) || heap_area_p(e) || stack_area_p(e) || pointer_dummy_targets_area_p(e));
}

/*
 * This function computes the current offset of the area a passed as
 * argument. The memory footprint of the variable v is also computed
 * and then added to a's offset. The initial offset is returned to the
 * calling function.  The layout of the area is updated.
 *
 * The memory footprint cannot be computed for C and Fortran varying
 * length arrays (VLA). They are allocated in the StackArea. We could
 * check here that area a is not the StackArea and/or that a is the
 * StackArea if the memory footprint of v cannot be statically
 * computed.
 *
 * A similar function, CurrentOffsetOfArea(), is used by the Fortran parser.
 */
int current_offset_of_area(entity a /* area */,
			   entity v /* scalar or array variable */)
{
  int OldOffset;
  type ta = entity_type(a);
  area aa = type_area(ta);

  /* the local areas are StaticArea, DynamicArea, HeapArea, StackArea */
  OldOffset = area_size(aa);
  int s;
  if (!SizeOfArray(v, &s)) {
    /* Varying Length Arrays (VLA) in C or Fortran must be allocated
     * in the stack area, where offsets are not computed in the same
     * way.
     */
    pips_internal_error("Ill. arg.: VLA");
  }
  else {
    pips_assert("Offsets are not computed this way in stack areas.\n",
		!stack_area_p(a));
    area_size(aa) = OldOffset + s;
  }

  area_layout(aa) = gen_nconc(area_layout(aa), CONS(ENTITY, v, NIL));
  return OldOffset;
}

bool empty_static_area_p(entity e)
{
    if (!static_area_p(e)) return false;
    return ENDP(area_layout(type_area(entity_type(e))));
}

void print_common_layout(FILE * fd, entity c, bool debug_p)
{
  entity mod = get_current_module_entity();
  /* list members = area_layout(type_area(entity_type(c))); */
  /* list members = common_members_of_module(c, mod , true); */
  /* for debugging only */
  list members = common_members_of_module(c, mod , false);
  list equiv_members = NIL;

  (void) fprintf(fd,"\nLayout for common /%s/ of size %td:\n",
		 module_local_name(c), area_size(type_area(entity_type(c))));

  if(ENDP(members)) {
    pips_assert("An empty area has size 0", area_size(type_area(entity_type(c)))==0);
    (void) fprintf(fd, "\t* empty area *\n\n");
  }
  else {
    if(area_size(type_area(entity_type(c)))==0
       // The next condition cannot be tested outside of the Fortran parser
       // && (common_size_map == hash_table_undefined || common_to_size(c)==0)
       && !heap_area_p(c)
       && !stack_area_p(c)) {
      if(debug_p) {
	pips_user_warning("Non-empty area %s should have a final size greater than 0\n",
			  entity_module_name(c));
      }
      else {
	pips_internal_error("Non-empty area %s should have a size greater than 0",
			    entity_module_name(c));
      }
    }
    /* Look for variables declared in this common by *some* procedures
     * which declares it. The procedures involved depend on the ordering
     * of the parser steps by pipsmake and the user. Maybe, the list should
     * be filtered and restricted to the current module: YES!
     */
    FOREACH(ENTITY, m, members)
      {
	pips_assert("RAM storage",
		    storage_ram_p(entity_storage(m)));
	if(ram_function(storage_ram(entity_storage(m)))==mod) {
	  int s;

	  /* Consistency check between the area layout and the ram section */
	  if(ram_section(storage_ram(entity_storage(m)))!=c) {
	    pips_internal_error("Variable %s declared in area %s but allocated in area %s",
				entity_local_name(m), entity_module_name(c),
				entity_module_name(ram_section(storage_ram(entity_storage(m)))));
	  }

	  if(!SizeOfArray(m, &s)) {
	    if(ram_section(storage_ram(entity_storage(m)))==HeapArea
	       || ram_section(storage_ram(entity_storage(m)))==StackArea) {
	      s = -1;
	    }
	    else {
	      pips_user_warning("Varying size of array \"%s\"\n",
				entity_name(m));
	      // VLA are now supported by PIPS in the stack_area and the dynamic_area
	      pips_internal_error("Fortran standard prohibit varying size array\n");
	    }
	  }

	  (void) fprintf(fd,
			 "\tVariable %s,\toffset = %td,\tsize = %d\n", 
			 entity_name(m),
			 ram_offset(storage_ram(entity_storage(m))),
			 s);

	}
      }
    (void) fprintf(fd, "\n");

    /* Look for variables aliased with a variable in this common */
    FOREACH(ENTITY, m, members)
      {
	list equiv = ram_shared(storage_ram(entity_storage(m)));
	equiv_members = arguments_union(equiv_members, equiv);
      }

    if(!ENDP(equiv_members)){

      equiv_members = arguments_difference(equiv_members, members);
      if(!ENDP(equiv_members)) {
	sort_list_of_entities(equiv_members);

	(void) fprintf(fd, "\tVariables aliased to this common:\n");

	FOREACH(ENTITY, m, equiv_members)
	  {
	    pips_assert("RAM storage",
			storage_ram_p(entity_storage(m)));
	    (void) fprintf(fd,
			   "\tVariable %s,\toffset = %td,\tsize = %d\n", 
			   entity_name(m),
			   ram_offset(storage_ram(entity_storage(m))),
			   array_size(m));
	  }
	(void) fprintf(fd, "\n");
	gen_free_list(equiv_members);
      }
    }
  }
  gen_free_list(members);
}
