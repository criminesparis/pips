Effects-utils library
---------------------

This library provides utility functions for the Newgen types declared
in effects.newgen. As of June 08, 2016, these types are:

action_kind = store:unit + environment:unit + type_declaration:unit ;
action = read:action_kind + write:action_kind ;
approximation = may:unit + must:unit + exact:unit ;
cell_interpretation = value_of:unit + address_of:unit ;
cell = reference + preference + gap ;
cell_relation = first:interpreted_cell x second:interpreted_cell x approximation x descriptor ;
cell_relations = list:cell_relation* ;
descriptor = convexunion:Psysteme* + convex:Psysteme + none:unit ;
effect = cell x action x approximation x descriptor ;
effects_classes = classes:effects* ;
effects = effects:effect* ;
entity_effects = entity->effects ;
gap = variable:entity x path_selectors ;
interpreted_cell = cell x cell_interpretation ;
path_selector = expression + recursive_selector ;
path_selectors = path_selector* ;
persistant_expression_to_effects = persistent expression->effects ;
recursive_selector = basis:path_selectors* x coefficient:expression ;
statement_cell_relations = persistent statement->cell_relations ;
statement_effects = persistent statement->effects ;

These types are used to implement various PIPS analyses:
 * proper and cumulated effects, atomic or convex, rw, in or out;
 * pointer_values (Beatrice Creusillet)
 * points-to (Amira Mensi)

These analyses require different lattices of abstract locations and
sets of those. The abstract locations are either entities, references
or cells. They can use either standard references

reference = variable:entity x indices:expression* ;

where indices are the subscript expressions of an array reference, or
as extended references where indices can be either subscript
expressions of struct fields to unify the handling of arrays and
structs. They can imply dereferencing as in p[i] where p is a pointer
and not an array.

The extended references can be called points_to_references and be used
by points_to_cells.

A store independent effect is a constant effect, probably called a
constant memory access path elsewhere.

abstract_location.c: to deal with heap and malloc; generates entities
                     for related abstract locations

anywhere_abstract_locations.c: defines entities related to abstract
                               location lattice (all, anywhere, malloc,
                               nowhere, null, heap, stack, static, dynamic..)

			       defines partial order between abstract
			       location entities, conflicts

cell_relations.c: generic relational operator

compare.c: comparison of references, cells, effect, pointer_value

conflicts.c: conflicts between effects, effect and variable, cells,
             points_to cells, cells lists, references, entities,
             effect and entity,

	     may or must conflicts

	     effect inclusion

effects.c: deals with effects and cells, and lists of effects;
           effects can be concrete or abstract (anywhere, nowhere, null);

	   You have different kinds of effects: io, std_file, heap, malloc...

	   deals with points_to_cells()

pointer_values.c: support for pointer value analysis by Beatrice Creusillet;

		  lattice entities for undefined and null pointer, 
		  
		  operators on pv lattice

points_to.c: support for the points_to analysis by Amira Mensi.

             manages points_to lists and points_to sets, and
             points_to cells, and points_to references

	     provides order operators on points_to cells, intersection

	     check atomicity of points_to references

prettyprint.c: prettyprint for references, points_to references and
               pointer values

type.c: detects fields and pointers hidden in references (?)

	deals with type of the different kinds of cells and expression

	check constant_path
