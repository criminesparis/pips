/*

  $Id: trace.c 23480 2018-08-22 07:33:48Z ancourt $

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
#include "local.h"
#include "transformations.h"

#define ADD_ELEMENT_TO_LIST( _list, _type, _element) \
    (_list = gen_nconc( _list, CONS( _type, _element, NIL)))

/* get vertex in a list by the vertex's label
 */
vertex get_vertex_in_list(list in_l, string in_s)
{
    MAP(VERTEX, ver, {
        string s = (string)vertex_vertex_label(ver);
	if (same_string_p(in_s, s)) return ver;
    }, in_l);
    return vertex_undefined;
}

/* print a graph to text format
 */
void prettyprint_graph_text(FILE * out_f, list l_of_vers)
{
  FOREACH (VERTEX, ver, l_of_vers) {
    FOREACH (SUCCESSOR, succ,  vertex_successors(ver)) {
      fputs((string) vertex_vertex_label (ver), out_f);
      fprintf(out_f, " ");
      fputs((string) vertex_vertex_label (successor_vertex(succ)), out_f);
      fprintf(out_f, " ");
      fputs((string) successor_arc_label (succ), out_f);
      fprintf(out_f, "\n");
    }
  }
}

/* print a graph to daVinci format, each label of successor is represented by 
 * a circular node, each vertex is represented by a square node
 */
void prettyprint_graph_daVinci(FILE * out_f, list l_of_vers) {
    /* To match the call to the free() at the end: */
    string gr_buffer = strdup(""); 
    bool first_node_parent = true;
    fprintf(out_f, "[\n");

    MAP(VERTEX, ver, {
        string node_name_parent = (string)vertex_vertex_label(ver);
	bool first_node_child = true;
	if (first_node_parent)
	    first_node_parent = false;
	else
	    fprintf(out_f, ",\n");
	fprintf(out_f,"l(\"%s\",n(\"\",[a(\"OBJECT\",\"%s\")],[\n", node_name_parent, node_name_parent); 

	MAP(SUCCESSOR, succ, {
	    string node_name_child = (string)vertex_vertex_label(successor_vertex(succ));
	    if (first_node_child)
	        first_node_child = false;
	    else
	        fprintf(out_f, ",\n");
	    if (strlen((string)successor_arc_label(succ)) == 0) {
	        fprintf(out_f, "  l(\"\",e(\"\",[],r(\"%s\")))", node_name_child);
	    } else {
	        string temp_buffer = strdup(concatenate(gr_buffer, ",\nl(\"", node_name_parent, "-", node_name_child, "\",n(\"\",[a(\"OBJECT\",\"", (string)successor_arc_label(succ), "\"),a(\"_GO\",\"ellipse\")],[\n  l(\"\",e(\"\",[],r(\"", node_name_child, "\")))]))", NULL));
		free(gr_buffer);
		gr_buffer = temp_buffer;
		fprintf(out_f, "  l(\"\",e(\"\",[],r(\"%s-%s\")))", node_name_parent, node_name_child);
	    } 
	}, vertex_successors(ver));
	fprintf(out_f, "]))");
    }, l_of_vers);

    fprintf(out_f, "%s", gr_buffer);
    fprintf(out_f, "\n]");
    free(gr_buffer);
}

list make_filtered_dg_or_dvdg(statement mod_stat, graph mod_graph)
{
    list verlist = NIL;
    list vars_ent_list = get_list_of_variable_to_filter();

    persistant_statement_to_int s_to_l = persistant_statement_to_int_undefined;
    int dl = -1;

    if (!statement_undefined_p(mod_stat)) {
        /* for computing the line numbers of statements */
        s_to_l = statement_to_line_number(mod_stat);
	dl = module_to_declaration_length(get_current_module_entity());
    }

    MAP(VERTEX, v1, {
        statement s1 = vertex_to_statement(v1);

	MAP(SUCCESSOR, su, {
	    vertex v2 = successor_vertex(su);
	    statement s2 = vertex_to_statement(v2);
	    dg_arc_label dal = (dg_arc_label) successor_arc_label(su);

	    MAP(CONFLICT, c, {
	        if (!statement_undefined_p(mod_stat)) {
		    entity conflict_var = reference_variable(effect_any_reference(conflict_source(c)));
		    if (gen_in_list_p(conflict_var, vars_ent_list) || vars_ent_list == NIL) {
		        string succ_label = (string)malloc(sizeof(string)*30);
			int l1 = dl + apply_persistant_statement_to_int(s_to_l, s1);
			int l2 = dl + apply_persistant_statement_to_int(s_to_l, s2);

			vertex vertex_parent = NULL;
			vertex vertex_child = NULL;
			char statement_action_parent = action_read_p(effect_action(conflict_source(c))) ? 'R' : 'W';
			char statement_action_child = action_read_p(effect_action(conflict_sink(c))) ? 'R' : 'W';
			string variable_name_parent = words_to_string(effect_words_reference(effect_any_reference(conflict_source(c))));
			string variable_name_child = words_to_string(effect_words_reference(effect_any_reference(conflict_sink(c))));
			string node_name_parent = (string)malloc(sizeof(string)*strlen(variable_name_parent) + 30);
			string node_name_child = (string)malloc(sizeof(string)*strlen(variable_name_child) + 30);

			successor succ = NULL;
			memset(node_name_parent, 0, sizeof(string)*strlen(variable_name_parent) + 30);
			memset(node_name_child, 0, sizeof(string)*strlen(variable_name_child) + 30);
			sprintf(node_name_parent, "%d-<%s>-%c", l1, variable_name_parent, statement_action_parent);
			sprintf(node_name_child, "%d-<%s>-%c", l2, variable_name_child, statement_action_child);

			/* Additional information for EDF prettyprint.
			   Instruction calls are given with  statement numbers
			*/
			if (get_bool_property("PRETTYPRINT_WITH_COMMON_NAMES")) {
			    if (instruction_call_p(statement_instruction(s1)))
			        sprintf(node_name_parent + strlen(node_name_parent), " %td-%s", statement_number(s1),
					entity_local_name(call_function(instruction_call(statement_instruction(s1)))));
			    else sprintf(node_name_parent + strlen(node_name_parent), " %td", statement_number(s1));
			    if (instruction_call_p(statement_instruction(s2)))
			        sprintf(node_name_child + strlen(node_name_child), " %td-%s", statement_number(s2),
					entity_local_name(call_function(instruction_call(statement_instruction(s2)))));
			    else sprintf(node_name_child + strlen(node_name_child), " %td", statement_number(s2));
			}

			memset(succ_label, 0, strlen(succ_label));
			if (conflict_cone(c) != cone_undefined) {
			    if (!statement_undefined_p(mod_stat)) {
			        strcat(succ_label, "levels(");
				MAPL(pl, {
				    sprintf(succ_label + strlen(succ_label),
					    pl == cone_levels(conflict_cone(c)) ? "%td" : ",%td", INT(CAR(pl)));
				}, cone_levels(conflict_cone(c)));
				strcat(succ_label, ")");
			    }
			}

			vertex_parent = get_vertex_in_list(verlist, node_name_parent);
			if (vertex_undefined_p(vertex_parent)) {
			    vertex_parent = make_vertex((vertex_label)node_name_parent, NIL);
			    ADD_ELEMENT_TO_LIST(verlist, VERTEX, vertex_parent);
			}

			vertex_child = get_vertex_in_list(verlist, node_name_child);
			if (vertex_undefined_p(vertex_child)) {
			    vertex_child = make_vertex((vertex_label)node_name_child, NIL);
			    ADD_ELEMENT_TO_LIST(verlist, VERTEX, vertex_child);
			}

			succ = make_successor((dg_arc_label)succ_label, vertex_child);
			ADD_ELEMENT_TO_LIST(vertex_successors(vertex_parent), SUCCESSOR, succ);
		    }
		}
	    }, dg_arc_label_conflicts(dal));

	}, vertex_successors(v1));

    }, graph_vertices(mod_graph));

    gen_free_list(vars_ent_list);

    if (!statement_undefined_p(mod_stat))
        free_persistant_statement_to_int(s_to_l);

    return verlist;
}

bool print_filtered_dg_or_dvdg(string mod_name, bool is_dv)
{
    string dg_name = NULL;
    string local_dg_name = NULL;
    FILE *fp;
    graph dg;
    statement mod_stat;
    list flt_graph;

    set_current_module_entity(local_name_to_top_level_entity(mod_name));
    set_current_module_statement( (statement)
	db_get_memory_resource(DBR_CODE, mod_name, true) );
    mod_stat = get_current_module_statement();
    set_ordering_to_statement(mod_stat);
    
    dg = (graph) db_get_memory_resource(DBR_DG, mod_name, true);

    flt_graph = make_filtered_dg_or_dvdg(mod_stat, dg);

    local_dg_name = db_build_file_resource_name(DBR_DG, mod_name, is_dv ? ".dvdg" : ".dg");
    dg_name = strdup(concatenate(db_get_current_workspace_directory(), 
				 "/", local_dg_name, NULL));
    fp = safe_fopen(dg_name, "w");

    debug_on("RICEDG_DEBUG_LEVEL");

    if (is_dv) {
        prettyprint_graph_daVinci(fp, flt_graph);
    } else {
        prettyprint_graph_text(fp, flt_graph);
    }

    debug_off();
    
    safe_fclose(fp, dg_name);
    free(dg_name);
    
    DB_PUT_FILE_RESOURCE(is_dv ? DBR_DVDG_FILE : DBR_DG_FILE, strdup(mod_name), local_dg_name);

    gen_free_list(flt_graph);
    
    reset_current_module_statement();
    reset_current_module_entity();
    reset_ordering_to_statement();

    return true;
}

static bool statement_in_loopnest_p = false;
static statement test_statement_of_reference;
static void statement_in_loopnest(statement s)
{
  if (statement_number(test_statement_of_reference) == statement_number(s))
    statement_in_loopnest_p= true;
}

static void print_cone_vecteur(FILE * fd,Pvecteur v, Ptsg gs, int type)
{
  Pbase b=gs->base;
  Pvecteur coord;
  if(vect_in_basis_p(v, b)) {
    fprintf(fd, (type==1) ? "Vertex":"Ray"); 
    for(coord = b; !VECTEUR_NUL_P(coord) ; coord = coord->succ) {
      fprint_string_Value(fd, " \t",vect_coeff(vecteur_var(coord), v));
    }
    fprintf(fd, " \n"); 
  }
}


extern entity selected_label;

bool print_loopnest_dependence_cone(const char* module_name)
{
  statement mod_stat;
  graph dg = (graph) db_get_memory_resource(DBR_DG, module_name, true);
  FILE *fp;
  string dc_name,local_dc_name;
  statement loopnest_st;
  bool first=true;
  set_current_module_entity(local_name_to_top_level_entity(module_name));
  set_current_module_statement( (statement)
				db_get_memory_resource(DBR_CODE, module_name, true) );
  mod_stat = get_current_module_statement();
  set_ordering_to_statement(mod_stat);
  local_dc_name = db_build_file_resource_name(DBR_DC_FILE, module_name,  ".dc");
  dc_name = strdup(concatenate(db_get_current_workspace_directory(), "/", local_dc_name, NULL));
  fp = safe_fopen(dc_name, "w");

  debug_on("RICEDG_DEBUG_LEVEL");
  
  /* Get the loop label from the user */
  const char* lp_label = get_string_property("LOOP_LABEL");
  if( string_undefined_p( lp_label))
    pips_user_warning("No loop label", "Please precise the loop label\n");
   
  if(lp_label)
    {
      selected_label = find_label_entity(module_name, lp_label);
      if (entity_undefined_p(selected_label)) {
	pips_user_warning("loop label does not exist\n", "Please give a valid label (%s not valid)\n",lp_label);
      }
    }
  if (!entity_undefined_p(selected_label)) {
    fprintf(fp,"Label: %s ",lp_label);
    loopnest_st=find_loop_from_label(mod_stat, selected_label);    
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
		Ptsg gs = (Ptsg) cone_generating_system(conflict_cone(c));
		if( !SG_UNDEFINED_P(gs)) {
		  if (first) {
		    fprintf(fp,"- Dependence Cone Basis :");
		    base_fprint(fp,gs->base , (get_variable_name_t) safe_entity_name);
		    first=false;
		  }
		  if( sg_nbre_rayons(gs) > 0) {
		    for (Pray_dte e = sg_rayons(gs); e != NULL; e = e->succ) {
		      print_cone_vecteur(fp,e->vecteur, gs,2);
		    }
		  }
		  if( sg_nbre_droites(gs) > 0) {
		    for (Pray_dte e = sg_droites(gs); e != NULL; e = e->succ) {
		      Pvecteur v=vect_copy(e->vecteur);
		      print_cone_vecteur(fp,e->vecteur, gs,2);
		      vect_chg_sgn(v);
		      print_cone_vecteur(fp,e->vecteur, gs,2);
		      vect_rm(v);
		    }
		  }
		  if(  sg_nbre_sommets(gs) > 0) {
		    for (Psommet e = sg_sommets(gs); e != NULL; e = e->succ) {
		      print_cone_vecteur(fp,e->vecteur, gs,1);
		    }
		  }
		}
	      }
	    }
	  }
	}
      }
    }
    if (first) fprintf(fp,"- No Dependencies");
  }
 
  debug_off();
    
  safe_fclose(fp, dc_name);
  free(dc_name);
    
  DB_PUT_FILE_RESOURCE( DBR_DC_FILE, strdup(module_name), local_dc_name);

  reset_current_module_statement();
  reset_current_module_entity();
  reset_ordering_to_statement();

  return true;
}







































