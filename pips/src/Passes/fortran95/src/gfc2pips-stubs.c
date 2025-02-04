/*

 $Id: gfc2pips-stubs.c 23176 2016-08-30 12:47:13Z coelho $

 Copyright 1989-2016 MINES ParisTech
 Copyright 2009-2010 HPC-Project

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

#include "gfc2pips-private.h"

#include "c_parser_private.h"
#include "misc.h"
#include "text-util.h"
#include <stdio.h>



/************************************
 * STUB FUNCTIONS
 * They are there to get rid of the whole spaghetti
 * that is PIPS libraries linking :-(
 */

#define _STUB_MSG_(severity,msg) \
  pips_debug(0,"@%s(%d) !%s! : %s \n",__FILE__,__LINE__,severity,msg);
#define STUB_ERROR_MSG(msg) { _STUB_MSG_("ERROR",msg); exit(1); }
#define STUB_WARNING_MSG(msg) _STUB_MSG_("WARNING",msg)
#define STUB_ERROR() STUB_ERROR_MSG("")
#define STUB_WARNING() STUB_WARNING_MSG("")

// Preprocessor
#include "preprocessor.h"

/*************************************************
 * PIPSDBM
 */

string db_get_memory_resource( const string rname,
                               const string oname,
                               bool pure ) {
  STUB_ERROR();
}

string db_get_meta_data_directory() {
  STUB_ERROR();
}

string db_get_directory_name_for_module( string name ) {
  STUB_WARNING();
  return string_undefined;
}

gen_array_t db_get_module_list( void ) {
  STUB_WARNING();
  gen_array_t a = gen_array_make( 0 );
  return a;
}

string db_get_current_workspace_directory( void ) {
  STUB_WARNING();
  return string_undefined;
}

bool db_resource_p( string rname, string oname ) {
  STUB_WARNING();
  return FALSE;
}

void db_put_or_update_memory_resource( string rname,
                                       string oname,
                                       void * p,
                                       bool update_is_ok ) {
  STUB_ERROR();
}

bool db_touch_resource(const char* rname, const char* oname)
{
  STUB_ERROR();
  return FALSE;
}

bool db_resource_required_or_available_p(const char* rname, const char* oname)
{
  STUB_ERROR();
  return FALSE;
}

string db_build_file_resource_name(const char* r, const char* o, const char* s)
{
  STUB_ERROR();
  return NULL;
}

/************************************************
 * C_Syntax
 */

void compilation_unit_parser(const char* module)
{
  STUB_ERROR();
}

void CParserError( char *msg ) {
  STUB_ERROR();
}

/***********************************************
 * Effects
 */
list expression_to_proper_effects( expression e ) {
  STUB_ERROR();
}

/***********************************************
 * Control
 */
bool clean_up_sequences( statement s ) {
  STUB_ERROR();
}

// FIXME Really unused ??
unstructured control_graph( statement st ) {
  STUB_ERROR();
}
void unspaghettify_statement( statement mod_stmt ) {
  STUB_ERROR();
}

statement hcfg(statement st){
  STUB_ERROR();
}
/***********************************************
 * STEP
 */
void load_global_directives( entity k ) {
  STUB_ERROR();
}
string directive_to_string( void *d, bool close ) {
  STUB_ERROR();
}

/**********************************************
 * BOOTSTRAP
 */
bool check_loop_range( range r, hash_table h ) {
  STUB_ERROR();
}

/**********************************************
 * PROPERTIES
 */
bool get_bool_property( const string name ) {
  if ( strcmp( "PRETTYPRINT_LISTS_WITH_SPACES", name ) == 0
      || strcmp( "PRETTYPRINT_REGENERATE_ALTERNATE_RETURNS", name ) == 0
      || strcmp( "PRETTYPRINT_C_CODE", name ) == 0
      || strcmp( "ABORT_ON_USER_ERROR", name ) == 0 ) {
    return true;
  }
  if ( strcmp( "NO_USER_WARNING", name ) == 0 ) {
    return false;
  }
  fprintf( stderr, "***** Property requested : %s ***** ", name );
  STUB_WARNING();
  return 0;
}
string get_string_property( const string name ) {
  fprintf( stderr, "***** Property requested : %s ***** ", name );
  STUB_ERROR();
}
int get_int_property( const string name ) {
  fprintf( stderr, "***** Property requested : %s ***** ", name );
  STUB_ERROR();
}
void set_bool_property( const string name, bool b ) {
  fprintf( stderr, "***** Property requested : %s ***** ", name );
  STUB_ERROR();
}
void set_string_property( const string name, string s ) {
  fprintf( stderr, "***** Property requested : %s ***** ", name );
  STUB_ERROR();
}
bool too_many_property_errors_pending_p(void) {
  STUB_WARNING_MSG("unimplemented in gfc2pips !");
}
bool properties_initialized_p(void) {
  STUB_WARNING_MSG("unimplemented in gfc2pips !");
  return true;
}


/*************************************************
 * PIPSMAKE
 */
bool active_phase_p(const char* phase)
{
  STUB_ERROR();
}

/********************************************************* PRETTYPRINT STUFF */

bool transformer_with_temporary_values_p(void * t) {
  return t != NULL;
}

void print_points_to(void * v) {
  STUB_ERROR();
}

void print_points_to_cell(void * v)
{
  STUB_ERROR();
}

void print_points_to_cells(void * v)
{
  STUB_ERROR();
}

void print_points_to_graph(void * v)
{
  STUB_ERROR();
}

void print_points_to_list(void * v)
{
  STUB_ERROR();
}

void print_points_to_relations(void * v)
{
  STUB_ERROR();
}

void print_transformer(void * v)
{
  STUB_ERROR();
}

void dump_transformer(void * v)
{
  STUB_ERROR();
}

void print_region(void * v)
{
  STUB_ERROR();
}

void print_effect(void * v)
{
  STUB_ERROR();
}

void print_effects(void * v)
{
  STUB_ERROR();
}
