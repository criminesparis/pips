/*

  $Id: pypips.c 23519 2019-07-01 11:26:08Z coelho $

  Copyright 1989-2016 MINES ParisTech
  Copyright 2009-2010 TÉLÉCOM Bretagne
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

// nope! ???
#ifdef NDEBUG
#undef NDEBUG
#endif // NDEBUG

#include <unistd.h> // getcwd
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdarg.h>

/* hmmm... when all header files are not yet generated cproto may silently
 * fail to generate these headers.
 * this few declarations allow to generate headers without anything else.
 */
#ifdef CPROTO_IS_PROTOTYPING

typedef char * string;
typedef void * list;
typedef enum { false, true } bool;

#define list_undefined 0
#define DEFINE_LOCAL_STACK(a, b) /* nope */

#else // no CPROTO, real includes

#include "linear.h"
#include "genC.h"

#include "ri.h"
#include "database.h"

#include "misc.h"

#include "ri-util.h" /* ri needed for statement_mapping in pipsdbm... */
#include "pipsdbm.h"
#include "resources.h"
#include "phases.h"
#include "properties.h"
#include "pipsmake.h"
#include "text-util.h" // for words_to_string

#include "top-level.h"

// from "transformations/util.c":
statement find_loop_from_label(statement, entity);

#endif // CPROTO_IS_PROTOTYPING

/********************************************************************** LOGS */

static FILE * logstream = NULL;
static list log_list = list_undefined;

static void pyps_log_handler(const char *fmt, va_list *args)
{
  va_list args_copy;

  // avoid a repeat as pips_log_display called by pips_log_alist
  // already sent it to stderr
  if (logstream != stderr)
  {
    va_copy (args_copy, *args);
    vfprintf(logstream, fmt, args_copy);
    va_end(args_copy);
    fflush(logstream);
  }

  if (!list_undefined_p(log_list))
  {
    char* tmp;
    va_copy (args_copy, *args);
    vasprintf(&tmp, fmt, args_copy);
    va_end(args_copy);
    log_list = CONS(STRING,tmp,log_list);
  }
}

char * pyps_last_error = NULL;

static void pyps_error_handler(
  const char * calling_function_name,
  const char * a_message_format,
  va_list * args)
{
  // Save pre-existing error message
  char *old_error = pyps_last_error;

  char * tmp;
  va_list acpy;
  va_copy(acpy, *args);
  vasprintf(&tmp, a_message_format, acpy);
  va_end(acpy);

  asprintf(&pyps_last_error,"in %s: %s",calling_function_name,tmp);
  free(tmp);

  // If we already had a message before, we stack it over the new one
  if(old_error) {
    char *tmp = pyps_last_error;
    asprintf(&pyps_last_error,"%s%s",old_error,tmp);
    free(old_error);
    free(tmp);
  }
}

void close_log_buffer(void)
{
  if (!list_undefined_p(log_list))
  {
    gen_free_string_list(log_list);
    log_list = list_undefined;
  }
}

void open_log_buffer(void)
{
  if (!list_undefined_p(log_list))
    close_log_buffer();
  log_list = NIL;
}

char* get_log_buffer(void)
{
  assert(!list_undefined_p(log_list));
  list log_list_tmp=gen_copy_seq(log_list);
  log_list_tmp = gen_nreverse(log_list_tmp);
  char* ret = words_to_string(log_list_tmp);
  gen_free_list(log_list_tmp);
  return ret;
}

void verbose(bool on)
{
  if(on) logstream = stderr;
  else logstream = fopen("/dev/null","w");
}

/************************************************************ PROPERTY STACK */

/* stack of properties, so that the previous value can be reinstated
 * when going out of a phase.
 */
DEFINE_LOCAL_STACK(properties,property);

void set_property(const char* propname, const char* value)
{
  // thank's to rk, this hack is no longer needed
#if 0
  /* nice hack to temporarly redirect stderr */
  int saved_stderr = dup(STDERR_FILENO);
  char *buf;
  freopen("/dev/null","w",stderr);
  asprintf(&buf, "/dev/fd/%d", saved_stderr);
#endif
  if (!safe_set_property(propname, value)) {
#if 0
    freopen(buf,"w",stderr);
    free(buf);
#endif
    pips_user_error("error in setting property %s to %s\n",
                    propname, value);
  }
#if 0
  else {
    freopen(buf,"w",stderr);
    free(buf);
  }
#endif
}

void push_property(const char* name, const char * value)
{
  property p = copy_property(get_property(name,false));
  set_property(strdup(name),value);
  properties_push(p);
}

void pop_property(const char* name)
{
  property p = properties_pop();
  if(property_bool_p(p))
    set_bool_property(name,property_bool(p));
  else if(property_string_p(p))
    set_string_property(name,property_string(p));
  else
    set_int_property(name,property_int(p));
}

/******************************************************* PIPS INITIALIZATION */

void atinit(void)
{
  /* init various composants */
  // FIXME
  set_pips_meta_informations("<unknown>", "<unknown>", "<unknown>");

  initialize_newgen();
  initialize_sc((char*(*)(Variable))entity_local_name);
  pips_log_handler = pyps_log_handler;
  pips_error_handler = pyps_error_handler;
  set_exception_callbacks(push_pips_context, pop_pips_context);
  make_properties_stack();
}

/* create a new workspace...
 * FC: what about opening an existing one?
 */
void create(char* workspace_name, char ** filenames)
{
  if (workspace_exists_p(workspace_name))
    pips_user_error("Workspace %s already exists. Delete it!\n",
                    workspace_name);
  else if (db_get_current_workspace_name()) {
    pips_user_error("Close current workspace %s before "
                    "creating another one!\n",
                    db_get_current_workspace_name());
  }
  else
  {
    if (db_create_workspace(workspace_name))
    {
      // create the array of arguments
      gen_array_t filename_list = gen_array_make(0);
      while(*filenames)
      {
        gen_array_append(filename_list,*filenames);
        filenames++;
      }

      bool success = create_workspace(filename_list);

      gen_array_free(filename_list);

      if (!success)
      {
        db_close_workspace(false);
        pips_user_error("Could not create workspace %s\n", workspace_name);
      }
    }
    else {
      pips_user_error("Cannot create directory for workspace, "
                      "check rights!\n");
    }
  }
}

char* info(char * about)
{
  string sinfo = NULL;
  if (same_string_p(about, "workspace"))
  {
    sinfo = db_get_current_workspace_name();
    if (sinfo) sinfo = strdup(sinfo);
  }
  else if (same_string_p(about, "module"))
  {
        sinfo = db_get_current_module_name();
        if(sinfo) sinfo=strdup(sinfo);
  }
  else if (same_string_p(about, "modules") && db_get_current_workspace_name())
  {
    gen_array_t modules = db_get_module_list();
    int n = gen_array_nitems(modules), i;

    size_t sinfo_size=0;
    for(i=0; i<n; i++)
    {
      string m = gen_array_item(modules, i);
      sinfo_size+=strlen(m)+1;
    }
    sinfo = strdup(string_array_join(modules, " "));
    if(!sinfo)
      fprintf(stderr,"not enough memory to hold all module names\n");
    gen_array_full_free(modules);
  }
  else if (same_string_p(about, "directory"))
  {
    char pathname[MAXPATHLEN];
    sinfo = getcwd(pathname, MAXPATHLEN);
    if(sinfo)
      sinfo=strdup(sinfo);
    else
      fprintf(stderr,"failer to retreive current working directory\n");
  }

  if (!sinfo)
    sinfo = strdup("");
  return sinfo;
}

/* apply a transformation on a module
 */
void apply(char * phasename, char * target)
{
  if (!safe_apply(phasename,target)) {
    if(!pyps_last_error)
      asprintf(&pyps_last_error, "phase %s on module %s failed" ,
               phasename, target);
    THROW(user_exception_error);
  }
}

/* apply a transformation on a set of modules, concurrently
 */
void capply(char * phasename, char ** targets)
{
  // create the array of arguments
  gen_array_t target_list = gen_array_make(0);
  while (*targets)
  {
    gen_array_append(target_list,*targets);
    targets++;
  }
  bool ok = safe_concurrent_apply(phasename, target_list);
  gen_array_free(target_list);
  if(!ok) {
    if(!pyps_last_error)
      asprintf(&pyps_last_error,
               "capply phase %s failed without setting error message",
               phasename);
    THROW(user_exception_error);
  }
}

/* display resource rname about module mname
 */
void display(char *rname, char *mname)
{
  string old_current_module_name = db_get_current_module_name();
  if(old_current_module_name) {
    old_current_module_name = strdup(old_current_module_name);
    db_reset_current_module_name();
  }

  db_set_current_module_name(mname);
  string fname = build_view_file(rname);
  db_reset_current_module_name();
  if(old_current_module_name) {
    db_set_current_module_name(old_current_module_name);
    free(old_current_module_name);
  }

  if (!fname)
  {
    pips_user_error("Cannot build view file %s\n", rname);
    return;
  }

  safe_display(fname);
  free(fname);
  return;
}

/* return the rname[mname] resource,
 * which must be a string containing a file name
 */
char* show(char * rname, char *mname)
{
  if (!db_resource_p(rname, mname)) {
    pips_user_warning("no resource %s[%s].\n", rname, mname);
    return  strdup("");
  }

  // ensure that it is a filename, hence a string
  if (!displayable_file_p(rname)) {
    pips_user_warning("resource %s cannot be displayed.\n", rname);
    return strdup("");
  }

  // now returns the name of the file.
  return strdup(db_get_memory_resource(rname, mname, true));
}

/* Returns the list of the modules that call that specific module,
 * separated by ' '.
 */
char * get_callers_of(char * module_name)
{
  safe_make("CALLERS", module_name);
  gen_array_t callers = get_callers(module_name);
  char * callers_string = strdup(string_array_join(callers, " "));
  gen_array_free(callers);
  return callers_string;
}

/* Returns the list of the modules called by that specific module,
 * separated by ' '.
 */
char * get_callees_of(char * module_name)
{
  safe_make("CALLERS",module_name);
  gen_array_t callees = get_callees(module_name);

  char * callees_string = strdup(string_array_join(callees, " "));

  gen_array_free(callees);

  return callees_string;
}

/* Returns the list of the modules called by that specific module,
 * separated by ' '.
 */
char * pyps_get_stubs(void)
{
  gen_array_t stubs = get_stubs();
  char * stubs_string = strdup(string_array_join(stubs, " "));
  gen_array_free(stubs);
  return stubs_string;
}

/* add an environment variable of a given value
 */
void setenviron(char *name, char *value)
{
  setenv(name, value, 1);
}

/* get environment variable
 */
char* getenviron(char *name)
{
  return getenv(name);
}


/* Add a source file to the workspace
 * We wrap process_user_file() here with a hack
 * to define the workspace language so that some
 * pipsmake activate specific to the language
 * will be defined.
 * This function will be removed when pipsmake
 * will be improved to handle multilanguage workspace !
 */
bool add_a_file( string file )
{
  gen_array_t filename_list = gen_array_make(0);
  gen_array_append(filename_list,file);
  language workspace_language(gen_array_t files);
  language l = workspace_language(filename_list);
  activate_language(l);
  free_language(l);
  gen_array_free(filename_list);
  bool process_user_file(string file);
  if(process_user_file(file)==false) {
    pips_user_error("Error adding new file.");
    return false;
  }
  return true;
}


/*
 * Retrieve the language (string form) for a module
 */
char *get_module_language( string mod_name )
{
  language l = module_language(module_name_to_entity(mod_name));

  switch(language_tag(l)) {
    case is_language_fortran: return "fortran";
    case is_language_fortran95: return "fortran95";
    case is_language_c: return "c";
    default: return "unknown";
  }
}


// Broker registering python callback to C

#include <Python.h>


// Store the python object that will provide stub for missing module on the fly
static PyObject *stub_broker = NULL;

/*
 * This is the callback interface for PIPS missing module to python
 * It'll be called by pips to retrieve a file name when a module wasn't found
 * by PIPS.
 * The string is allocated and should be freed by the caller.
 */
static string get_stub_from_broker(string str)
{
  string result = NULL;

  // Assert that a broker is defined !
  if (stub_broker) {

    // Get the stub file (implemented in a python method...)
    PyObject *pyStubFile =
      PyEval_CallMethod(stub_broker, "stub_file_for_module", "(s)", str);

    // Sanity check
    if(pyStubFile) {
      // Convert to a regular C string
#if PY_MAJOR_VERSION >= 3
      result = strdup(PyUnicode_AsUTF8(pyStubFile));
#else // PYTHON 2
      result = strdup(PyString_AsString(pyStubFile));
#endif
      Py_XDECREF(pyStubFile);
    } else {
      // NULL is returned, error managed by the caller
      fprintf(stderr,"Callback failed !\n");
      PyErr_Print();
    }
  }
  // else NULL...

  return result;
}


/*
 *  Register the workspace (or any other object) as a resolver for missing
 *  modules. Method "stub_file_for_module" will be called and have to be defined
 */
void set_python_missing_module_resolver_handler(PyObject *PyObj)
{
  Py_XDECREF(stub_broker);          /* Dispose of previous callback */
  stub_broker = PyObj;         /* Remember new callback */
  Py_XINCREF(stub_broker);          /* Record of new callback */

  void set_internal_missing_module_resolver_handler(string (*)(string));
  set_internal_missing_module_resolver_handler(get_stub_from_broker);
}

/* Read execution mode for a loop */
bool get_loop_execution_parallel(
  const char* module_name,
  const char* loop_label)
{
  // prelude
  set_current_module_entity(module_name_to_entity( module_name ));
  set_current_module_statement
    ((statement) db_get_memory_resource(DBR_CODE, module_name, true) );

  entity label = find_label_entity(module_name,loop_label);
  if(entity_undefined_p(label))
    pips_user_error("label '%s' does not exist\n",loop_label);
  statement stmt = find_loop_from_label(get_current_module_statement(),label);
  if(statement_undefined_p(stmt))
    pips_user_error("label '%s' is not on a loop\n",loop_label);
  bool is_exec_parallel_p =
    execution_parallel_p(loop_execution(statement_loop(stmt)));

  // reset current state
  reset_current_module_entity();
  reset_current_module_statement();
  return is_exec_parallel_p;
}

/* Change execution mode for a loop */
void set_loop_execution_parallel(
  const char* module_name,
  const char* loop_label,
  bool exec_parallel_p)
{
  // prelude
  set_current_module_entity(module_name_to_entity( module_name ));
  set_current_module_statement
    ((statement) db_get_memory_resource(DBR_CODE, module_name, true) );

  entity label = find_label_entity(module_name,loop_label);
  if(entity_undefined_p(label))
    pips_user_error("label '%s' does not exist\n",loop_label);
  statement stmt = find_loop_from_label(get_current_module_statement(),label);
  if(statement_undefined_p(stmt))
    pips_user_error("label '%s' is not on a loop\n",loop_label);
  execution_tag(loop_execution(statement_loop(stmt)))
      = (exec_parallel_p ? is_execution_parallel : is_execution_sequential);

  // Store the new code
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, module_name, get_current_module_statement());

  // reset current state
  reset_current_module_entity();
  reset_current_module_statement();
}
