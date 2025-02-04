/*

  $Id$

  Copyright 1989-2017 MINES ParisTech

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


/**
 * Pass: MPI_CONVERSION
 * Debug mode: MPI_GENERATION_DEBUG_LEVEL
 * Properties used:
 *   - MPI_NBR_CLUSTER
 *   - MPI_DUPLICATE_VARIABLE_PREFIX
 * Resource needed:
 *   - DBR_TASK
 *
 */

#include <stdlib.h>
#include <stdio.h>

#include "genC.h"
#include "linear.h"

#include "resources.h"
#include "database.h"
#include "ri.h"
#include "ri-util.h"
#include "pipsdbm.h"

#include "control.h"

#include "misc.h"
#include "syntax.h"
#include "c_syntax.h"

#include "properties.h"

#include "task_parallelization.h"
#include "prettyprint.h"

static string mpi_conversion_declaration_commenter(__attribute__((unused)) entity e) {
  return strdup(COMMENT_MPI_CONVERSION);
}

/*******************************************************
 * GENERIC MPI FUNCTION MAKER : BEGIN                  *
 *******************************************************/
enum mpi_communication_mode {
  mpi_communication_default_mode,
  mpi_communication_synchronous_mode,
  mpi_communication_ready_mode,
  mpi_communication_buffered_mode
};

/**
 * Functions to generate standard MPI function statement
 * Can maybe also make function to return MPI function like instruction instead of statement to be more flexible?
 * Only C version are made, for Fortran version, have to add an error manager variable
 *   (instead return result in C than represent possible error, add it in call function, cf MPI doc)
 * All these functions can be general and move into a MPI manager?
 *   In that case only unstatic function that return statement or type
 */
/**
 * generate statement:
 * MPI_Comm_size(communicator, &size);
 * or
 * result = MPI_Comm_size(communicator, &size);
 */
static statement mpic_make_mpi_comm_size(entity communicator, entity size, entity result) {
  list args = NIL;
  args = CONS(EXPRESSION, make_entity_expression(communicator, NIL), args);
  args = CONS(EXPRESSION, make_address_of_expression(make_entity_expression(size, NIL)), args);
  args = gen_nreverse(args);
  entity called_function = entity_intrinsic(MPI_COMM_SIZE_FUNCTION_NAME);
  call mpi_call = make_call(called_function, args);
  statement mpi_st = statement_undefined;
  if (entity_undefined_p(result)) {
    mpi_st = call_to_statement(mpi_call);
  }
  else {
    mpi_st = make_assign_statement(entity_to_expression(result), call_to_expression(mpi_call));
  }
  return mpi_st;
}

/**
 * generate statement:
 * MPI_Comm_rank(communicator, &rank);
 * or
 * result = MPI_Comm_rank(communicator, &rank);
 */
static statement mpic_make_mpi_comm_rank(entity communicator, entity rank, entity result) {
  list args = NIL;
  args = CONS(EXPRESSION, make_entity_expression(communicator, NIL), args);
  args = CONS(EXPRESSION, make_address_of_expression(make_entity_expression(rank, NIL)), args);
  args = gen_nreverse(args);
  entity called_function = entity_intrinsic(MPI_COMM_RANK_FUNCTION_NAME);
  call mpi_call = make_call(called_function, args);
  statement mpi_st = statement_undefined;
  if (entity_undefined_p(result)) {
    mpi_st = call_to_statement(mpi_call);
  }
  else {
    mpi_st = make_assign_statement(entity_to_expression(result), call_to_expression(mpi_call));
  }
  return mpi_st;
}

/**
 * argc and argv must be defined
 * generate statement:
 * MPI_Init(&argc, &argv);
 * or
 * result = MPI_Init(&argc, &argv);
 */
static statement mpic_make_mpi_init(entity result, entity argc, entity argv) {
  list args = NIL;
  if (argc == NULL || entity_undefined_p(argc) || entity_undefined_p(argv)) {
    pips_user_error("argc and argv must be defined\n");
    return statement_undefined;
  }
  args = CONS(EXPRESSION, make_address_of_expression(make_entity_expression(argc, NIL)), args);
  args = CONS(EXPRESSION, make_address_of_expression(make_entity_expression(argv, NIL)), args);
  args = gen_nreverse(args);
  entity called_function = entity_intrinsic(MPI_INIT_FUNCTION_NAME);
  call mpi_call = make_call(called_function, args);
  statement mpi_st = statement_undefined;
  if (entity_undefined_p(result)) {
    mpi_st = call_to_statement(mpi_call);
  }
  else {
    mpi_st = make_assign_statement(entity_to_expression(result), call_to_expression(mpi_call));
  }
  return mpi_st;
}

/**
 * generate statement:
 * MPI_Finalize();
 * or
 * result = MPI_Finalize();
 */
static statement mpic_make_mpi_finalize(entity result) {
  list args = NIL;
  args = gen_nreverse(args);
  entity called_function = entity_intrinsic(MPI_FINALIZE_FUNCTION_NAME);
  call mpi_call = make_call(called_function, args);
  statement mpi_st = statement_undefined;
  if (entity_undefined_p(result)) {
    mpi_st = call_to_statement(mpi_call);
  }
  else {
    mpi_st = make_assign_statement(entity_to_expression(result), call_to_expression(mpi_call));
  }
  return mpi_st;
}

/*static statement mpifortran_make_mpi_finalize(entity result) {
  list args = CONS(EXPRESSION, make_entity_expression(result, NIL), NIL);
  args = gen_nreverse(args);
  statement mpi_st = make_call_statement(MPI_FINALIZE_FUNCTION_NAME, args, entity_undefined, string_undefined);
  return mpi_st;
}
*/
/**
 * make a list of expression that will be use as argument for MPI send/receive functions
 * ds is the destination or the source depend of a send or receive function
 * (&buffer, size, mpitype, ds, tag, communicator{, status/request})
 */
static list mpic_make_args_mpi_send_or_receiv(
    expression buffer,
    int size,
    entity mpitype,
    int ds,
    int tag,
    entity communicator,
    entity status,
    entity request)
{
  list args = NIL;

  args = CONS(EXPRESSION, make_address_of_expression(buffer), args);
  args = CONS(EXPRESSION, int_to_expression(size), args);

  pips_assert("mpitype must defined.\n", !entity_undefined_p(mpitype));
  args = CONS(EXPRESSION, make_entity_expression(mpitype, NIL), args);

//  basic bas = variable_basic(type_variable(entity_type(expression_to_entity(buffer))));
//  switch(basic_tag(bas)){
//  case is_basic_int:
//    //don't know what to put for size (so 100 for the moment...)
//    args = CONS(EXPRESSION, make_entity_expression(make_constant_entity("MPI_INT", is_basic_string, 100), NIL), args);
//    break;
//  case is_basic_float:
//    //don't know what to put for size (so 100 for the moment...)
//    args = CONS(EXPRESSION, make_entity_expression(make_constant_entity("MPI_FLOAT", is_basic_string, 100), NIL), args);
//    break;
//  default:
//    pips_user_warning("type %s not handled yet in MPI\n", basic_to_string(bas));
//    break;
//  }

  args = CONS(EXPRESSION, int_to_expression(ds), args);
  args = CONS(EXPRESSION, int_to_expression(tag), args);

  args = CONS(EXPRESSION, make_entity_expression(communicator, NIL), args);

  if (!entity_undefined_p(status) && !entity_undefined_p(request)) {
    pips_internal_error("MPI_Status and MPI_Request can't be use at the same time\n"
        "  use MPI_status for blocking function\n"
        "  use MPI_Request for non-blocking function\n");
  }
  else if (!entity_undefined_p(request)) {
    args = CONS(EXPRESSION, make_address_of_expression(make_entity_expression(request, NIL)), args);
  }
  else if (!entity_undefined_p(status)) {
    args = CONS(EXPRESSION, make_address_of_expression(make_entity_expression(status, NIL)), args);
  }

  args = gen_nreverse(args);
  return args;
}

static call mpic_make_generic_mpi_send_call(
    expression buffer,
    int size,
    entity mpitype,
    int dest,
    int tag,
    entity communicator,
    entity request,
    //bool blocking,                    //this information is contained inside request, if (request==entity_undefied) then blocking==true else blocking==false
    enum mpi_communication_mode mode)
{
  list args = mpic_make_args_mpi_send_or_receiv(buffer, size, mpitype, dest, tag, communicator, entity_undefined, request);

  entity called_function = entity_undefined;
  switch (mode) {
  case mpi_communication_synchronous_mode:
    if (entity_undefined_p(request))
      called_function = entity_intrinsic(MPI_SSEND_FUNCTION_NAME);
    else
      called_function = entity_intrinsic(MPI_ISSEND_FUNCTION_NAME);
    break;
  case mpi_communication_ready_mode:
    if (entity_undefined_p(request))
      called_function = entity_intrinsic(MPI_RSEND_FUNCTION_NAME);
    else
      called_function = entity_intrinsic(MPI_IRSEND_FUNCTION_NAME);
    break;
  case mpi_communication_buffered_mode:
    if (entity_undefined_p(request))
      called_function = entity_intrinsic(MPI_BSEND_FUNCTION_NAME);
    else
      called_function = entity_intrinsic(MPI_IBSEND_FUNCTION_NAME);
    break;
  case mpi_communication_default_mode:
  default:
    if (entity_undefined_p(request))
      called_function = entity_intrinsic(MPI_SEND_FUNCTION_NAME);
    else
      called_function = entity_intrinsic(MPI_ISEND_FUNCTION_NAME);
    break;
  }

  call mpi_call = make_call(called_function, args);
  return mpi_call;
}

static call mpic_make_generic_mpi_receive_call(
    expression buffer,
    int size,
    entity mpitype,
    int dest,
    int tag,
    entity communicator,
    entity status,
    entity request
    //bool blocking,                    //this information is contained inside request, if (request==entity_undefied) then blocking==true else blocking==false
)
{
  if (!entity_undefined_p(status) && !entity_undefined_p(request))
    pips_internal_error("MPI_Status and MPI_Request can't be use at the same time for MPI_Recv/MPI_Irecv instruction\n"
        "  use MPI_status for blocking receive (MPI_Recv)\n"
        "  use MPI_Request for non-blocking receive (MPI_Irecv)\n");
  else if (entity_undefined_p(status) && entity_undefined_p(request))
    pips_internal_error("MPI_Status xor MPI_Request must be use present for MPI_Recv/MPI_Irecv instruction\n"
        "  use MPI_status for blocking receive (MPI_Recv)\n"
        "  use MPI_Request for non-blocking receive (MPI_Irecv)\n");

  list args = mpic_make_args_mpi_send_or_receiv(buffer, size, mpitype, dest, tag, communicator, status, request);

  entity called_function = entity_undefined;
  if (entity_undefined_p(request))
    called_function = entity_intrinsic(MPI_RECV_FUNCTION_NAME);
  else
    called_function = entity_intrinsic(MPI_IRECV_FUNCTION_NAME);

  call mpi_call = make_call(called_function, args);
  return mpi_call;
}

/**
 * generate statement:
 * {result =} MPI_Send(&buffer, size, mpitype, dest, tag, communicator);
 */
static statement mpic_make_mpi_send(
    expression buffer,
    int size,
    entity mpitype,
    int dest,
    int tag,
    entity communicator,
    entity result)
{
  call mpi_call = mpic_make_generic_mpi_send_call(buffer, size, mpitype, dest, tag, communicator, entity_undefined, mpi_communication_default_mode);
  statement mpi_st = statement_undefined;
  if (entity_undefined_p(result)) {
    mpi_st = call_to_statement(mpi_call);
  }
  else {
    mpi_st = make_assign_statement(entity_to_expression(result), call_to_expression(mpi_call));
  }
  return mpi_st;
}
/**
 * generate statement:
 * {result =} MPI_Isend(&buffer, size, mpitype, dest, tag, communicator, &request);
 */
static statement mpic_make_mpi_isend(
    expression buffer,
    int size,
    entity mpitype,
    int dest,
    int tag,
    entity communicator,
    entity request,
    entity result)
{
  call mpi_call = mpic_make_generic_mpi_send_call(buffer, size, mpitype, dest, tag, communicator, request, mpi_communication_default_mode);
  statement mpi_st = statement_undefined;
  if (entity_undefined_p(result)) {
    mpi_st = call_to_statement(mpi_call);
  }
  else {
    mpi_st = make_assign_statement(entity_to_expression(result), call_to_expression(mpi_call));
  }
  return mpi_st;
}
/**
 * TODO do the same for MPI_Rsend/Irsend/Bsend/Ibsend/Ssend/Issend
 */

/**
 * generate statement:
 * {result =} MPI_Recv(&buffer, size, mpitype, source, tag, communicator, &status);
 */
static statement mpic_make_mpi_recv(
    expression buffer,
    int size,
    entity mpitype,
    int source,
    int tag,
    entity communicator,
    entity status,
    entity result)
{
  call mpi_call = mpic_make_generic_mpi_receive_call(buffer, size, mpitype, source, tag, communicator, status, entity_undefined);
  statement mpi_st = statement_undefined;
  if (entity_undefined_p(result)) {
    mpi_st = call_to_statement(mpi_call);
  }
  else {
    mpi_st = make_assign_statement(entity_to_expression(result), call_to_expression(mpi_call));
  }
  return mpi_st;
}
/**
 * generate statement:
 * {result =} MPI_Irecv(&buffer, size, mpitype, source, tag, communicator, &request);
 */
static statement mpic_make_mpi_irecv(
    expression buffer,
    int size,
    entity mpitype,
    int source,
    int tag,
    entity communicator,
    entity request,
    entity result)
{
  call mpi_call = mpic_make_generic_mpi_receive_call(buffer, size, mpitype, source, tag, communicator, entity_undefined, request);
  statement mpi_st = statement_undefined;
  if (entity_undefined_p(result)) {
    mpi_st = call_to_statement(mpi_call);
  }
  else {
    mpi_st = make_assign_statement(entity_to_expression(result), call_to_expression(mpi_call));
  }
  return mpi_st;
}

/**
 * return the type for MPI communicator:
 * MPI_Comm
 */
static type mpi_type_mpi_comm() {
  entity comm = FindOrCreateEntity(TOP_LEVEL_MODULE_NAME, MPI_COMM);
  if(storage_undefined_p(entity_storage(comm))) {
    entity_storage(comm) = make_storage_rom();
    put_new_typedef(MPI_COMM);
  }
  type comm_t = MakeTypeVariable(make_basic_typedef(comm), NIL);
  if(type_undefined_p(entity_type(comm))) {
    entity_type(comm) = ImplicitType(comm);
  }
  return comm_t;
}

/**
 * return the type for MPI status:
 * MPI_Status
 */
static type mpi_type_mpi_status() {
  entity stat = FindOrCreateEntity(TOP_LEVEL_MODULE_NAME, MPI_STATUS);
  if(storage_undefined_p(entity_storage(stat))) {
    entity_storage(stat) = make_storage_rom();
    put_new_typedef(MPI_STATUS);
  }
  type stat_t = MakeTypeVariable(make_basic_typedef(stat), NIL);
  if(type_undefined_p(entity_type(stat))) {
    entity_type(stat) = ImplicitType(stat);
  }
  return stat_t;
}

/**
 * return the type for MPI request:
 * MPI_Request
 */
static type mpi_type_mpi_request() {
  entity req =   FindOrCreateEntity(TOP_LEVEL_MODULE_NAME, MPI_REQUEST);
  if(storage_undefined_p(entity_storage(req))) {
    entity_storage(req) = make_storage_rom();
    put_new_typedef(MPI_REQUEST);
  }
  type req_t =MakeTypeVariable(make_basic_typedef(req), NIL);
  if(type_undefined_p(entity_type(req))) {
    entity_type(req) = ImplicitType(req);
  }
  return req_t;
}

/**
 * return the type for MPI datatype (to make custom datatype for example):
 * MPI_Datatype
 */
//* Not use
/*static type mpi_type_MPI_Datatype() {
  entity req =   FindOrCreateEntity(TOP_LEVEL_MODULE_NAME, MPI_DATATYPE);
  if(storage_undefined_p(entity_storage(req)))
    {
      entity_storage(req) = make_storage_rom();
      put_new_typedef(MPI_DATATYPE);
    }
  type req_t =MakeTypeVariable(make_basic_typedef(req), NIL);
  if(type_undefined_p(entity_type(req))) {
    entity_type(req) = ImplicitType(req);
  }
  return req_t;
}
*/
//*/

/*******************************************************
 * GENERIC MPI FUNCTION MAKER : END                    *
 *******************************************************/


/*******************************************************
 * CONTEXT_MPI + MPI FUNCTION MAKER  : BEGIN           *
 *******************************************************/
/**
 * Wrapper to call generic MPI function maker
 */
typedef struct ctx_mpi {
  entity size;                          // total number of proc
  entity rank;                          // id of proc used
  entity mpi_communicator;              // mpi_communicator for communication
  entity mpi_status;                    // mpi_status of a synchronous receive
  entity mpi_request;                   // mpi_request for asynchronous communication
  entity error;                         // for error handling
} ctx_mpi_t;

static ctx_mpi_t mpi_make_ctx(entity module) {
  ctx_mpi_t ctx;
  ctx.size = make_new_scalar_variable_with_prefix("size", module, MakeBasic(is_basic_int));
  ctx.rank = make_new_scalar_variable_with_prefix("rank", module, MakeBasic(is_basic_int));

  ctx.mpi_communicator = FindOrCreateEntity(TOP_LEVEL_MODULE_NAME, MPI_COMM_WORLD_STRING);
  if (type_undefined_p(entity_type(ctx.mpi_communicator))) {
    entity_type(ctx.mpi_communicator) = mpi_type_mpi_comm();
  }
  if (storage_undefined_p(entity_storage(ctx.mpi_communicator))) {
    //FIXME global variable, what kind of storage?
    // It's certainly not the good storage here...
    const char* module_name = module_local_name(module);
    entity area = FindEntity(module_name, STACK_AREA_LOCAL_NAME);
    entity_storage(ctx.mpi_communicator) =
//        make_storage_rom();
        make_storage_ram(make_ram(module, area, 0/*CurrentOffsetOfArea(area, ctx.mpi_communicator)*/, NIL));
  }

  ctx.mpi_status = make_new_scalar_variable_with_prefix("status", module, MakeBasic(is_basic_int));
  entity_type(ctx.mpi_status) = mpi_type_mpi_status();

  ctx.mpi_request = make_new_scalar_variable_with_prefix("request", module, MakeBasic(is_basic_int));
  entity_type(ctx.mpi_request) = mpi_type_mpi_request();

  ctx.error = entity_undefined;
  return ctx;
}
static void mpi_free_ctx(__attribute__ ((__unused__)) ctx_mpi_t * ctx) {
  //Nothing to do
  return;
}

static statement mpi_comm_size_ctx(const ctx_mpi_t ctx) {
  return mpic_make_mpi_comm_size(ctx.mpi_communicator, ctx.size, ctx.error);
}

static statement mpi_comm_rank_ctx(const ctx_mpi_t ctx) {
  return mpic_make_mpi_comm_rank(ctx.mpi_communicator, ctx.rank, ctx.error);
}

static statement mpi_init_ctx(const ctx_mpi_t ctx) {
  entity argc = gen_find_tabulated("main:argc", entity_domain);
  entity argv = gen_find_tabulated("main:argv", entity_domain);
  return mpic_make_mpi_init(ctx.error, argc, argv);
}

static statement mpi_finalize_ctx(const ctx_mpi_t ctx) {
  return mpic_make_mpi_finalize(ctx.error);
}

static statement mpi_send_ctx(const ctx_mpi_t ctx, expression buffer, int size, int dest, int tag, bool blocking) {
  entity mpitype = entity_undefined;
  basic bas = variable_basic(type_variable(entity_type(expression_to_entity(buffer))));
  switch(basic_tag(bas)){
  case is_basic_int:
    //don't know what to put for size (so 100 for the moment...)
    mpitype = make_constant_entity("MPI_INT", is_basic_string, 100);
    break;
  case is_basic_float:
    //don't know what to put for size (so 100 for the moment...)
//    mpitype = make_constant_entity("MPI_FLOAT", is_basic_string, 100);
    mpitype = make_constant_entity("MPI_DOUBLE", is_basic_string, 100);
    break;
  default:
    pips_user_warning("type %s not handled yet in MPI\n", basic_to_string(bas));
    break;
  }

  if (!blocking)
    return mpic_make_mpi_isend(buffer, size, mpitype, dest, tag, ctx.mpi_communicator, ctx.mpi_request, ctx.error);
  else
    return mpic_make_mpi_send(buffer, size, mpitype, dest, tag, ctx.mpi_communicator, ctx.error);
}
/**
 * TODO do the same for Ssend, Rsend, Bsend
 */

static statement mpi_recv_ctx(const ctx_mpi_t ctx, expression buffer, int size, int source, int tag, bool blocking) {
  entity mpitype = entity_undefined;
  basic bas = variable_basic(type_variable(entity_type(expression_to_entity(buffer))));
  switch(basic_tag(bas)){
  case is_basic_int:
    //don't know what to put for size (so 100 for the moment...)
    mpitype = make_constant_entity("MPI_INT", is_basic_string, 100);
    break;
  case is_basic_float:
    //don't know what to put for size (so 100 for the moment...)
//    mpitype = make_constant_entity("MPI_FLOAT", is_basic_string, 100);
    mpitype = make_constant_entity("MPI_DOUBLE", is_basic_string, 100);
    break;
  default:
    pips_user_warning("type %s not handled yet in MPI\n", basic_to_string(bas));
    break;
  }

  if (blocking)
    return mpic_make_mpi_recv(buffer, size, mpitype, source, tag, ctx.mpi_communicator, ctx.mpi_status, ctx.error);
  else
    return mpic_make_mpi_irecv(buffer, size, mpitype, source, tag, ctx.mpi_communicator, ctx.mpi_request, ctx.error);
}

/*******************************************************
 * CONTEXT_MPI + MPI FUNCTION MAKER  : END             *
 *******************************************************/


/*******************************************************
 * CONTEXT MANAGEMENT : BEGIN                          *
 *******************************************************/

typedef struct ctx_conv {
  ctx_mpi_t ctx_mpi;
//  hash_table hash_statement_to_add;     //to memorize the global statements to add
//                                        //  (don't work with it but with hash_statement_receive)
//  hash_table hash_statement_receive;    //work on these statements
//  statement* statement_to_add;          //to memorize the global statements to add
//                                        //  (don't work with it but with statement_send_receive)
  //statement* statement_body;            //work on these statements
  statement* statement_send_receive;    //work on these statements
  statement statement_work_on;
  int nbr_cluster;
  int current_cluster;
  task current_task;
  //int last_cluster;                     //only to free useless stuff
  int** tag;                            //tag[sender][receiver]
  statement return_statement;
} ctx_conv_t;

static ctx_conv_t conv_make_ctx(entity module, int nbr_cluster) {
  pips_assert("number of cluster can't be equal to 0", nbr_cluster != 0);
  ctx_conv_t ctx;

  ctx.ctx_mpi = mpi_make_ctx(module);

//  ctx.hash_statement_to_add = hash_table_make(hash_int, nbr_cluster);
//  ctx.hash_statement_receive = hash_table_make(hash_int, nbr_cluster);
//  ctx.statement_to_add = malloc(sizeof(*(ctx.statement_to_add)) * nbr_cluster);
  //ctx.statement_body = malloc(sizeof(*(ctx.statement_body)) * nbr_cluster);
  ctx.statement_send_receive = malloc(sizeof(*(ctx.statement_send_receive)) * nbr_cluster);
  for (int i = 0; i < nbr_cluster; ++i) {
    ctx.statement_send_receive[i] = statement_undefined;
  }
  ctx.statement_work_on = statement_undefined;

  ctx.nbr_cluster = nbr_cluster;
  ctx.current_cluster = -2;
  ctx.current_task = task_undefined;
  //ctx.last_cluster = -2;

  ctx.tag = malloc(sizeof(*(ctx.tag)) * nbr_cluster);
  for (int i = 0; i < nbr_cluster; ++i) {
    ctx.tag[i] = malloc(sizeof(**(ctx.tag)) * nbr_cluster);
    for (int j = 0; j < nbr_cluster; ++j) {
      ctx.tag[i][j] = 0;
    }
  }

  ctx.return_statement = statement_undefined;

  return ctx;
}
static void conv_free_ctx(ctx_conv_t * ctx) {
//  pips_assert("stack of task not empty", stack_size(ctx->stack_task) == 0);
////  pips_assert("current_task have to be undefined", ctx->current_task == task_undefined);
  mpi_free_ctx(&ctx->ctx_mpi);

//  if (ctx->current_cluster >= 0) {
//    statement st = (statement)hash_get(ctx->hash_statement_to_add, &(ctx->current_cluster);
//    free_statement(st);
//  }
  for (int i = 0; i < ctx->nbr_cluster; ++i) {
    free(ctx->tag[i]);
  }
  free(ctx->tag);

//  free(ctx->statement_to_add);
  //free(ctx->statement_body);
  free(ctx->statement_send_receive);
  return;
}



static void ctx_init(ctx_conv_t * ctx) {
  int i = 0;
  for (i=0; i<ctx->nbr_cluster; i++) {
    //   statement body = make_empty_block_statement();
    //  expression cond = MakeBinaryCall(entity_intrinsic(EQUAL_OPERATOR_NAME), entity_to_expression(ctx->ctx_mpi.rank), int_to_expression(i));
    //  statement stadd = make_test_statement(cond, body, make_empty_block_statement());

//    hash_put_or_update(ctx->hash_statement_receive, (void *)i, receive);
//    hash_put_or_update(ctx->hash_statement_to_add,  (void *)i, stadd);
    ctx->statement_send_receive[i] = statement_undefined;
    //ctx->statement_body[i] = body;
//    ctx->statement_to_add[i] = stadd;
  }
}
//static void ctx_reset(ctx_conv_t * ctx) {
//  int i = 0;
//  int current_cluster = ctx->current_cluster;
//  if (current_cluster != -2) {
//    for (i=0; i<ctx->nbr_cluster; i++) {
////      if (i != current_cluster) {
//        statement receive = make_empty_block_statement();
//        expression cond = MakeBinaryCall(entity_intrinsic(EQUAL_OPERATOR_NAME), entity_to_expression(ctx->ctx_mpi.rank), int_to_expression(i));;
//        statement stadd = make_test_statement(cond, receive, make_continue_statement(entity_empty_label()));
//
//        hash_update(ctx->hash_statement_receive, &i, receive);
//        hash_update(ctx->hash_statement_to_add, &i, stadd);
////      }
//    }
//  }
//}

static void ctx_set_return_statement(ctx_conv_t * ctx, statement rs) {
  if (!statement_undefined_p(ctx->return_statement)) {
    pips_user_error("Can only have one return statement :(\n");
  }
  ctx->return_statement = copy_statement(rs);
}
static statement ctx_get_return_statement(const ctx_conv_t ctx) {
  return ctx.return_statement;
}

static void ctx_set_statement_work_on(ctx_conv_t * ctx, statement st) {
  //each time we work on a new task, we reinitialize the context
  //especially the statements to generate
  ctx_init(ctx);

  task ta = load_parallel_task_mapping(st);
  ctx->current_task = ta;
  int cluster = task_on_cluster(ta);
  ctx->current_cluster = cluster;

  statement stat = copy_statement(st);
  free_extensions(statement_extensions(stat));
  statement_extensions(stat) = empty_extensions();

//  statement testst = (statement) hash_get(ctx->hash_statement_to_add, (void *)(cluster));
//  statement testst = ctx->statement_to_add[cluster];
//  test te = statement_test(testst);
//  free_statement(test_true(te));
//  test_true(te) = stat;

//  hash_put_or_update(ctx->hash_statement_receive, (void *)(cluster), st);
  //ctx->statement_body[cluster] = stat;
  ctx->statement_work_on = stat;
}
static statement ctx_get_statement_work_on(const ctx_conv_t ctx) {
  //int current_cluster = ctx.current_cluster;
  //statement st = ctx.statement_body[current_cluster];
  statement st = ctx.statement_work_on;
  return st;
}

//static statement ctx_new_body_cluster(ctx_conv_t * ctx, int for_cluster) {
//  pips_assert("for_cluster and ctx.current_cluster must be different\n", ctx->current_cluster!=for_cluster);
//  if (!empty_statement_or_continue_p(ctx->statement_body[for_cluster])) {
//    ctx->statement_body[for_cluster] = make_empty_block_statement();
//  }
//  return ctx.statement_body[for_cluster];
//}
//static void ctx_add_to_body_cluster(ctx_conv_t * ctx, statement stat, int for_cluster) {
//  if (!statement_undefined_p(stat)) {
//    statement st = ctx->statement_body[for_cluster];
//    insert_statement(st, stat, false);
//  }
//}
//static statement ctx_get_body_cluster(const ctx_conv_t ctx, int for_cluster) {
//  //pips_assert("for_cluster and ctx.current_cluster must be different\n", ctx.current_cluster!=for_cluster);
//  return ctx.statement_body[for_cluster];
//}
//static void ctx_update_body_cluster(ctx_conv_t * ctx, int for_cluster) {
//  pips_assert("for_cluster and ctx.current_cluster must be different\n", ctx->current_cluster!=for_cluster);
//  if (!empty_statement_or_continue_p(ctx->statement_body[for_cluster])) {
//    test_true(statement_test(ctx->statement_to_add[for_cluster])) = ctx->statement_body[for_cluster];
//    //ctx->statement_body[for_cluster] = make_empty_block_statement();
//  }
//}
//static void ctx_set_body_cluster(ctx_conv_t * ctx, statement stat, int for_cluster) {
//  pips_assert("for_cluster and ctx.current_cluster must be different\n", ctx->current_cluster!=for_cluster);
//  if (!statement_undefined_p(ctx->statement_body[for_cluster])) {
//    ctx->statement_body[for_cluster] = stat;
//    test_true(statement_test(ctx->statement_to_add[for_cluster])) = stat;
//  }
//}

static void ctx_set_send_statement(ctx_conv_t * ctx, statement send) {
  pips_assert("ctx->send_statement must be statement_undefined\n", statement_undefined_p(ctx->statement_send_receive[ctx->current_cluster]));
  ctx->statement_send_receive[ctx->current_cluster] = send;
}
static statement ctx_get_send_statement(ctx_conv_t * ctx) {
  pips_assert("ctx->send_statement mustn't be statement_undefined\n", !statement_undefined_p(ctx->statement_send_receive[ctx->current_cluster]));
  statement send = ctx->statement_send_receive[ctx->current_cluster];
  print_statement(send);
  ctx->statement_send_receive[ctx->current_cluster] = statement_undefined;
  return send;
}
static void ctx_set_receive_statement(ctx_conv_t * ctx, statement receive, int for_cluster) {
  pips_assert("for_cluster and ctx.current_cluster must be different\n", ctx->current_cluster!=for_cluster);
  ctx->statement_send_receive[for_cluster] = receive;
}
static statement ctx_get_receive_statement(const ctx_conv_t ctx, int for_cluster) {
  pips_assert("for_cluster and ctx.current_cluster must be different\n", ctx.current_cluster!=for_cluster);
  statement receive = ctx.statement_send_receive[for_cluster];
  return receive;
}
//static void ctx_update_receive_statement_from_body_statement(ctx_conv_t * ctx, int for_cluster) {
//  pips_assert("for_cluster and ctx.current_cluster must be different\n", ctx->current_cluster!=for_cluster);
//  ctx->statement_send_receive[for_cluster] = ctx->statement_body[for_cluster];
//}

//static void ctx_set_body_statement_to_add(ctx_conv_t * ctx, statement new_body, int for_cluster) {
//  pips_assert("for_cluster and ctx.current_cluster must be different\n", ctx->current_cluster!=for_cluster);
//  if (empty_statement_or_continue_p(test_true(statement_test(ctx->statement_to_add[for_cluster])))) {
//    free(test_true(statement_test(ctx->statement_to_add[for_cluster])));
//  }
//  test_true(statement_test(ctx->statement_to_add[for_cluster])) = new_body;
//}
//static statement ctx_get_body_statement_to_add(const ctx_conv_t ctx, int for_cluster) {
//  pips_assert("for_cluster and ctx.current_cluster must be different\n", ctx.current_cluster!=for_cluster);
//  return test_true(statement_test(ctx.statement_to_add[for_cluster]));
//}

static bool ctx_is_blocking(const ctx_conv_t ctx) {
  task ta = ctx.current_task;
  return (bool) task_synchronization(ta);
}

static int ctx_get_tag(const ctx_conv_t ctx, int sender, int receiver) {
  pips_assert("sender_cluster<nbr_cluster\n", sender<ctx.nbr_cluster);
  pips_assert("receiver_cluster<nbr_cluster\n", receiver<ctx.nbr_cluster);
  return ctx.tag[sender][receiver];
}
static void ctx_inc_tag(ctx_conv_t * ctx, int sender, int receiver) {
  pips_assert("sender_cluster<nbr_cluster\n", sender<ctx->nbr_cluster);
  pips_assert("receiver_cluster<nbr_cluster\n", receiver<ctx->nbr_cluster);
  ctx->tag[sender][receiver]++;
}
/**
 *
 * \return
 *                  if (rank==p) {
 *                    [...]
 *                    MPI_Send();
 *                  }
 *                  if (rank==0) {
 *                    [...]
 *                    MPI_Recv();
 *                  }
 *                  [...]
 *                  if (rank==n) {
 *                    [...]
 *                    MPI_Recv();
 *                  }
 */
static statement ctx_generate_new_statement_cluster_dependant(const ctx_conv_t ctx) {
  int current_cluster = ctx.current_cluster;
  statement st = make_empty_block_statement();
//  hash_table hsta = ctx.hash_statement_to_add;

  {
//  statement current = (statement) hash_get(hsta, (void *)(current_cluster+1));
//  statement current = ctx.statement_to_add[current_cluster];
//  insert_statement(st, current, false);
    statement current = ctx.statement_work_on;
    expression cond = MakeBinaryCall(entity_intrinsic(EQUAL_OPERATOR_NAME), entity_to_expression(ctx.ctx_mpi.rank), int_to_expression(current_cluster));
    statement add = make_test_statement(cond, current, make_empty_block_statement());
    insert_statement(st, add, false);
  }

  int i=0;
  for (i=0; i<ctx.nbr_cluster; i++) {
    if (i != current_cluster) {
//      statement add = (statement) hash_get(hsta, (void *)i);
//      statement add = ctx.statement_to_add[i];
      statement receiv = ctx.statement_send_receive[i];
      if (!statement_undefined_p(receiv)) {
        expression cond = MakeBinaryCall(entity_intrinsic(EQUAL_OPERATOR_NAME), entity_to_expression(ctx.ctx_mpi.rank), int_to_expression(i));
        statement add = make_test_statement(cond, receiv, make_empty_block_statement());
        insert_statement(st, add, false);
        ctx.statement_send_receive[i] = statement_undefined;
      }
    }
  }

  return st;
}

/*******************************************************
 * CONTEXT MANAGEMENT : END                            *
 *******************************************************/

/**
 * put initialize MPI functions at the beginning of the module_stateent (function):
 *    // Generated by Pass MPI_CONVERSION
 *    MPI_Status status0;
 *    // Generated by Pass MPI_CONVERSION
 *    MPI_Request request0;
 *    // Generated by Pass MPI_CONVERSION
 *    int size0, rank0;
 *    MPI_Init(&argc, &argv);
 *    MPI_Comm_size(MPI_COMM_WORLD, &size0);
 *    MPI_Comm_rank(MPI_COMM_WORLD, &rank0);
 */
static void initilization(statement module_statement, const ctx_conv_t ctx) {
  insert_statement(module_statement, mpi_comm_rank_ctx(ctx.ctx_mpi), true);
  insert_statement(module_statement, mpi_comm_size_ctx(ctx.ctx_mpi), true);
  insert_statement(module_statement, mpi_init_ctx(ctx.ctx_mpi), true);

  push_generated_variable_commenter(mpi_conversion_declaration_commenter);
  add_declaration_statement_at_beginning(module_statement, ctx.ctx_mpi.rank);
  add_declaration_statement_at_beginning(module_statement, ctx.ctx_mpi.size);
  add_declaration_statement_at_beginning(module_statement, ctx.ctx_mpi.mpi_request);
  add_declaration_statement_at_beginning(module_statement, ctx.ctx_mpi.mpi_status);
  pop_generated_variable_commenter();
}

/**
 * put finalize MPI functions at the end of the module_stateent (function), before the return:
 *    MPI_Finalize();
 */
static void finalization(statement module_statement, const ctx_conv_t ctx) {
  insert_statement(module_statement, mpi_finalize_ctx(ctx.ctx_mpi), false);
  statement rs = ctx_get_return_statement(ctx);
  if (!statement_undefined_p(rs))
    insert_statement(module_statement, rs, false);
}


static bool is_distributed_comments(string comments) {
  if (empty_comments_p(comments))
    return false;

  string dist = "distributed";

  return strstr(comments, dist) != NULL;
}

static bool is_distributed_send_comments(string comments) {
  if (empty_comments_p(comments))
    return false;

  string dist = "distributed";
  string send = "send";

  return strstr(comments, dist) != NULL && strstr(comments, send) != NULL;
}

static bool is_distributed_receive_comments(string comments) {
  if (empty_comments_p(comments))
    return false;

  string dist = "distributed";
  string receive = "receive";

  return strstr(comments, dist) != NULL && strstr(comments, receive) != NULL;
}

static int find_sender_cluster(ctx_conv_t * ctx, __attribute__ ((__unused__)) statement stat) {
//  pips_assert("statement stat is copy receive statement",
//      is_distributed_send_comments(statement_comments(stat)) && assignment_statement_p(stat));
//
//  call c = statement_call(stat);
//  list args = call_arguments(c);
//  expression rhs = EXPRESSION(CAR(CDR(args)));
//
//  entity rhse = expression_to_entity(rhs);
//  string rhsname = entity_name(rhse);
//  list l = strsplit(rhsname, "_");
//  return atoi(STRING(CAR(gen_nreverse(l))));
  return ctx->current_cluster;
}

static int find_receiver_cluster(__attribute__ ((__unused__)) ctx_conv_t * ctx, statement stat) {
  pips_assert("statement stat is copy receive statement",
      is_distributed_receive_comments(statement_comments(stat)) && assignment_statement_p(stat));

  call c = statement_call(stat);
  list args = call_arguments(c);
  expression lhs = EXPRESSION(CAR(args));

  entity lhse = expression_to_entity(lhs);
  string lhsname = entity_name(lhse);
  list l = strsplit(lhsname, "_");
  return atoi(STRING(CAR(gen_nreverse(l))));
}

static statement generate_send_from_statement(ctx_conv_t * ctx, statement stat) {
  statement st = statement_undefined;

  pips_assert("statement stat is copy send statement",
      is_distributed_send_comments(statement_comments(stat)) && assignment_statement_p(stat));

  expression buffer = expression_undefined;
  int sender = find_sender_cluster(ctx, stat);
  int receiver = find_receiver_cluster(ctx, stat);
  int tag = ctx_get_tag(*ctx, sender, receiver);
  bool blocking = ctx_is_blocking(*ctx);

  call c = statement_call(stat);
  list args = call_arguments(c);
  //  expression lhs = EXPRESSION(CAR(args));
   expression rhs = EXPRESSION(CAR(CDR(args)));

  buffer = copy_expression(rhs);

  st = mpi_send_ctx(ctx->ctx_mpi, buffer, 1, receiver, tag, blocking);

  return st;
}

static statement generate_receive_from_statement(ctx_conv_t * ctx, statement stat) {
  statement st = statement_undefined;

  pips_assert("statement stat is copy receive statement",
      is_distributed_receive_comments(statement_comments(stat)) && assignment_statement_p(stat));

  expression buffer = expression_undefined;
  int sender = find_sender_cluster(ctx, stat);
  int receiver = find_receiver_cluster(ctx, stat);
  int tag = ctx_get_tag(*ctx, sender, receiver);
  bool blocking = ctx_is_blocking(*ctx);

  call c = statement_call(stat);
  list args = call_arguments(c);
  expression lhs = EXPRESSION(CAR(args));
  //  expression rhs = EXPRESSION(CAR(CDR(args)));

  buffer = copy_expression(lhs);

  st = mpi_recv_ctx(ctx->ctx_mpi, buffer, 1, sender, tag, blocking);

  return st;
}


static void replace_sender_entity_by_receiver_entity_in_reference(reference ref, int *receiv_cluster) {
  pips_debug(8, "begin\n");
  entity ent = reference_variable(ref);
  const char * prefix = get_string_property((const char * ) MPI_GENERATION_PREFIX);
  const char * ent_name = entity_user_name(ent);
  if (same_stringn_p(prefix, ent_name, strlen(prefix))) {
    char * prefix2 = strdup(concatenate(prefix, "_index_", NULL));
    if (!same_stringn_p(prefix2, ent_name, strlen(prefix2))) {
      // It's not an iterator variable, so need to modify to have the receiver variable
      pips_user_warning("Not implemented yet.\n"
          "Modify variable to use vriable of the cluster number %i", *receiv_cluster);
    //NOT good...
//    string cluster_id = strrchr(entity_name(ent),'_');
//    string new_name = gen_strndup0( entity_name(ent), strlen(entity_name(ent))-strlen(cluster_id)+1 );
////    string new_name = strdup(entity_name(ent));
////    string cluster_id = strrchr(new_name,'_');
////    new_name[cluster_id-new_name+1] = '\0';
//    pips_user_warning("new_name=%s\n", new_name);
//    new_name = concatenate(new_name, i2a(*receiv_cluster), NULL);
//    pips_user_warning("new_name=%s\n", new_name);
//
//    entity new_entity = gen_find_tabulated(new_name, entity_domain);
//    if (entity_undefined_p(new_entity)) {
//      pips_user_error("The entity %s doesn't exit\n", new_name);
//      return;
//    }
//
//    reference_variable(ref) = new_entity;
    }
    free(prefix2);
  }
  else {
    // TODO more com need to be add here, case of dynamic scheduling
    pips_user_warning("NOT a generated MPI variable (entity_name(ent)=%s)\n"
        //"Be sure that it's only a iterator variable\n"
        , entity_name(ent));
  }

  pips_debug(8, "end\n");
}




static bool sequence_working_false(sequence seq, ctx_conv_t * ctx);
static bool test_working_false(test t, ctx_conv_t * ctx);
static bool search_copy_communication(statement stat, ctx_conv_t * ctx);
static void make_send_receive_conversion(statement stat, ctx_conv_t * ctx);


/**
 * This function update the receive statements for a sequential statement
 * NB : This function can be put in search_copy_communication;
 *      in this case search_copy_communication can return true and false
 *      And have to treat the declaration here instead of in make_send_receive_conversion
 * \param seq       sequence to treat
 * \param ctx       context
 * \return          always false, we make another gen_recurse in this function
 */
static bool sequence_working_false(sequence seq, ctx_conv_t * ctx) {
  pips_debug(8, "begin\n");
  list stats = sequence_statements(seq);

  int nbr_cluster = ctx->nbr_cluster;

  // st[cluster_num] will correspond to a sequence of MPI_recv that will update
  //   the receive statements to add
  statement st[nbr_cluster];
  for (int i = 0; i < nbr_cluster; ++i) {
    if (i!=ctx->current_cluster) {
      st[i] = make_empty_block_statement();
//      st[i] = ctx_new_body_cluster(ctx, i);
    }
  }

  FOREACH(STATEMENT, s, stats) {
    //TODO ...

    for (int i = 0; i < nbr_cluster; ++i) {
      if (i!=ctx->current_cluster) {
        pips_assert("receiv_statement must be undefined when we enter this function\n",
            statement_undefined_p(ctx_get_receive_statement(*ctx, i)));
      }
//      else {
//        pips_assert("\n", statement_undefined_p(ctx_get_send_statement(ctx)));
//      }
    }

    gen_context_multi_recurse(s, ctx
//        gen_context_recurse(s, ctx
        , statement_domain, search_copy_communication, make_send_receive_conversion
        , sequence_domain, sequence_working_false, gen_core /*gen_null*/
        , test_domain, test_working_false, gen_core /*gen_null*/
//            , loop_domain, gen_true, gen_true
//            , whileloop_domain, gen_true, gen_true
//            , forloop_domain, gen_true, gen_true
//            //, call_domain, gen_true, gen_true             // to detect copy for communication statement done in statement_domaine case
//            //, multitest_domain, gen_true, gen_true        // don't exist in PIPS yet
//            //, unstructured_domain, gen_true, gen_true     // never happens? bug case?
//            //, expression_domain, gen_true, gen_true
        , NULL
        );

    // between each statement of the sequence,
    // if a receive statement is present, then it is memorize in st and we reset the receive statement for the next statement to analyze
    for (int i = 0; i < nbr_cluster; ++i) {
      if (i!=ctx->current_cluster) {
        statement receive_statement = ctx_get_receive_statement(*ctx, i);
        if (!statement_undefined_p(receive_statement)) {
          insert_statement(st[i], receive_statement, false);
          ctx_set_receive_statement(ctx, statement_undefined, i);
        }
      }
    }
  }

  // At the end of the sequence,
  // the receive statement is modified to be to the st that correspond to all the receive statements that mus be done by the sequence
  for (int i = 0; i < nbr_cluster; ++i) {
    if (i!=ctx->current_cluster) {
      if (!empty_statement_or_continue_p(st[i])) {
        ctx_set_receive_statement(ctx, st[i], i);
//        ctx_set_body_statement_to_add(ctx, st[i], i);
      }
      else {
        free(st[i]);
      }
//      ctx_update_receive_statement_from_body_statement(ctx, i);
//      ctx_update_body_cluster(ctx, i);
    }
  }

  pips_debug(8, "end\n");
  return false;
}


/**
 * This function update the receive statements for a test statement
 * NB : This function can be put in search_copy_communication;
 *      in this case search_copy_communication can return true and false
 * \param t         test to treat
 * \param ctx       context
 * \return          always false, we make another gen_recurse
 */
static bool test_working_false(test t, ctx_conv_t * ctx) {
  pips_debug(8, "begin\n");

  int nbr_cluster = ctx->nbr_cluster;
  statement st[nbr_cluster];
  statement st_true[nbr_cluster];
  statement st_false[nbr_cluster];
  for (int i = 0; i < nbr_cluster; ++i) {
    if (i!=ctx->current_cluster) {
//      st[i] = make_empty_block_statement();
      st[i] = statement_undefined;
      st_true[i] = statement_undefined;
      st_false[i] = statement_undefined;
      //      st[i] = ctx_new_body_cluster(ctx, i);
    }
  }

  expression cond = test_condition(t);
  statement ttrue = test_true(t);
  statement tfalse = test_false(t);

  //  //TODO analyze dynamic
  //  if (cond!=entier) {
  //    for (int i = 0; i < ctx->nbr_cluster; ++i) {
  //        if (i!=ctx->current_cluster) {
  //
  //        }
  //        else {
  //          //TODO modify AST
  //        }
  //    }
  //  }

  //true case
  if (!statement_undefined_p(ttrue)) {
    for (int i = 0; i < nbr_cluster; ++i) {
      if (i!=ctx->current_cluster) {
        pips_assert("\n", statement_undefined_p(ctx_get_receive_statement(*ctx, i)));
      }
    }

    gen_context_multi_recurse(ttrue, ctx
        //        gen_context_recurse(s, ctx
        , statement_domain, search_copy_communication, make_send_receive_conversion
        , sequence_domain, sequence_working_false, gen_core /*gen_null*/
        , test_domain, test_working_false, gen_core /*gen_null*/
        //            , loop_domain, gen_true, gen_true
        //            , whileloop_domain, gen_true, gen_true
        //            , forloop_domain, gen_true, gen_true
        //            //, call_domain, gen_true, gen_true             // to detect copy for communication statement done in statement_domaine case
        //            //, multitest_domain, gen_true, gen_true        // don't exist in PIPS yet
        //            //, unstructured_domain, gen_true, gen_true     // never happens? bug case?
        //            //, expression_domain, gen_true, gen_true
        , NULL
    );

    //Memorize the result of the true case
    for (int i = 0; i < ctx->nbr_cluster; ++i) {
      if (i!=ctx->current_cluster) {
        st_true[i] = ctx_get_receive_statement(*ctx, i);
        ctx_set_receive_statement(ctx, statement_undefined, i);
      }
    }
  }

  //false case
  if (!statement_undefined_p(tfalse)) {
    for (int i = 0; i < nbr_cluster; ++i) {
      if (i!=ctx->current_cluster) {
        pips_assert("\n", statement_undefined_p(ctx_get_receive_statement(*ctx, i)));
      }
    }

    gen_context_multi_recurse(tfalse, ctx
        //        gen_context_recurse(s, ctx
        , statement_domain, search_copy_communication, make_send_receive_conversion
        , sequence_domain, sequence_working_false, gen_core /*gen_null*/
        , test_domain, test_working_false, gen_core /*gen_null*/
        //            , loop_domain, gen_true, gen_true
        //            , whileloop_domain, gen_true, gen_true
        //            , forloop_domain, gen_true, gen_true
        //            //, call_domain, gen_true, gen_true             // to detect copy for communication statement done in statement_domaine case
        //            //, multitest_domain, gen_true, gen_true        // don't exist in PIPS yet
        //            //, unstructured_domain, gen_true, gen_true     // never happens? bug case?
        //            //, expression_domain, gen_true, gen_true
        , NULL
    );

    //Memorize the result of the false case
    for (int i = 0; i < ctx->nbr_cluster; ++i) {
      if (i!=ctx->current_cluster) {
        st_false[i] = ctx_get_receive_statement(*ctx, i);
        ctx_set_receive_statement(ctx, statement_undefined, i);
      }
    }
  }

  for (int i = 0; i < ctx->nbr_cluster; ++i) {
    //    bool need_more_com = false;     //TODO: Not implemented yet
    expression ncond = copy_expression(cond);
    if (!integer_constant_expression_p(ncond)) {
      gen_context_recurse(ncond, &i, reference_domain, gen_true2, replace_sender_entity_by_receiver_entity_in_reference);
    }

    if (i!=ctx->current_cluster) {
      if (!statement_undefined_p(st_true[i]) || !statement_undefined_p(st_false[i])) {
        //Generate if statement considering whether true or false case make communication
        if (statement_undefined_p(st_false[i])) {
          //Generate "if (ncond) st_true"
          st[i] = make_test_statement(
              ncond,
              st_true[i],
              make_empty_block_statement());
        }
        else if (statement_undefined_p(st_true[i])) {
          //Generate "if (!ncond) st_false"
          st[i] = make_test_statement(
              not_expression(ncond),
              //unary_intrinsic_expression(C_NOT_OPERATOR_NAME, ncond),
              st_false[i],
              make_empty_block_statement());
        }
        else {
          //Generate "if (ncond) st_true else st_false"
          st[i] = make_test_statement(
              ncond,
              st_true[i],
              st_false[i]);
        }

          ctx_set_receive_statement(ctx, st[i], i);
//          ctx_set_body_statement_to_add(ctx, st[i], i);
      }
    }
  }

  pips_debug(8, "end\n");
  return false;
}

/**
 * use as filter for gen_context_recurse
 * check if the statement stat will be communication
 * if so, generate the MPI_Send and MPI_Receive corresponding.
 * by this fact, when we leave the statement, we know if we encounter a communication in the explored AST
 * \param stat      statement analyzed
 * \param ctx       context
 * \return          always true
 */
static bool search_copy_communication(statement stat, ctx_conv_t * ctx) {
  pips_debug(8, "begin\n");
  if (assignment_statement_p(stat) && is_distributed_comments(statement_comments(stat))) {
    int sender_cluster = find_sender_cluster(ctx, stat);
    int receiver_cluster = find_receiver_cluster(ctx, stat);
    statement mpi_send_st = generate_send_from_statement(ctx, stat);
    statement mpi_receive_st = generate_receive_from_statement(ctx, stat);

    ctx_inc_tag(ctx, sender_cluster, receiver_cluster);

    ctx_set_send_statement(ctx, mpi_send_st);
    ctx_set_receive_statement(ctx, mpi_receive_st, receiver_cluster);
    //TODO remplacer la copi par le send dans le rewrite si meme if  --> Done
    //TODO modifier les flow pour le receive dans le rewrite si statement est control flow
    //TODO add declaration pour les receive si statement sequence
  }

  pips_debug(8, "end\n");
  return true;
}

/**
 * Update statement that we work on by replace communication assignment by real MPI_send function
 * and compute the corresponding MPI_receiv that must be done
 */
static void make_send_receive_conversion(statement stat, ctx_conv_t * ctx) {
  pips_debug(5, "begin\n");
  statement st = (statement) gen_get_ancestor_type(statement_domain, stat);
  statement mpi_send_st = statement_undefined;

  /**
   * if the statement is a sequence
   *   add the declaration for all the receive cluster (that have a receive statement)
   */
  if (statement_sequence_p(stat)) {
    //Only add the declaration
    push_generated_variable_commenter(mpi_conversion_declaration_commenter);
    for (int i = 0; i < ctx->nbr_cluster; ++i) {
      if (i!=ctx->current_cluster) {
        statement receive_statement = ctx_get_receive_statement(*ctx, i);
        // verify the presence of a receive message
        if (!statement_undefined_p(receive_statement)) {
          receive_statement = make_block_with_stmt_if_not_already(receive_statement);
          if (receive_statement != ctx_get_receive_statement(*ctx, i)) {
            ctx_set_receive_statement(ctx, receive_statement, i);
          }

          //Copy all the declaration of the sequence
          // FIXME: Problem with the scope name? same entity declare at many places (but totally different scope so no collision)?
          FOREACH(ENTITY, decl, statement_declarations(stat)) {
            receive_statement = add_declaration_statement(receive_statement, decl);
            statement_declarations(receive_statement) = CONS(ENTITY, decl, statement_declarations(receive_statement));
          }
        }
      }
    }
    pop_generated_variable_commenter();
  }
  /**
   * if the statement stat is copy statement for communication
   *   replace the copy statement by the send communication statement
   */
  else if (assignment_statement_p(stat) && is_distributed_comments(statement_comments(stat))) {
    //if it's a copy-communication statement, the last function called by PIPS was search_copy_communication
    // and this function must have create a send_statement
    mpi_send_st = ctx_get_send_statement(ctx);
    ifdebug(8) {
      pips_debug(8, "mpi_send_st\n");
      print_statement(mpi_send_st);
      pips_debug(8, "ctx_get_statement_work_on(*ctx)\n");
      print_statement(ctx_get_statement_work_on(*ctx));
      pips_debug(8, "end ctx_get_statement_work_on(*ctx)\n");
    }

    if (statement_replace_in_root_statement(stat, mpi_send_st, ctx_get_statement_work_on(*ctx)))
      free_statement(stat);
    else
      pips_internal_error("This case never happen.\n");
  }

  /**
   * look the parent statement of the AST
   * to duplicate it for the receiver's clusters
   *   the duplication of the AST is only done if there is a receive statement
   *   (if (!statement_undefined_p(ctx_get_receive_statement(*ctx, i))))
   * TODO and potentially modify the AST in case of dynamic flow by adding variable and send/receive of this dynamic value \\
   *      (This case can only happen if copy_value_of_write is used, but this compilation process is unsure in many point)
   */
  if (st != NULL) {
    for (int i = 0; i < ctx->nbr_cluster; ++i) {
      if (i!=ctx->current_cluster) {
        statement receive_statement = ctx_get_receive_statement(*ctx, i);

        if (!statement_undefined_p(receive_statement)) {
          switch (instruction_tag(statement_instruction(st))) {
          case is_instruction_sequence:
          {
            // Nothing to do
            pips_internal_error("This case never happen because sequence_working_false always return false\n");
            break;
          }
          case is_instruction_test:
          {
            pips_internal_error("This case never happen because test_working_false always return false\n");
//            test t = statement_test(st);
//            expression cond = test_condition(t);
//            statement new_statement = statement_undefined;
//
//            expression ncond = copy_expression(cond);
//            bool need_more_com = false;     // TO DO: Not implemented yet
//            if (!integer_constant_expression_p(ncond)) {
//              gen_context_recurse(ncond, &i, reference_domain, gen_true, replace_sender_entity_by_receiver_entity_in_reference);
//            }
//            if (need_more_com) {
//              // TO DO modify AST if dynamic
//              //add more send/receive com
//              pips_internal_error("some variables do not exist on receive cluster. Need to send them.\n");
//            }
//
//            statement receive_statement = ctx_get_receive_statement(*ctx, i);
//            if (!statement_undefined_p(receive_statement)) {
//              if (test_true(t)==stat) {
//                new_statement = make_test_statement(
//                    ncond,
//                    receive_statement,
//                    make_empty_block_statement());
//              }
//              else if (test_false(t)==stat) {
//                new_statement = make_test_statement(
//                    not_expression(ncond),
//                    //unary_intrinsic_expression(C_NOT_OPERATOR_NAME, copy_expression(cond)),
//                    receive_statement,
//                    make_empty_block_statement());
//              }
//              else {
//                pips_internal_error("This case never happen;\n");
//              }
//
//              ctx_set_receive_statement(ctx, new_statement, i);
//              new_statement = statement_undefined;
//            }
            break;
          }
          case is_instruction_loop:
          {
            ifdebug(8) {
              pips_debug(8, "is_instruction_loop\n");
              print_statement(st);
              pips_debug(8, "\n");
            }

            loop l = statement_loop(st);
            range rg = loop_range(l);
            expression lower = range_lower(rg);
            expression upper = range_upper(rg);
            expression increment = range_increment(rg);
            statement new_statement = statement_undefined;

            expression nlower = copy_expression(lower);
            expression nupper = copy_expression(upper);
            expression nincrement = copy_expression(increment);
            bool need_more_com = false;     //TODO: Not implemented yet
            if (!integer_constant_expression_p(nlower))
              gen_context_recurse(nlower, &i, reference_domain, gen_true2, replace_sender_entity_by_receiver_entity_in_reference);
            if (!integer_constant_expression_p(nupper))
              gen_context_recurse(nupper, &i, reference_domain, gen_true2, replace_sender_entity_by_receiver_entity_in_reference);
            if (!integer_constant_expression_p(nincrement))
              gen_context_recurse(nincrement, &i, reference_domain, gen_true2, replace_sender_entity_by_receiver_entity_in_reference);
            if (need_more_com) {
              //TODO modify AST if dynamic
              //add more send/receive com
              pips_internal_error("some variables do not exist on receive cluster. Need to send/receive them.\n");
            }

            // Try to aggregate the communication when sending adjacent array element
            syntax snincrement = expression_syntax(nincrement);
            syntax snlower = expression_syntax(nlower);
            syntax snupper = expression_syntax(nupper);
            ifdebug(8) {
              pips_debug(8, "nincrement\n");
              print_expression(nincrement);
              pips_debug(8, "nsincrement\n");
              print_syntax(snincrement);

              pips_debug(8, "nlower\n");
              print_expression(nlower);
              pips_debug(8, "snlower\n");
              print_syntax(snlower);

              pips_debug(8, "nupper\n");
              print_expression(nupper);
              pips_debug(8, "snupper\n");
              print_syntax(snupper);
            }

            // Increment must be +1
            if (expression_constant_p(nincrement) && expression_to_int(nincrement) == 1) {
//              new_statement = generate_receive_from_statement(ctx, stat);
//              new_statement = mpi_recv_ctx(ctx->ctx_mpi, buffer, 1, sender, tag, blocking);
//              mpic_make_mpi_recv(buffer, size, mpitype, source, tag, ctx.mpi_communicator, ctx.mpi_status, ctx.error);
//              if (entity_undefined_p(result)) {
//                mpi_st = call_to_statement(mpi_call);
//              }
//              else {
//                mpi_st = make_assign_statement(entity_to_expression(result), call_to_expression(mpi_call));
//              }
//              {result =} MPI_Recv(&buffer, size, mpitype, source, tag, communicator, &status);
//              {result =} MPI_Irecv(&buffer, size, mpitype, source, tag, communicator, &request);
              call mpi_call_recv;
              entity result = entity_undefined;
              // receive_statement is : [result =] MPI_[I]Recv(&buffer, size, mpitype, source, tag, communicator, &status);
              //                   or : [result =] MPI_IRecv(&buffer, size, mpitype, source, tag, communicator, &request);
              if (assignment_statement_p(receive_statement)) {
                call assign_call = instruction_call(statement_instruction(receive_statement));
                list args = call_arguments(assign_call);
                expression lhs = EXPRESSION(CAR(args));
                expression rhs = EXPRESSION(CAR(CDR(args)));
                result = expression_to_entity(lhs);
                mpi_call_recv = expression_call(rhs);
              }
              else {
                mpi_call_recv = statement_call(receive_statement);
              }


              list args = call_arguments(mpi_call_recv);
              expression argbuf = (EXPRESSION(CAR(args)));
	      //              expression argsize = (EXPRESSION(CAR(CDR(args))));
//              expression argtype = copy_expression(EXPRESSION(CAR(CDR(CDR(args)))));
//              expression argsource = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(args))))));
//              expression argtag = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(CDR(args)))))));
//              expression argcom = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(CDR(CDR(args))))))));
//              expression argstatreq = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(CDR(CDR(CDR(args)))))))));
              entity lindex = loop_index(l);
              entity argbufent = expression_to_entity(EXPRESSION(CAR(call_arguments((expression_call(argbuf))))));
              ifdebug(8) {
                pips_debug(8, "argbufent\n");
                print_entity_variable(argbufent);
                pips_debug(8, "argbuf\n");
                print_expression(argbuf);
              }

              // verify that we work on the most inside array index for C code
              // TODO need to make the inverse for Fortran code...
              call refcall = expression_call(argbuf);
              reference refbuf = expression_reference(EXPRESSION(CAR(call_arguments(refcall))));
              list indices = reference_indices(refbuf);
              ifdebug(8) {
                pips_debug(8, "refbuf\n");
                print_reference(refbuf);
                pips_debug(8, "lindex\n");
                print_entity_variable(lindex);
              }
              //while (indices != NIL && !same_entity_p(lindex, expression_to_entity(EXPRESSION(CAR(indices))))) {
              //  indices = CDR(indices);
              //}
              for (indices = reference_indices(refbuf);
                  indices != NIL && !same_entity_p(lindex, expression_to_entity(EXPRESSION(CAR(indices))));
                  indices = CDR(indices));

              if (indices != NIL && same_entity_p(lindex, expression_to_entity(EXPRESSION(CAR(indices))))) {
                // if we are in the most inside array index (C code)
                if (CDR(indices) == NIL
                    // expression_constant_p(argsize) && expression_to_int(argsize) == 1 // Normally is already verify in our case
                    ) {
                  // We can replace the MPI_Receiv to a more aggregate one.
                  // ie. instead of making (for (i=[n;m]) MPI_Recv(a[i])) -> MPI_Recv(a[n:m])
                  expression newtype = copy_expression(EXPRESSION(CAR(CDR(CDR(args)))));
                  expression newsource = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(args))))));
                  expression newtag = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(CDR(args)))))));
                  expression newcom = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(CDR(CDR(args))))))));
                  expression newstatreq = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(CDR(CDR(CDR(args)))))))));
                  expression newbuf = expression_undefined;
                  expression newsize = expression_undefined;

                  // Compute the new size of element to communicate
                  if (zero_expression_p(nlower)) {
                    //newsize = copy_expression(nupper); // it's false, we have to add 1 to this number...
                    intptr_t upint;
                    if (expression_integer_value(nupper, &upint))
                      newsize = int_to_expression(upint+1);
                    else
                      newsize = expressions_to_operation(
                          gen_make_list(expression_domain,
                              copy_expression(nupper),
                              int_to_expression(1),
                              NULL),
                          CreateIntrinsic(PLUS_OPERATOR_NAME));
                          //CreateIntrinsic(PLUS_C_OPERATOR_NAME));
                  }
                  else {
                    intptr_t lowint, upint;
                    if (expression_integer_value(nlower, &lowint) && expression_integer_value(nupper, &upint)) {
                      intptr_t newsizeint = upint-lowint+1;
                      if (newsizeint > 0)
                        newsize = int_to_expression(newsizeint);
                      else
                        pips_internal_error("communication of a negative number of elements (%ld)\n"
                            "This case never happen...", newsizeint);
                    }
                    else
                      newsize = expressions_to_operation(
                          gen_make_list(expression_domain,
                              expressions_to_operation(gen_make_list(expression_domain, copy_expression(nlower), copy_expression(nupper), NULL),
                                  CreateIntrinsic(MINUS_OPERATOR_NAME)),
                                  //CreateIntrinsic(MINUS_C_OPERATOR_NAME)),
                              int_to_expression(1),
                              NULL),
                          CreateIntrinsic(PLUS_OPERATOR_NAME));
                          //CreateIntrinsic(PLUS_C_OPERATOR_NAME));
                  }

                  // Compute the new first array element to communicate
                  list oldindices = reference_indices(refbuf);
                  list newindices = NIL;
                  while (oldindices != NIL) {
                    if (same_entity_p(lindex, expression_to_entity(EXPRESSION(CAR(oldindices)))))
                      newindices = CONS(EXPRESSION, copy_expression(nlower), newindices);
                      //newindices = gen_append(CONS(EXPRESSION, int_to_expression(0), NIL), newindices);
                    else
                      newindices = CONS(EXPRESSION, EXPRESSION(CAR(oldindices)), newindices);
                      //newindices = gen_append(CONS(EXPRESSION, EXPRESSION(CAR(oldindices)), NIL), newindices);
                    oldindices = CDR(oldindices);
                  }
                  newindices = gen_nreverse(newindices);
                  newbuf = make_address_of_expression(make_entity_expression(argbufent, newindices));
                  //newbuf = make_call_expression(call_function(expression_call(argbuf)), make_entity_expression(argbufent, newindices));

                  ifdebug(8) {
                    pips_debug(8, "newsize\n");
                    print_expression(newsize);
                    expression_consistent_p(newsize);
                    pips_debug(8, "newbuf\n");
                    print_expression(newbuf);
                  }

                  //Generate the new aggregate receive statement in MPI
                  call receive_call;
                  list newarg = gen_make_list(expression_domain, newbuf, newsize, newtype, newsource, newtag, newcom, newstatreq, NULL);
                  receive_call = make_call(call_function(mpi_call_recv), newarg);
                  if (entity_undefined_p(result)) {
                    new_statement = call_to_statement(receive_call);
                  }
                  else {
                    new_statement = make_assign_statement(entity_to_expression(result), call_to_expression(receive_call));
                  }

                  //Replace the the communication for the sender
                  call send_call, mpi_send_call;
                  entity result_send = entity_undefined;
                  if (assignment_statement_p(mpi_send_st)) {
                    call assign_call = instruction_call(statement_instruction(mpi_send_st));
                    list args = call_arguments(assign_call);
                    expression lhs = EXPRESSION(CAR(args));
                    expression rhs = EXPRESSION(CAR(CDR(args)));
                    result_send = expression_to_entity(lhs);
                    mpi_send_call = expression_call(rhs);
                  }
                  else {
                    mpi_send_call = statement_call(mpi_send_st);
                  }

                  list sendarg;
                  entity sendbufent = expression_to_entity(EXPRESSION(CAR(call_arguments((expression_call(EXPRESSION(CAR(call_arguments(mpi_send_call)))))))));
                  expression sendreq = expression_undefined;
                  expression sendbuf = make_address_of_expression(make_entity_expression(sendbufent, gen_full_copy_list(newindices)));
                  expression sendsize = copy_expression(newsize);
                  expression sendtype = copy_expression(newtype);
                  expression senddest = int_to_expression(i);
                  expression sendtag = copy_expression(newtag);
                  expression sendcom = copy_expression(newcom);
                  // expression sendtype = copy_expression(EXPRESSION(CAR(CDR(CDR(call_arguments(mpi_send_call))))));
                  // expression senddest = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(call_arguments(mpi_send_call)))))));
                  // expression sendtag = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(CDR(call_arguments(mpi_send_call))))))));
                  // expression sendcom = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(CDR(CDR(call_arguments(mpi_send_call)))))))));
                  if (same_entity_p(entity_intrinsic(MPI_SEND_FUNCTION_NAME), call_function(mpi_send_call))) {
                    //MPI_Send
                    sendarg = gen_make_list(expression_domain, sendbuf, sendsize, sendtype, senddest, sendtag, sendcom, NULL);
                  }
                  else {
                    //MPI_Isend
                    sendreq = copy_expression(EXPRESSION(CAR(CDR(CDR(CDR(CDR(CDR(CDR(call_arguments(mpi_send_call))))))))));
                    sendarg = gen_make_list(expression_domain, sendbuf, sendsize, sendtype, senddest, sendtag, sendcom, sendreq, NULL);
                  }
                  send_call = make_call(call_function(mpi_send_call), sendarg);


                  statement send_statement;
                  if (entity_undefined_p(result_send)) {
                    send_statement = call_to_statement(send_call);
                  }
                  else {
                    send_statement = make_assign_statement(entity_to_expression(result_send), call_to_expression(send_call));
                  }

                  if (!statement_replace_in_root_statement(st, send_statement, ctx_get_statement_work_on(*ctx)))
                    pips_internal_error("This case never happen.\n");

                  ifdebug(5) {
                    pips_debug(5, "send_statement\n");
                    print_statement(send_statement);
                    statement_consistent_p(send_statement);
                    pips_debug(5, "\n");
                  }


                  // clean the memory
                  free_statement(receive_statement);
                  receive_statement = statement_undefined;
                  free_statement(mpi_send_st);
                  mpi_send_st = statement_undefined;
                  free_expression(nlower);
                  free_expression(nupper);
                  free_expression(nincrement);
                }
                // else we have to verify that each more index are 0,
                // and the total size of the MPI_[I]Recv is equal to the size of all the inside array...
                else {
                  // TODO: implementation for multidimensional array communication
                  // Not implemented yet...
                  // Does an array resizing can be a issue ?
                  //   For instance the array size for the reception is contiguous but not for the sender...
                  // How to implement it:
                  // We have to verify that the loop concern the last (resp. first for fortran) index of the array to communicate
                  //   that all the inner (resp. outer) dimension start at 0 and communicate all there dimension elements
                  //   that the current dimension that we want to communicate is on all the dimension array and not just part of it
                  //     ie. that the loop start at 0 and end at the size of the array.
                  // Then replace the start of the array to communicate by a 0 for the concern dimension
                  //   and multiply the size to communicate by the size of the current dimension that it's treated.
                  // Do not forget to replace the com for the sender
                  // Do not forget to clean the memory
                  new_statement = make_loop_statement(
                      loop_index(l),
                      nlower, nupper, nincrement,
                      receive_statement);
                }
              }
            }
            // if (statement_undefined_p(new_statement)) {
            else {
              new_statement = make_loop_statement(
                  loop_index(l),
                  nlower, nupper, nincrement,
                  receive_statement);
            }
            ctx_set_receive_statement(ctx, new_statement, i);

            ifdebug(5) {
              pips_debug(5, "receive_statement\n");
              print_statement(receive_statement);
              statement_consistent_p(receive_statement);
              pips_debug(5, "new_statement\n");
              print_statement(new_statement);
              statement_consistent_p(new_statement);
              pips_debug(5, "\n");
            }
            //new_statement = statement_undefined;
            break;
          }
          case is_instruction_whileloop:
          {
            ifdebug(8) {
              pips_debug(8, "is_instruction_whileloop\n");
              print_statement(st);
              pips_debug(8, "\n");
            }

            whileloop l = statement_whileloop(st);
            expression cond = whileloop_condition(l);
            statement new_statement = statement_undefined;

            expression ncond = copy_expression(cond);
            bool need_more_com = false;     //TODO: Not implemented yet
            if (!integer_constant_expression_p(ncond))
              gen_context_recurse(ncond, &i, reference_domain, gen_true2, replace_sender_entity_by_receiver_entity_in_reference);
            if (need_more_com) {
              //TODO modify AST if dynamic
              //add more send/receive com
              pips_internal_error("some variables do not exist on receive cluster. Need to send/receive them.\n");
            }

            new_statement = make_whileloop_statement(
                ncond,
                receive_statement,
                STATEMENT_NUMBER_UNDEFINED,
                evaluation_before_p(whileloop_evaluation(l)));
            ctx_set_receive_statement(ctx, new_statement, i);
            //new_statement = statement_undefined;
            break;
          }
          case is_instruction_forloop:
          {
            ifdebug(8) {
              pips_debug(8, "is_instruction_whileloop\n");
              print_statement(st);
              pips_debug(8, "\n");
            }

            forloop l = statement_forloop(st);
            expression init = forloop_initialization(l);
            expression cond = forloop_condition(l);
            expression incr = forloop_increment(l);
            statement new_statement = statement_undefined;

            expression ninit = copy_expression(init);
            expression ncond = copy_expression(cond);
            expression nincr = copy_expression(incr);
            bool need_more_com = false;     //TODO: Not implemented yet
            if (!integer_constant_expression_p(ninit))
              gen_context_recurse(ninit, &i, reference_domain, gen_true2, replace_sender_entity_by_receiver_entity_in_reference);
            if (!integer_constant_expression_p(ncond))
              gen_context_recurse(ncond, &i, reference_domain, gen_true2, replace_sender_entity_by_receiver_entity_in_reference);
            if (!integer_constant_expression_p(nincr))
              gen_context_recurse(nincr, &i, reference_domain, gen_true2, replace_sender_entity_by_receiver_entity_in_reference);
            if (need_more_com) {
              //TODO modify AST if dynamic
              //add more send/receive com
              pips_internal_error("some variables do not exist on receive cluster. Need to send them.\n");
            }

            new_statement = make_forloop_statement(
                ninit,
                ncond,
                nincr,
                receive_statement);
            ctx_set_receive_statement(ctx, new_statement, i);
            //new_statement = statement_undefined;
            break;
          }
          case is_instruction_call:
          //{
          //  break;
          //}
          case is_instruction_unstructured:
          case is_instruction_multitest:
          case is_instruction_goto:
          case is_instruction_expression:
            pips_internal_error("This case never happen? tag=%d\n", instruction_tag(statement_instruction(st)));
            break;
          default:
            pips_internal_error("This tag doesn't exist: %d\n", instruction_tag(statement_instruction(st)));
            break;
          }
        }
      }
    }
  }
  pips_debug(5, "end\n");
}



static statement make_mpi_conversion(entity module, statement module_statement) {
  ifdebug(2) {
    pips_debug(2, "begin\n");
    pips_debug(2, "statement with : \n");
    print_statement(module_statement);
  }
  statement new_module_statement = make_empty_block_statement();


  if (statement_sequence_p(module_statement)) {
    int nbr_copy = get_int_property(MPI_GENERATION_NBR_CLUSTER);
    ctx_conv_t ctx;
    ctx = conv_make_ctx(module, nbr_copy);
    sequence seq = statement_sequence(module_statement);
    list stats = sequence_statements(seq);

    //0. init the environement
    initilization(new_module_statement , ctx);

    //1. Work task by task
    //   Modify the control flow graph
    //   To add if (rank==x) ...
    FOREACH(STATEMENT, s, stats) {
      if (declaration_statement_p(s)) {
        statement new_decl = copy_statement(s);
        insert_statement_no_matter_what(new_module_statement, new_decl, false);
        //No need?
        //statement_declarations(new_module_statement) = gen_append(statement_declarations(new_module_statement), statement_declarations(new_decl));
      }
      else if (return_statement_p(s)) {
        ctx_set_return_statement(&ctx, s);
      }
      else if (statement_sequence_p(s)) {
        ctx_set_statement_work_on(&ctx, s);


        gen_context_multi_recurse(ctx_get_statement_work_on(ctx), &ctx
//        gen_context_recurse(ctx_get_statement_work_on(ctx), &ctx
            , statement_domain, search_copy_communication, make_send_receive_conversion
            , sequence_domain, sequence_working_false, gen_core /*gen_null*/
            , test_domain, test_working_false, gen_core /*gen_null*/
//            , loop_domain, gen_true, gen_true
//            , whileloop_domain, gen_true, gen_true
//            , forloop_domain, gen_true, gen_true
//            //, call_domain, gen_true, gen_true             // to detect copy for communication statement done in statement_domaine case
//            //, multitest_domain, gen_true, gen_true        // don't exist in PIPS yet
//            //, unstructured_domain, gen_true, gen_true     // never happens? bug case?
//            //, expression_domain, gen_true, gen_true
            , NULL
            );

//        gen_context_recurse(ctx_get_statement_work_on(ctx), &ctx, statement_domain, gen_true, make_send_conversion);
//        gen_context_recurse(ctx_get_statement_work_on(ctx), &ctx, statement_domain, gen_true, make_receive_conversion);

        insert_statement(new_module_statement , ctx_generate_new_statement_cluster_dependant(ctx), false);
//        free_statement(s);
//        s = status_undefined;
//        print_statement(new_module_statement );
      }
      else {
        print_statement(s);
        pips_internal_error("This case never happen?\n");
      }
    }

    //2. close the environement
    finalization(new_module_statement , ctx);

    conv_free_ctx(&ctx);
    free_statement(module_statement);
  } else {
    free_statement(new_module_statement);
    pips_internal_error("The statement must be the module statement (a sequence of instruction).\n");
    new_module_statement = module_statement;
  }

  ifdebug(2) {
    pips_debug(2, "statement with : \n");
    print_statement(new_module_statement);
    pips_debug(2, "end\n");
  }
  return new_module_statement ;
}


/**
 * PIPS pass
 */
bool mpi_conversion(const char* module_name) {
  entity module;
  statement module_statement;
  bool good_result_p = true;

  debug_on("MPI_GENERATION_DEBUG_LEVEL");
  pips_debug(1, "begin\n");

  //-- configure environment --//
  set_current_module_entity(module_name_to_entity(module_name));
  module = get_current_module_entity();

  set_current_module_statement( (statement)
      db_get_memory_resource(DBR_CODE, module_name, true) );
  module_statement = get_current_module_statement();

  pips_assert("Statement should be OK before...",
      statement_consistent_p(module_statement));

  set_ordering_to_statement(module_statement);

  //-- get dependencies --//
//  if(use_points_to) {
//    set_pointer_info_kind(with_points_to); //enough?
//  }
  set_parallel_task_mapping((statement_task)
      db_get_memory_resource(DBR_TASK, module_name, true));

  //-- Make the job -- //
  module_statement = make_mpi_conversion(module, module_statement);

  pips_assert("Statement should be OK after...",
      statement_consistent_p(module_statement));

  // Removed useless block created by the insert_statement
  unspaghettify_statement(module_statement);

  /* Reorder the module, because some statements have been added.
     Well, the order on the remaining statements should be the same,
     but by reordering the statements, the number are consecutive. Just
     for pretty print... :-) */
  module_reorder(module_statement);

  pips_assert("Statement should be OK after...",
      statement_consistent_p(module_statement));

  //-- Save modified code to database --//
  DB_PUT_MEMORY_RESOURCE(DBR_CODE, strdup(module_name), module_statement);

  reset_ordering_to_statement();
  reset_current_module_statement();
  reset_current_module_entity();
  reset_parallel_task_mapping();

  pips_debug(1, "end\n");
  debug_off();

  return (good_result_p);
}

