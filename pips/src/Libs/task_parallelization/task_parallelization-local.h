#include "task_private.h"

#ifndef _newgen_graph_included
#include "dg.h"

/* Instantiation of the dependence graph: */
typedef dg_arc_label arc_label;
typedef dg_vertex_label vertex_label;
#include "graph.h"
#endif

typedef struct {
  double tlevel;
  double blevel;
  double prio;
  double task_time;
  gen_array_t edge_cost;
  list data;
  bool scheduled;
  int order_sched;
  int cluster;
  int nbclusters;
}annotation;

typedef struct {
  double time;
  list data;
}cluster;

#define MPI_COMM_WORLD_STRING "MPI_COMM_WORLD"

#define MPI_GENERATION_NBR_CLUSTER "MPI_NBR_CLUSTER"
#define MPI_GENERATION_PREFIX "MPI_DUPLICATE_VARIABLE_PREFIX"
//#define MPI_GENERATION_SUFFIX "MPI_DUPLICATE_VARIABLE_SUFFIX"
#define MPI_GENERATION_PRIVATE_VARIABLES_LIST "MPI_PRIVATE_VARIABLES_LIST"
#define MPI_GENERATION_PRIVATE_PARAMETER "MPI_PRIVATE_PARAMETER"

#define COMMENT_VARIABLE_REPLICATION " Generated by Pass VARIABLE_REPLICATION\n"
#define COMMENT_COPY_VARIABLE " Generated by Pass COPY_VARIABLE\n"
#define COMMENT_MPI_CONVERSION " Generated by Pass MPI_CONVERSION\n"
