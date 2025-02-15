// $Id: modeling-local.h 23073 2016-03-09 09:51:11Z coelho $

typedef struct
{
  stack  loops_for_call;
  stack loop_indices;
  stack current_stat;
  stack testif;
  gen_array_t nested_loops;
  gen_array_t nested_loop_indices;
  gen_array_t nested_call;
  gen_array_t nested_if;
}
  nest_context_t,
  * nest_context_p;


#define spear_error(...) \
  spear_log_func(CURRENT_FUNCTION, __FILE__, __LINE__, spear_error_log, __VA_ARGS__)

#define spear_warning(...) \
  spear_log_func(CURRENT_FUNCTION, __FILE__, __LINE__, spear_warning_log, __VA_ARGS__)
