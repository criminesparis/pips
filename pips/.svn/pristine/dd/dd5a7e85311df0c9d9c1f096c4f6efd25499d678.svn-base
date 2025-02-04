/* PIPS run-time support for C code generation
 *
 * Low-level functions used by the PIPS code generation algorithms:
 * * pips_min(int x1, in x2, int x3...)
 * * pips_max(int x1, int x2, in x3...)
 * * idiv(x,y)
 * * ...
 *
 * Some of these overloaded functions are available as intrinsics MIN
 * and MAX.
 *
 * For pips_min() and pips_max(), the first argument is the number of
 * effective arguments, the second argument is the first effective
 * argument and other arguments are passed as varargs. For instance:
 *
 * pips_min(5, 1, 2, 3, 4, 5);
 *
 * Initially, the source code for these two operators has been available in
 * validation/Hyperplane/run_time.src/pips_run_time.c
 */

//#define PIPS_C_MIN_OPERATOR_NAME        "pips_min"
//#define PIPS_C_MAX_OPERATOR_NAME        "pips_max"

// Old implementation inefficient for execution time, but can have "infinite" number of arguments
// #include <stdarg.h>
// 
// int pips_min(int count, int first,  ...)
// {
//     va_list ap;
//     int j;
//     int min = first;
//     va_start(ap, first);
//     for(j=0; j<count-1; j++) {
//         int next =va_arg(ap, int);
//         min = min<next? min : next;
//     }
//     va_end(ap);
//     return min;
// }
// 
// int pips_max(int count, int first,  ...)
// {
//     va_list ap;
//     int j;
//     int max = first;
//     va_start(ap, first);
//     for(j=0; j<count; j++) {
//         int next =va_arg(ap, int);
//         max = max>next? max : next;
//     }
//     va_end(ap);
//     return max;
// }


/* Alternative implementation provided by Fabien Coelho for up to 6 arguments.
 * Some improve by NL to try to make them more generic.
 * There is a ternaire test version (commented) and a if/then/else test version.
 * inline to be considered need to be compiled with minimum of -O1 or -Ofast
 *   -O0 or without -O no inlining is done
 * It is supposed to be as efficient as Fortran MIN and MAX intrinsics
 */

// type of pips_min/pips_max functions
#define mytype float

#define pips_min(n, ...)                    \
  pips_min_ ## n(__VA_ARGS__)
#define pips_max(n, ...)                    \
  pips_max_ ## n(__VA_ARGS__)

// To generate a list of argument with mytype, up to 6 args
#define argument_var1(mytype, a, ...) mytype a
#define argument_var2(mytype, a, ...) mytype a, argument_var1(mytype, __VA_ARGS__)
#define argument_var3(mytype, a, ...) mytype a, argument_var2(mytype, __VA_ARGS__)
#define argument_var4(mytype, a, ...) mytype a, argument_var3(mytype, __VA_ARGS__)
#define argument_var5(mytype, a, ...) mytype a, argument_var4(mytype, __VA_ARGS__)
#define argument_var6(mytype, a, ...) mytype a, argument_var5(mytype, __VA_ARGS__)

//definition of the body of pips_min and pips_max function
// ternaire version
// #define pips_min_return(mytype, m, a1, a2, ...) \
//   return a1 < a2 ? pips_min(m, a1, __VA_ARGS__) :  pips_min(m, a2, __VA_ARGS__);
// if/then/else version
#define pips_min_return(mytype, m, a1, a2, ...) \
  {                                     \
    mytype r;                           \
    if (a1<a2)                          \
      r=pips_min(m, a1, __VA_ARGS__);   \
    else                                \
      r=pips_min(m, a2, __VA_ARGS__);   \
    return r;                           \
  }
// #define pips_max_return(mytype, m, a1, a2, ...) \
//   return a1 > a2 ? pips_max(m, a1, __VA_ARGS__) :  pips_max(m, a2, __VA_ARGS__);
#define pips_max_return(mytype, m, a1, a2, ...) \
  {                                     \
    mytype r;                           \
    if (a1>a2)                          \
      r=pips_max(m, a1, __VA_ARGS__);   \
    else                                \
      r=pips_max(m, a2, __VA_ARGS__);   \
    return r;                           \
  }

//declaration of pips_min_n function, n is the number of variables to compare
// m must be n-1 value
#define pips_min_decl(mytype, n, m, ...) \
  __inline__ mytype pips_min_ ## n(argument_var ## n(mytype, __VA_ARGS__)) { \
    pips_min_return(mytype, m, __VA_ARGS__) \
  }
#define pips_max_decl(mytype, n, m, ...) \
  __inline__ mytype pips_max_ ## n(argument_var ## n(mytype, __VA_ARGS__)) { \
    pips_max_return(mytype, m, __VA_ARGS__) \
  }

// X macro to declare pips_min_n/pips_max_n functions
#define X_pips_decl(mytype, _) \
  _(mytype, 3, 2, i1, i2, i3) \
  _(mytype, 4, 3, i1, i2, i3, i4) \
  _(mytype, 5, 4, i1, i2, i3, i4, i5) \
  _(mytype, 6, 5, i1, i2, i3, i4, i5, i6)

//The basic pips_min_2/pips_max_2 must be manually declared
// __inline__ mytype pips_min_2(mytype i1, mytype i2)
// {
//   return i1 < i2? i1: i2;
// }
__inline__ mytype pips_min_2(mytype i1, mytype i2)
{
  mytype r;
  if (i1<i2)
    r=i1;
  else
    r=i2;
  return r;
}
// __inline__ mytype pips_max_2(mytype i1, mytype i2)
// {
//   return i1 > i2? i1: i2;
// }
__inline__ mytype pips_max_2(mytype i1, mytype i2)
{
  mytype r;
  if (i1>i2)
    r=i1;
  else
    r=i2;
  return r;
}

// declaration of pips_min_n functions
X_pips_decl(mytype, pips_min_decl)
// declaration of pips_max_n functions
X_pips_decl(mytype, pips_max_decl)
