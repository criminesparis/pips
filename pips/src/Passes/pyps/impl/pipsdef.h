/* Header automatically inserted by PYPS for defining MAX, MIN, MOD and others
 *
 * Notes:
 *
 * 1. This may not be the behavior intended by the programmer.
 *
 * 2. MIN and MAX do not always have only two arguments.
 *
 * To be reviewed when intrinsics are dealt better in PIPS (FI, 19 April 2015)
 */
#ifndef __PIPS__ /* for PIPS re entrance */
#ifndef MAX0
# define MAX0(a, b) ((a) > (b) ? (a) : (b))
#endif

#ifndef MAX
# define MAX(a, b) ((a) > (b) ? (a) : (b))
#endif

#ifndef pips_max
# define pips_max(n, a, b) ((a) > (b) ? (a) : (b))
#endif

#ifndef MIN
# define MIN(a, b) ((a) < (b) ? (a) : (b))
#endif

#ifndef pips_min
# define pips_min(n, a, b) ((a) > (b) ? (a) : (b))
#endif

#ifndef MOD
# define MOD(a, b) ((a) % (b))
#endif

#ifndef DBLE
# define DBLE(a) ((double)(a))
#endif

#ifndef INT
# define INT(a) ((int)(a))
#endif

#ifdef WITH_TRIGO
#  include <math.h>
#  ifndef COS
#    define COS(a) (cos(a))
#  endif

#  ifndef SIN
#    define SIN(a) (sin(a))
#  endif
#endif
#endif
