import os

import pyps

cfile = r"""#ifndef PYPS_INTRINSICS_H
#define PYPS_INTRINSICS_H

#ifndef MOD
# define MOD(a, b) ((a) % (b))
#endif

#ifndef MIN
# define MIN(a, b) ( (a) < (b) ? (a) : (b) )
#endif

#ifndef pips_min
# define pips_min(n, a, b) ( (a) < (b) ? (a) : (b) )
#endif

#ifndef MAX
# define MAX(a, b) ( (a) > (b) ? (a) : (b) )
#endif

#ifndef pips_max
# define pips_max(n, a, b) ( (a) > (b) ? (a) : (b) )
#endif

#ifndef MAX0
# define MAX0(a, b) ((a)>(b)?(a):(b))
#endif

#endif //PYPS_INTRINSICS_H"""


# When going to compile, edit all the c files to add the macros corresponding to fortran symbols

class workspace(pyps.workspace):
    """"""

    def goingToRunWith(self, files, outdir):
        """
        Creating the file containing the macros
        """
        intrpath = '_pyps_intr.h'
        with open(intrpath, 'w') as f:
            f.write(cfile)
        # Editing the source files to add the include in them
        abspath = os.path.abspath(intrpath)
        for file in files:
            read_data = open(file).read()
            # Don't put the include more than once
            if read_data.find('\n#include "{0}"\n'.format(abspath)) != -1:
                continue
            with open(file, 'w') as f:
                f.write('/* Header automatically inserted by PYPS*/\n#include "{0}"\n\n'.format(abspath))
                f.write(read_data)
        super(workspace, self).goingToRunWith(files, outdir)
