#!/usr/bin/env python

from __future__ import print_function

import os
import pickle
import shutil
import subprocess
import sys
import tempfile

import pyps
from pyps import module
from six.moves import range


class object_code(object):
    """
    Preprocessed c source file descriptor
    """

    def __init__(self, sourcefile, cppflags, cflags):
        """"""
        self.cflags = cflags
        CPP = os.getenv('CPP', 'cpp')
        cmd = [CPP, '-U__GNUC__'] + cppflags + [sourcefile]  # todo: check hard-coded option -U__GNUC__?
        # print('# running', cmd)
        sp = subprocess.Popen(cmd, stdout=subprocess.PIPE)
        sp.wait()
        self.code = sp.stdout.read()
        self.cname = sourcefile.replace(os.sep, '__')

    def set_cname(self, cname):
        """"""
        self.cname = cname
        for op in self.cflags:
            if op == '-c':
                i = self.cflags.index(op)
                self.cflags[i + 1] = self.cname
                break

    def dump_to_c(self, in_dir):
        """"""
        self.set_cname(in_dir + os.sep + self.cname)
        with open(self.cname, 'wb') as cfile:  # Python 3: we write bytes, not unicode
            cfile.write(self.code)


def ofile(argv):
    """"""
    for opt in argv[1:]:
        if opt == '-o':
            index = argv.index(opt)
            return argv[index + 1]
    return ''


def cppflags(argv):
    """"""
    flags = []
    for opt in argv[1:]:
        if opt.startswith('-D') or opt.startswith('-I'):
            flags += [opt]
            argv.remove(opt)
    return flags


class pipscc:
    """
    Modular pips compiler front-end
    """

    def __init__(self, argv):
        """
        Create a pips compiler instance from argv
        """
        self.argv = argv
        self.is_ld = len(self.gather_c_files()) == 0

    def run(self):
        """
        Run the compilation
        """
        if not self.is_ld:
            self.pipscpp()
        else:
            self.pipsld()

    def pipscpp(self):
        """
        Simulate the behavior of the c preprocessor
        """
        # parse command line
        CPPFLAGS = cppflags(self.argv)
        OUTFILE = ofile(self.argv)
        # print("# CPPFLAGS: ", CPPFLAGS)
        cpp_and_linking = len([f for f in self.argv[1:] if f == '-c']) == 0

        # look for input file
        for opt in self.argv[1:]:
            if not opt.startswith('-') and opt.endswith('.c'):
                if not OUTFILE:
                    OUTFILE = os.path.splitext(os.path.basename(opt))[0] + '.o'
                # generate internal representation of preprocessed code
                args = self.argv[1:]
                if cpp_and_linking: args.insert(0, '-c')
                obj = object_code(opt, CPPFLAGS, args)
                # serialize it
                with open(OUTFILE, 'wb') as newobj:
                    pickle.dump(obj, newobj)
        # print("# OBJ written: ", OUTFILE)
        # check if we should link too
        if cpp_and_linking:
            for i in range(1, len(self.argv)):
                if self.argv[i].endswith('.c'):
                    self.argv[i] = os.path.splitext(self.argv[i])[0] + '.o'
            self.pipsld()

    # that's all folks

    def gather_object_files(self):
        """"""
        return [opt for opt in self.argv[1:]
                if not opt.startswith('-') and opt.endswith('.o')]

    def gather_c_files(self):
        """"""
        return [opt for opt in self.argv[1:]
                if not opt.startswith('-') and opt.endswith('.c')]

    def unpickle(self, WDIR, files):
        """
        Generate a list of unpickled object files from files
        """
        o_files = []
        for ifile in files:
            obj = pickle.load(open(ifile, 'rb'))
            obj.dump_to_c(WDIR)
            obj.oname = ifile
            o_files += [obj]
        return o_files

    def changes(self, ws):
        """
        Apply any change to the workspace, should be overloaded by the user
        """
        for f in ws.fun:
            f.display()
        for c in ws.cu:
            c.display()

    def get_wd(self):
        """
        Selects a working directory for pipscc
        """
        wdir = tempfile.mkdtemp('pipscc')
        # print('# intermediate files generated in', wdir)
        return wdir

    def get_workspace(self, c_files):
        """"""
        return pyps.workspace(*c_files)

    def compile(self, wdir, o_files):
        """"""
        CC = os.getenv('CC', 'gcc')
        for obj in o_files:
            cmd = [CC] + obj.cflags + ['-o', obj.oname]
            # print('# running', cmd)
            sp = subprocess.Popen(cmd)
            sp.wait()

        cmd = [CC] + self.argv[1:]
        # print('# running', cmd)
        sp = subprocess.Popen(cmd)
        exitcode = sp.wait()
        if exitcode:
            shutil.rmtree(wdir)

    def pipsld(self):
        """
        Simulate C linker, all computation is done at link time
        """
        wdir = self.get_wd()

        # gather pickled input files
        input_files = self.gather_object_files()
        if len(input_files) == 0:
            print('pipscc: no input files', file=sys.stderr)
            sys.exit(1)
        else:
            # load pickled input files
            o_files = self.unpickle(wdir, input_files)
            c_files = [o.cname for o in o_files]
            # print('# input files:', c_files)

            # run pips with this informations
            # print('# running pips')
            with self.get_workspace(c_files) as ws:
                # add extra operations
                self.changes(ws)
                # commit changes
                ws.save(rep=wdir)

            # now run the compiler
            self.compile(wdir, o_files)
        shutil.rmtree(wdir)


if __name__ == '__main__':
    thecompiler = pipscc(sys.argv)
    thecompiler.run()
