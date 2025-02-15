#!/usr/bin/env python
#
# environement variable used :
# PIPS_WORKSPACE : directory where to save the workspace (needed)
# PIPS_WORKINGDIR : directory to work in (usually pips-make working directory, default '.')
# PIPS_CC : compiler to use (default gcc)
# PIPS_LD : linker to use (default gcc)
# PIPS_AR : archiver to use (default ar)

from __future__ import print_function

import difflib
import fnmatch
import os
import pickle
import shutil
import subprocess
import sys


def getDirectory():
    """
    Returns PIPS Workspace directory ($PIPS_WORKSPACE)
    """
    return os.getenv('PIPS_WORKSPACE')


def getPipsWD():
    """
    Returns PIPS Working directory ($PIPS_WORKINGDIR)
    """
    return os.getenv('PIPS_WORKINGDIR', '.')


def optRemove(argv, op, hasArg=False):
    """
    Remove any instance of option op in argv, removing op argument if hasArg is set
    """
    for opt in argv:
        if opt == op:
            index = argv.index(opt)
            del argv[index]
            if hasArg:
                del argv[index]


def ofile(argv):
    """
    Return the output file (identified by option -o) in gcc arguments
    """
    for opt in argv:
        if opt == '-o':
            index = argv.index(opt)
            return argv[index + 1]
    return ''


def extractCPPflags(argv):
    """
    Extract and remove preprocessor flags from argv, and then return them
    """
    flags = []
    for opt in argv:
        if opt.startswith('-D') or opt.startswith('-I'):
            flags += [opt]
            argv.remove(opt)
    return flags


class Object(object):
    """
    Preprocessed C source file descriptor
    """

    # If a file is compiled more than one and the preprocessed output is different, these information are filled
    # and then retrieved by _CCWorkspace.addObject which issue a warning in the compilation log.
    equ_c_name = ''  # Relative path of the conflicting source file
    equ_diff = ''  # Unified diff result

    def __init__(self, argv):
        """
        Construct a new Object given GCC arguments
        """
        self.argv = argv  # Always useful to know it

        # --- Retrieve command line information ---
        cflags = argv

        # Retrieve source file from arguments
        for opt in cflags:
            if fnmatch.fnmatch(opt, '*.c'):
                cflags.remove(opt)
                sourcefile = opt
        self.cname = os.path.relpath(sourcefile, getPipsWD())

        # Retrieve object file name
        objfile = ofile(cflags)
        if objfile == '':
            objfile = os.path.splitext(sourcefile)[0] + '.o'
        self.objectfile = os.path.relpath(objfile, getPipsWD())

        # Clean cflags from some unused flags
        optRemove(cflags, '-o', True)
        optRemove(cflags, '-MF', True)
        optRemove(cflags, '-c')
        self.cflags = cflags

        # Build output dir for preprocessed source file
        dir = os.path.join(getDirectory(), os.path.dirname(self.cname))
        if not os.path.isdir(dir):
            os.makedirs(dir)

        # Sometimes, source file are compiled more than once (often, with and without -fPIC option)
        # When this happened, we save preprocessed output to a temporary name, next we make a diff
        # before replacing the old preprocessed output.
        outfile = os.path.join(getDirectory(), self.cname)
        if os.path.exists(outfile):
            outcpp = os.path.join(os.path.dirname(outfile), 'tmp.' + os.path.basename(outfile))
        else:
            outcpp = outfile

        # Prepare a call to CC to get preprocessed source file
        CC = os.getenv('PIPS_CC', 'gcc')
        cmd = [CC, '-U__GNUC__', '-E'] + cflags + ['-c', '-o', outcpp, sourcefile]

        # Call CC
        sp = subprocess.Popen(cmd)
        exitcode = sp.wait()

        if exitcode:
            sys.exit(exitcode)  # Should never happen because the source file should have been already compiled successfully.

        if outcpp != outfile:  # If there was already a source file
            if not cmp(outfile, outcpp):  # todo: replace cmp
                # If there is no difference between preprocessed files, we do nothing
                # else, we save some information  (name of the file and Diff) which will
                # be handled in _CCWorkspace.addObject (because the Object have no information
                # about other compilation unit, it's better to do a search in _CCWorkspace.addObject).
                Object.equ_c_name = self.cname
                s1 = open(outcpp).readlines()
                s2 = open(outfile).readlines()
                Object.equ_diff = difflib.unified_diff(s1, s2, outcpp, outfile)
            shutil.move(outcpp, outfile)

    def getCName(self):
        """
        Return the relative path of the source file
        """
        return self.cname

    def getOutputFilename(self):
        """
        Return the relative path of the output object file
        """
        return self.objectfile

    def getIName(self):
        """
        Return the relative path of the intermediate .i file
        """
        return os.path.splitext(self.cname)[0] + ".i"

    def compile(self, dir, outdir):
        """
        Compile file relative to dir and creates the output relatively to outdir
        """

        # The compiler never preprocess .i files. We copy our .c file to .i before compiling them to avoid
        # the preprocessor step
        ifile = os.path.splitext(self.cname)[0] + ".i"
        ifile = os.path.join(dir, ifile)
        cfile = os.path.join(dir, self.cname)

        # Prepare call to CC
        outfile = os.path.join(outdir, self.getOutputFilename())
        cmd = [os.getenv('PIPS_CC', 'gcc')]
        cmd += self.cflags + ['-c', ifile, '-o', outfile]

        # Move .c to .i file
        shutil.copy(cfile, ifile)

        # Create output directory
        outdir = os.path.dirname(outfile)
        if not os.path.isdir(outdir):
            os.makedirs(outdir)

        # Call CC
        print(' '.join(cmd))
        sp = subprocess.Popen(cmd)
        exitcode = sp.wait()
        if exitcode != 0:
            sys.exit(exitcode)

        os.remove(ifile)

    def __str__(self):
        return 'cflags ' + ' '.join(self.cflags) + '\ncname ' + self.cname


class LinkerObject(object):
    """
    Linker step descriptor
    """

    def __init__(self, args):
        """
        Construct a linker Object using linker args
        """
        self.args = []
        self.files = []

        # Retrieve output file name
        self.output = os.path.relpath(ofile(args), getPipsWD())
        optRemove(args, '-o', True)

        # Split arguments between input files and other arguments
        for arg in args:
            if os.path.isfile(arg):
                arg = os.path.relpath(arg, getPipsWD())
                self.files.append(arg)
            else:
                self.args.append(arg)

    def getOutputFilename(self):
        """
        Return the relative path to the output binary
        """
        return self.output

    def link(self, dir, outdir):
        """
        Link files relative to dir and creates the output relatively to outdir
        """
        LD = os.getenv('PIPS_CC', 'gcc')
        LD = os.getenv('PIPS_LD', LD)

        # Output binary
        outfile = os.path.join(outdir, self.output)

        # Create output directory
        outfiledir = os.path.dirname(outfile)
        if not os.path.isdir(outfiledir):
            os.makedirs(outfiledir)

        # Prepare call to LD
        cmd = [LD] + self.args + ['-o', outfile] + [os.path.join(outdir, x) for x in self.files]

        # Call LD
        print(' '.join(cmd))
        sp = subprocess.Popen(cmd)
        exitcode = sp.wait()
        if exitcode != 0:
            sys.exit(exitcode)


class ArObject(object):
    """
    ar step descriptor
    """

    def __init__(self, args):
        """
        Initialise archiver object using options from ar
        """

        self.args = []
        self.files = []
        self.output = ''
        self.cwd = os.path.relpath(os.getcwd(),
                                   getPipsWD())  # Remember the current directory because ar extract file there

        # We loop over each arg. If arg isn't a file and it is the first file in the list, then it is the output file
        # Else if it is a file, it's an input file
        # If argument is not a file, it's marked as a simple argument
        for arg in args:
            if os.path.isfile(arg):
                arg = os.path.relpath(arg, getPipsWD())
                if self.output == '':
                    self.output = arg
                else:
                    self.files.append(arg)
            else:
                self.args.append(arg)

    def getOutputFilename(self):
        """
        Return output archive relative path
        """
        return self.output;

    def link(self, dir, outdir):
        """"""
        outdir = os.path.abspath(outdir)
        ar = os.getenv('PIPS_AR', 'ar')

        outfile = os.path.join(outdir, self.output)

        # Create output directory
        outfiledir = os.path.dirname(outfile)
        if not os.path.isdir(outfiledir):
            os.makedirs(outfiledir)

        # Prepare call to AR
        cmd = [ar] + self.args + [outfile] + [os.path.join(outdir, x) for x in self.files]

        p = os.getcwd()
        if not os.path.exists(os.path.join(outdir, self.cwd)):
            os.makedirs(os.path.join(outdir, self.cwd))
        os.chdir(os.path.join(outdir, self.cwd))
        # Call CC
        print(' '.join(cmd))
        sp = subprocess.Popen(cmd)
        exitcode = sp.wait()
        os.chdir(p)
        if exitcode != 0:
            sys.exit(exitcode)


class _CCWorkspace(object):
    """"""

    def __init__(self):
        """"""
        self.objects = []

    def addObject(self, obj):
        """"""
        self.objects += [obj]
        if isinstance(obj, Object) and Object.equ_c_name != '':
            pipsgccLog.write(
                'Warning : file %s compiled twice or more with differents preprocessor flags :\n' % Object.equ_c_name)
            for x in self.objects:
                if isinstance(x, Object) and x.getCName() == Object.equ_c_name:
                    pipsgccLog.write(' '.join(x.argv) + '\n')
            Object.equ_c_name = ''
            pipsgccLog.write('Diff is :\n%s\n' % Object.equ_diff)


class CCWorkspace(object):
    """"""

    def __init__(self, ws, sourceList, **kargs):
        """"""
        dir = sourceList[0]
        del sourceList[0]

        if not os.path.isdir(dir):
            raise ValueError("'" + dir + "' is not a directory")
        filename = os.path.join(dir, 'workspace')
        if not os.path.isfile(filename):
            raise ValueError("'" + filename + "' doesn't exist")

        wsfile = open(filename)
        ws = pickle.load(wsfile)

        self.objects = ws.objects
        self.dir = dir

        for obj in self.objects:
            if isinstance(obj, Object):
                sourceList.append(os.path.join(dir, obj.getCName()))
        sourceList = list(set(sourceList))  # Remove duplicates

    # pyps.workspace.__init__(self, sourceList)

    def compile(self, CC='gcc', CFLAGS='', LDFLAGS='', link=True, outdir='.', outfile='', extrafiles=[]):
        """
        Reimplements workspace.compile
        """
        if not os.path.isdir(outdir):
            raise ValueError("'" + outdir + "' is not a directory")
        for obj in self.objects:
            if isinstance(obj, Object):
                obj.compile(self.dir, outdir)
            else:
                obj.link(self.dir, outdir)


# File log (in $PIPS_WORKSPACE/make.log or ./make.log).
# It is used because sometimes gcc output is redirected to /dev/null.

if getDirectory() is not None:
    if not os.path.exists(getDirectory()):
        os.makedirs(getDirectory())
    pipsgccLog = open(os.path.join(getDirectory(), 'make.log'), 'a')
else:
    pipsgccLog = open('make.log', 'a')
