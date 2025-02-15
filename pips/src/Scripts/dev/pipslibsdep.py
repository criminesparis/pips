#!/usr/bin/env python
#
# $Id: pipslibsdep.py 23561 2019-07-04 16:34:07Z daverio $
#
# Copyright 1989-2016 MINES ParisTech
#
# This file is part of PIPS.
#
# PIPS is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# any later version.
#
# PIPS is distributed in the hope that it will be useful, but WITHOUT ANY
# WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.
#
# See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with PIPS.  If not, see <http://www.gnu.org/licenses/>.
#

# Serge Guelton
# this quick'n dirty script generates on standard output a dot view of dependencies betwwen libraries
# it also prints on stderr a list of libraries that are uselessly #included by others
# parameters can be given: they are library names that must appear on the dependency check / view.
# If none is given, all libraries are considered
# you must manually set generate_dot_file to true if you want to activate this feature

from __future__ import print_function

import os
import re
import sys
from functools import reduce
from optparse import OptionParser
from subprocess import Popen, PIPE

parser = OptionParser()
parser.add_option('-s', '--srcdir',
                  action='store', type='string', dest='srcdir',
                  metavar='<dir>', help='use <dir> as top_srcdir dir')

parser.add_option('-b', '--builddir',
                  action='store', type='string', dest='builddir',
                  metavar='<dir>', help='use <dir> as top_builddir dir')

parser.add_option('-l', '--lib',
                  action='store', type='string', dest='libname',
                  metavar='<libname>', help='only inspect <libname> instead of all libs')

parser.add_option('-d', '--dot',
                  action='store', type='string', dest='dotfile',
                  metavar='<file>', help='generate dot description of dependencies in <file>')
parser.add_option('-v', '--verbose',
                  action='count', dest='verbose', default=0,
                  help='make lots of noise (cumulative)')

(options, args) = parser.parse_args()

if not options.srcdir or not options.builddir:
    parser.error('options --srcdir and --builddir are mandatory')

libdir = os.path.join(options.builddir, 'src', 'Libs')
srcdir = os.path.join(options.srcdir, 'src', 'Libs')
if not os.path.isfile(os.path.join(srcdir, 'syntax', 'syntax-local.h')):
    parser.error('options --srcdir does not point to pips source dir')
if not os.path.isfile(os.path.join(libdir, 'syntax', 'syntax.h')):
    parser.error('options --builddir does not point to pips build dir')

print("""\
=========================
PIPS include checker
by serge guelton o(^_-)O
=========================\
""")


def log(lvl, *msg):
    """"""
    if lvl <= options.verbose:
        print(' '.join(map(str, msg)))


def dotname(name):
    """"""
    return name.replace('-', '_')


class Sym(object):
    """"""

    def __init__(self, name):
        """"""
        self.name = name

    def undefined(self):
        """"""
        m = re.match(r'^ +U (\w+)$', self.name)
        return m.groups()[0] if m else None

    def defined(self):
        """"""
        m = re.match(r'^[0123456789abcdef]+ +[TDB] (\w+)$', self.name)
        return m.groups()[0] if m else None


class Library(object):
    """"""

    def __init__(self, name, path):
        """"""
        self.name = name
        self.path = path
        self.objs = []
        self.used_symbols = {}
        self.defined_symbols = {}
        self.used_libraries = {}

    def objects(self):
        """"""
        if not self.objs:
            objs_dir = os.path.join(self.path, '.libs')
            if not os.path.isdir(objs_dir):
                raise RuntimeError('object files not built in ' + self.name)
            objs = [o for o in os.listdir(objs_dir) if re.match(r'.*\.o$', o)]
            if not objs:
                raise RuntimeError('object files not built in ' + self.name)
            self.objs = [os.path.join(objs_dir, x) for x in objs]
        return self.objs

    def compute_symbols(self):
        """"""
        log(1, 'computing symbols for', self.name)
        for obj in self.objects():
            log(2, 'creating', self.name, 'lib with entry', os.path.basename(obj))
            self.used_libraries[os.path.basename(obj)] = set()
            cmd = ['nm', obj]
            sp = Popen(cmd, stdout=PIPE)
            sp.wait()
            for symbol in sp.stdout.readlines():
                s = Sym(symbol)
                m = s.undefined()
                if m:
                    log(2, m, 'used by', os.path.basename(obj), 'in', self.name)
                    if m not in lib.used_symbols:
                        lib.used_symbols[m] = set()
                    lib.used_symbols[m].add(os.path.basename(obj))
                else:
                    m = s.defined()
                    if m:
                        log(2, m, 'defined by', os.path.basename(obj), 'in', self.name)
                        lib.defined_symbols[m] = os.path.basename(obj)

    def compute_deps(self, alllibs):
        """"""
        log(1, 'computing dependencies for', self.name)
        for (sym, objs) in self.used_symbols.items():
            log(2, 'checking symbol', sym, 'in objects', objs, 'and lib', self.name)
            for otherlib in alllibs:
                if otherlib != self:
                    if sym in otherlib.defined_symbols.keys():
                        log(2, sym, 'from', otherlib.name, 'used in', self.name, 'by', objs)
                        for obj in objs:
                            self.used_libraries[obj].add(otherlib.name)
        return self.used_libraries

    def check_includes(self, alllibs):
        """"""
        depsdir = os.path.join(srcdir, self.name)
        err = {}
        if not os.path.isdir(depsdir):
            raise RuntimeError('dep files not built in ' + depsdir)
        for d in os.listdir(depsdir):
            log(2, 'checking includes for', self.name, ':', d)
            err[d] = set()
            if re.match(r'.*\.[cly]$', d):
                for line in open(os.path.join(depsdir, d)):
                    m = re.match(r'#include\s*"(\w+)\.h"', line)
                    if m:  # d depends on (m.groups()[0])
                        deplib = m.groups()[0]
                        if deplib in (x.name for x in alllibs) and deplib != self.name:
                            obj = d[:-1] + 'o'
                            if obj in self.used_libraries and deplib not in self.used_libraries[obj]:
                                err[d].add(deplib)
        return err

    def dotstr(self, only=None):
        """"""
        fmt = dotname(self.name) + ' [label="%s"]\n' % self.name
        if not only or only == self.name:
            for d in reduce(lambda x, y: x | y, self.used_libraries.values(), set()):
                fmt += dotname(d) + ' -> ' + dotname(self.name) + '\n'
        return fmt


libraries = [Library(d, os.path.join(libdir, d))
             for d in os.listdir(libdir)
             if os.path.isdir(os.path.join(libdir, d)) and os.path.isfile(os.path.join(libdir, d, 'Makefile'))]

for lib in libraries:
    lib.compute_symbols()

for lib in libraries:
    lib.compute_deps(libraries)

check_result = 0
for lib in libraries:
    if not options.libname or lib.name == options.libname:
        err = lib.check_includes(libraries)
        for (k, v) in err.items():
            if v:
                check_result += 1
                print(lib.name, ':', k, ':', ' '.join(v), file=sys.stderr)

# pretty print dot file if required
if options.dotfile:
    with open(options.dotfile, 'w') as fd:
        print('digraph pipslibs {', file=fd)
        if options.libname:
            for lib in libraries:
                print(lib.dotstr(options.libname), file=fd)
        else:
            for lib in libraries:
                print(lib.dotstr(), file=fd)
        print('}', file=fd)

if check_result == 0:
    print('everything ok')
else:
    print(check_result, 'errors')

sys.exit(check_result)
