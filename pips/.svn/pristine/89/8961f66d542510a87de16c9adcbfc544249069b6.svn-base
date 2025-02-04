#! /usr/bin/env python

from __future__ import print_function

import re
import sys

usage = 'usage: pipsmakerc-extract-loop-phase.py rc-file.tex properties.rc pipsdep.rc'

if len(sys.argv) < 4:
    print(usage)
    sys.exit(1)

texfile = sys.argv[1]

# Read propdep file and convert it into a map.
pipsdep = {}
for line in open(sys.argv[3]):
    m = re.match(r'(.*?):\s*(.*)', line)
    p = m.group(1)
    deps = []
    if m.lastindex == 2:
        deps = re.split(r' ', m.group(2))
        deps = deps[0:len(deps) - 1]
    deps = [x.lower() for x in deps]
    pipsdep[p] = deps

# Read properties into a string
pipsprops = {}
for line in open(sys.argv[2]):
    m = re.match(r'\s*(.*?)\s+(.*)', line)
    d = m.group(2)
    if d in ('TRUE', 'FALSE'):
        d = d.capitalize()
    pipsprops[m.group(1)] = d

# Read input tex file into a string
rc = open(texfile).read()


def print_python_method(name, doc):  # todo: param doc never used
    """"""
    has_loop_label = False

    if name in pipsdep and len(pipsdep[name]) > 0:
        props = []  # todo: variable never used
        for prop in pipsdep[name]:
            if prop == 'loop_label':
                has_loop_label = True
                break
    if has_loop_label:
        print('"' + name + '",')


# Parse string documentation
doc_strings = re.findall(r'\\begin{PipsPass\}(.*?)\\end{PipsPass\}', rc, flags=re.M | re.S)

print('static char *loop_phases[] = {')
for dstr in doc_strings:
    m = re.match(r'{([^\}]+)\}[\n]+(.*)', dstr, flags=re.M | re.S)
    print_python_method(m.group(1), m.group(2))
print("0\n};")
