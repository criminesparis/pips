#!/usr/bin/env python

from __future__ import print_function

import os
import re
import sys
from subprocess import Popen, PIPE

from six import ensure_str


def parse_ops(code, op, f):
    """"""
    matches = re.findall(r'(%%%%%s (")?([a-zA-Z0-9 _./-]+)(")?[:space:]*%%%%)' % op, code)
    retcode = code
    for m in matches:
        retcode = f(retcode, m[0], m[2])
    return retcode


def parse_include(code, org_code, arg):
    """"""
    global _abspath
    hfile = os.path.join(_abspath, arg)
    print('Includes %s...' % hfile, file=sys.stderr)
    hcode = open(hfile).read()
    return code.replace(org_code, hcode)


def parse_gen_header(code, org_code, arg):
    """"""
    global _abspath
    cfile = os.path.join(_abspath, arg)
    print('Generate headers for %s using cproto...' % cfile, file=sys.stderr)
    p = Popen(['cproto', cfile], stdout=PIPE, stderr=PIPE)
    output, errors = map(ensure_str, p.communicate())
    if p.returncode != 0:
        raise RuntimeError('cproto failed with return code %d. stderr says... :\n%s' % (p.returncode, errors))
    return code.replace(org_code, output)


if len(sys.argv) != 2:
    print('Usage: %s path/to/_sac.py' % sys.argv[0], file=sys.stderr)
    sys.exit(1)

_abspath = os.path.abspath(os.path.dirname(sys.argv[0]))  # So that relative paths can be used !

saccode = open(sys.argv[1]).read()

try:
    #  Parse includes
    saccode = parse_ops(saccode, 'include', parse_include)

    # Parse gen_header
    saccode = parse_ops(saccode, 'gen_header', parse_gen_header)

except Exception as e:
    print(e, file=sys.stderr)
    sys.exit(1)

print(saccode)
sys.exit(0)
