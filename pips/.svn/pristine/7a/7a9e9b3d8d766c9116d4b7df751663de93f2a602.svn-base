"""
Pyps toolbox

it contains various utilities used in pyps.
It also hides the internal of pyps in another module,
to make user interface cleaner
"""

from __future__ import print_function

import fileinput
import os
import re

import pypsbase
from pypsconfig import pypsruntime

from six import ensure_binary

guard_begin = 'PIPS include guard begin:'
guard_begin_re = re.compile(r'^// %s (.+) $' % guard_begin)
guard_end = 'PIPS include guard end:'
include_re = re.compile(r'^\s*#\s*include\s*(\S+)\s*.*$')


def mkguard(guard, line):
    """"""
    p = line.rstrip('\r\n').split('//', 1)
    st = '// %s %s \n' % (guard, p[0])
    if len(p) == 2:
        st += '//' + p[1] + '\n'
    return st  # always ends with '\n'


def guardincludes(fname):
    """
    Adds guards around includes.
    """
    for l in fileinput.FileInput([fname], inplace=True):
        is_include = include_re.match(l)
        if is_include:
            print(mkguard(guard_begin, l), end='')  # always ends with '\n'
        print(l, end='')  # always ends with '\n'
        if is_include:
            print(mkguard(guard_end, l), end='')  # always ends with '\n'


def addBeginnning(fname, text):
    """
    Adds a line of text at the beginning of fname
    """
    fi = fileinput.FileInput([fname], inplace=True)
    for l in fi:
        if fi.isfirstline():
            print(text)
        print(l, end='')  # always ends with '\n'
    fi.close()


def unincludes(fname):
    """
    Removes the contents of included files
    """
    inside_include = False
    included = None  # todo: not used?
    end_included = None
    for l in fileinput.FileInput([fname], inplace=True):
        match = guard_begin_re.match(l)
        if match:
            included = match.group(1)
            inside_include = True
            end_included = mkguard(guard_end, included)
            print(included)
            continue
        if l == end_included:
            inside_include = False
            included = None  # todo: not used?
            end_included = None
            continue
        if inside_include:
            continue
        print(l, end='')  # always ends with '\n'


def string2file(string, fname):
    """"""
    with open(fname, 'w') as f:
        f.write(string)
    return fname


def file2string(fname):
    """"""
    return open(fname).read()


def nameToTmpDirName(name):
    """"""
    return '.' + name + '.tmp'


def formatprop(value):
    """"""
    if isinstance(value, bool):
        return str(value).upper()
    elif isinstance(value, str):
        return '"' + value + '"'
    else:
        return str(value)


def capply(ms, phase):
    """
    Concurrently apply a phase to all contained modules
    """
    if len(ms) > 0:
        ms.workspace.cpypips.capply(phase.upper(), [ensure_binary(m.name) for m in ms])


def apply(m, phase, *args, **kwargs):
    """
    Apply a phase to a module. The method pre_phase and post_phase
    of the originate workspace will be called.
    """
    m.workspace.pre_phase(phase, m)
    m.workspace.cpypips.apply(phase.upper(), m.name)
    m.workspace.post_phase(phase, m)


def update_props(passe, props):
    """
    Change a property dictionary by appending the pass name to the property when needed
    """
    for name, val in props.items():
        if name.upper() not in pypsbase.workspace.Props.all:
            del props[name]
            props[str.upper(passe + '_' + name)] = val
            # print('warning, changing ', name, 'into', passe + '_' + name)
    return props


def get_property(ws, name):
    """
    Return property value
    """
    name = name.upper()
    t = type(ws.props.all[name])

    if t == str:
        return ws.cpypips.get_string_property(name)
    elif t == int:
        return ws.cpypips.get_int_property(name)
    elif t == bool:
        return ws.cpypips.get_bool_property(name)
    else:
        raise TypeError('Property type ' + str(t) + ' is not supported')


def get_properties(ws, props):
    """
    Return a list of values of props list
    """
    return [get_property(ws, prop) for prop in props.items()]


def set_property(ws, prop, value):
    """
    Change property value and return the old one
    """
    prop = prop.upper()
    old = get_property(ws, prop)
    if value is None:
        return old
    val = formatprop(value)
    ws.cpypips.set_property(prop.upper(), val)
    return old


def set_properties(ws, props):
    """
    Set properties based on the dictionary props and returns a dictionary containing the old state
    """
    return {prop: set_property(ws, prop, value) for prop, value in props.items()}


def patchIncludes(s):
    """"""
    if not re.search(r'-I.\s', s) and not re.search(r'-I.$', s):
        s += ' -I.'
    return s


def get_runtimefile(fname, subdir=None, isFile=True):
    """
    Return runtime file path
    """
    searchdirs = [pypsruntime]  # removed "." from the search dir because it leads to complicated situations
    if subdir:
        searchdirs.insert(1, os.path.join(pypsruntime, subdir))
    for d in searchdirs:
        f = os.path.join(d, fname)
        if (isFile and os.path.isfile(f)) or (not isFile and os.path.isdir(f)):
            return f
    raise RuntimeError('Cannot find runtime file : ' + fname + '\nsearch path: ' + ':'.join(searchdirs))


def get_runtimedir(fname, subdir=None):
    """"""
    return get_runtimefile(fname, subdir=subdir, isFile=False)


def gen_compile_command(rep, makefile, outfile, rule, **opts):
    """"""
    # Moved here because of code duplication
    return ['make', '-C', rep, '-f', makefile, 'TARGET=' + outfile] + \
           ['%s=%s' % i for i in opts.items()] + [rule]
