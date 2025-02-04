import os
import re
from subprocess import Popen, PIPE

import new  # todo: undefined module?
import pyps


def binary_size(module, maker=pyps.Maker()):
    """
    Workspace extension to provide a binary_size function to each module.

    A call to the binary_size function of a given module attempts to compile the program and then to extract the
    compiled size and the instruction count of the given module using objdump.  The compiled size and the instruction
    count are returned by the function in a tuple. A ValueError exception is thrown if the function is not found in the
    binary (see below). A RuntimeError is thrown when the objdump call failed.

    Be careful. The symbol used by the compiler in the binary object for the given module must be guessed by the
    binary_size function. Given a function "foo", the symbol can be "foo", "foo.", "_foo" or many others forms, thus
    we cannot ensure that this function will work in every situations. A wrong guess can lead to a ValueError exception
    or in a few cases to wrongs results.
    """
    outfile = module.workspace.compile(maker=maker, CFLAGS='-O2')  # we should strip it instead

    ret = __funcsize(module.name, outfile)
    os.unlink(outfile)

    return ret


def __getLinePos(line):
    """"""
    m = re.match(r' *([0-9a-f]+):', line)
    return int(line[m.start(1):m.end(1)], 16)


def __matchSymbol(symbol, dump):
    """"""
    return re.search(r'\n[0-9a-f]+ <' + symbol + r'>:\n', dump)


def __funcsize(func, outfile=''):
    """"""
    args = ['objdump', '-S', outfile]
    objdump = Popen(args, stdout=PIPE)
    if objdump is None:
        raise RuntimeError('objdump call failed.')

    dump = objdump.stdout.read()

    symbol = func + '\\.'
    m = __matchSymbol(symbol, dump)
    if m is None:
        m = __matchSymbol(func, dump)
        if m is None:
            raise ValueError('Function ' + func + ' not found in output file ' + outfile)

    fdump = dump[m.end():len(dump) - 1]
    m = re.search(r'\n\n', fdump)
    fdump = fdump[0:m.start()]

    lines = fdump.split('\n')

    line_count = len(lines)
    size = __getLinePos(lines[len(lines) - 1]) - __getLinePos(lines[0])
    return size, line_count


def func_to_method(func, class_):
    """
    Internal helper function : Adds function func to class class_
    """
    method = new.instancemethod(func, None, class_)
    setattr(class_, func.__name__, method)


# Add binary_size function to pyps.module
func_to_method(binary_size, pyps.module)
