from __future__ import print_function

import os
import sys

import pyps
import workspace_check


def get_source_file_from_basename(basename, extensions):
    """"""
    for ext in extensions:
        if os.path.isfile(basename + '.' + ext):
            return basename + '.' + ext
    return None


class vworkspace(workspace_check.workspace):
    """
    This workspace is intended to handle some special PIPS validation stuff
    """

    @classmethod
    def get_main_source_file(cls):
        """
        Get the main source file for current script
        """
        file = os.getenv('FILE')
        if file is not None and not os.path.isfile(file):
            print("Error, file %s doesn't exist!" % file, file=sys.stderr)
            file = None

        if file is None:
            # Try to recover source corresponding to script filename
            basename = os.path.splitext(sys.argv[0])[0]
            basename = os.path.basename(basename)  # bold move!
            file = get_source_file_from_basename(basename, ('c', 'f', 'f90', 'f95'))
            if file is None:
                raise RuntimeError('''No source files ! Please define FILE environment 
                                    variable or provide %s.{c,f,f95}''' % basename)
        return file

    def __init__(self, *sources, **kwargs):
        """
        Init a workspace from (optional) sources for validation
        name will be gathered from WSPACE and sources from FILE environment variables
        """
        file = vworkspace.get_main_source_file()

        for f in list(sources):
            if f == file:
                raise RuntimeError('Hum... a validation script must be' +
                                   ' reusable. Thus you should write it without specifying ' + f +
                                   " in the vworkspace() constructor, it's automatically added!!")

        # This workspace is intended to be run with WSPACE and FILE environment variable defined
        wspace = os.getenv('WSPACE')
        if wspace is None:
            wspace = os.path.splitext(file)[0]
            print("WSPACE environment variable isn't defined, will use '%s'" % wspace, file=sys.stderr)

        kwargs.setdefault('deleteOnClose', True)
        kwargs.setdefault('deleteOnCreate', True)
        kwargs.setdefault('name', wspace)

        super(vworkspace, self).__init__(file, *sources, **kwargs)

        def str2bool(v):
            """
            helper to convert a string to a boolean
            """
            return v.lower() in ('yes', 'true', 't', '1')

        self.__should_compile = str2bool(kwargs.setdefault('compile', os.getenv('VALIDATION_COMPILE', '')))
        self.__should_run = str2bool(kwargs.setdefault('run', os.getenv('VALIDATION_RUN', '')))
        # Defined that we will check the output after each phase
        self._enable_check = str2bool(kwargs.setdefault('check', os.getenv('VALIDATION_CHECK', '')))

    def compile_and_run(self, *args, **kwargs):
        """"""
        a_out = self.compile(*args, **kwargs)
        out = ''
        if self.fun.main:
            (rc, out, err) = self.run(a_out)
        else:
            print('** No main() found, cannot executing test case **', file=sys.stderr)
        return out

    def post_phase(self, phase, module):
        """"""
        super(vworkspace, self).post_phase(phase, module)
        # check resulting code after the apply 
        if 'main' in self.fun:
            if self.__should_run:
                print('# Execution after ' + phase)
                print(self.compile_and_run())
            elif self.__should_compile:
                self.compile()


def validate_phases(self, *phases, **kwargs):
    """"""
    display_after = kwargs.setdefault('display_after', True)
    display_initial = kwargs.setdefault('display_initial', True)
    if display_initial:
        print('#')
        print('# Initial code for module ' + self.name)
        print('#')
        self.display()
    for phase in list(phases):
        if 'print_code_' in phase:
            print('#')
            print('# Display ' + phase + ' for module ' + self.name)
            print('#')
            self.display(phase)
        else:
            getattr(self, phase)()
            if display_after:
                print('#')
                print('# Code after ' + phase + ' for module ' + self.name)
                print('#')
                self.display()


pyps.module.validate_phases = validate_phases


def validate_phases(self, *phases, **kwargs):
    """"""
    display_initial = kwargs.setdefault('display_initial', False)
    display_after = kwargs.setdefault('display_after', True)
    if display_initial:
        for m in self:
            print('#')
            print('# Initial code for module ' + m.name)
            print('#')
            m.display()
    for phase in list(phases):
        for m in self:
            m.validate_phases(phase, display_after=display_after, display_initial=False)


pyps.modules.validate_phases = validate_phases
