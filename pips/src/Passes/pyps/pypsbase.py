# -*- coding: utf-8 -*-
from __future__ import print_function

import glob
import os
import re
import shlex
import shutil
import sys
import tempfile
from collections import OrderedDict  # In Python 3.6+, a plain dict would be enough
from functools import reduce
from subprocess import Popen, PIPE

import pypips
import pypsutils
from pypsutils import (addBeginnning, file2string, gen_compile_command, get_property, get_runtimefile, guardincludes,
                       nameToTmpDirName, patchIncludes, set_properties, set_property, string2file, unincludes,
                       update_props)
from six import ensure_binary, ensure_str, iteritems, itervalues

# initialize pipslibs when module is loaded
pypips.atinit()


class Maker(object):
    """
    Makefile generator, use it as a base class to
    implement target-specific compilation process
    """

    def __init__(self):
        """
        Loading attribute header and rules
        """
        self.headers = ''
        self.rules = ''
        self.ext = self.get_ext()
        makefile_info = self.get_makefile_info()
        for mi in makefile_info:
            atr = self.__get_makefile_attributes(mi[1], mi[0])
            self.headers += atr[0]
            self.rules += atr[1]

    @property
    def makefile(self):
        """
        Retrieve the name of the generated Makefile
        """
        return 'Makefile' + self.ext

    def generate(self, path, sources, cppflags='', ldflags=''):
        """
        Create a Makefile with additional flags if given
        """
        mk = 'SOURCES=' + ' '.join(sources) + '\n' + \
             self.headers + '\n' + \
             'CPPFLAGS+=' + cppflags + '\n' + \
             'LDFLAGS+=' + ldflags + '\n' + \
             self.rules
        return os.path.basename(string2file(mk, os.path.join(path, self.makefile))), []

    def __get_makefile_attributes(self, makefile, makefiledir):
        """"""
        l = file2string(get_runtimefile(makefile, makefiledir)).split('##pipsrules##')
        return l[0], l[1]

    def get_ext(self):
        """
        Retrieve makefile extension, specialize it to differentiate your makefile from others
        """
        return ''

    def get_makefile_info(self):
        """
        Retrieve the list of makefile from which the final makefile is generated
        """
        return [('pypsbase', 'Makefile.base')]


class loop(object):
    """
    Do-loop from a module
    """

    def __init__(self, module, label):
        """
        Bind a loop to its module
        """
        self.__module = module
        self.__label = label
        self.__ws = module.workspace

    @property
    def label(self):
        """
        Loop label, as seen in the source code
        """
        return self.__label

    @property
    def module(self):
        """
        Module containing the loop
        """
        return self.__module

    @property
    def pragma(self):
        """"""
        return self.__ws.cpypips.loop_pragma(self.__module.name, self.__label)

    @property
    def workspace(self):
        """
        Workspace containing the loop
        """
        return self.__ws

    def display(self):
        """
        Display loop module
        """
        self.module.display()

    def loops(self, label=None):
        """
        Get outer loops of this loop
        """
        loops = self.__ws.cpypips.module_loops(self.module.name, self.label)
        if label is not None:
            return self.loops()[label]
        else:
            return [loop(self.module, l) for l in str.split(loops, ' ')] if loops else []

    parallel = property(
        lambda self: self.__ws.cpypips.get_loop_execution_parallel(self.module.name, self.label),
        lambda self, is_parallel: self.__ws.cpypips.set_loop_execution_parallel(self.module.name, self.label, is_parallel),
        doc='True if the loop is parallel')


class module(object):
    """
    A source code function
    """

    def __init__(self, ws, name, source=''):
        """
        Binds a module to its workspace
        """
        self.__name = name
        self.__source = source
        self.__ws = ws
        self.re_compilation_units = re.compile(r'^.*!$')
        self.re_static_function = re.compile(r'^.*!.+$')

    def __str__(self):
        """"""
        return '%s/module=%s' % (self.__ws, self.__name)

    __repr__ = __str__

    @property
    def cu(self):
        """
        Compilation unit
        """
        return self.__ws.cpypips.compilation_unit_of_module(self.name)[:-1]

    @property
    def workspace(self):
        """"""
        return self.__ws

    @property
    def name(self):
        """
        Module name
        """
        return self.__name

    @property
    def language(self):
        """"""
        return self.__ws.cpypips.get_module_language(ensure_binary(self.name))  # SWIG needs ASCII, not unicode!

    def compilation_unit_p(self):
        """"""
        return self.re_compilation_units.match(self.name)

    def static_p(self):
        """"""
        return self.re_static_function.match(self.name)

    def edit(self, editor=os.getenv('EDITOR', 'vi')):
        """
        Edits module using given editor
        does nothing on compilation units ...
        """
        if not self.compilation_unit_p():
            self.print_code()
            printcode_rc = os.path.join(self.__ws.dirname, self.__ws.cpypips.show('PRINTED_FILE', self.name))
            code_rc = os.path.join(self.__ws.dirname, self.__ws.cpypips.show('C_SOURCE_FILE', self.name))
            # Well, this code is wrong because the resource is
            # invalidated, even if for example we decide later in the
            # editor not to edit the file...
            self.__ws.cpypips.db_invalidate_memory_resource('C_SOURCE_FILE', self.name)
            shutil.copy(printcode_rc, code_rc)
            # We use shell = True so that we can have complex EDITOR
            # variable such as "emacsclient -c --alternate-editor emacs"
            # :-)
            pid = Popen(editor + ' ' + code_rc, stderr=PIPE, shell=True)
            if pid.wait() != 0:
                print(pid.stderr.readlines(), file=sys.stderr)

    def __prepare_modification(self):
        """
        Prepare everything so that the source code of the module can be modified
        """
        self.print_code()
        printcode_rc = os.path.join(self.__ws.dirname, self.__ws.cpypips.show('PRINTED_FILE', self.name))
        code_rc = os.path.join(self.__ws.dirname, self.__ws.cpypips.show('C_SOURCE_FILE', self.name))
        self.__ws.cpypips.db_invalidate_memory_resource('C_SOURCE_FILE', self.name)
        return code_rc, printcode_rc

    def run(self, cmd):
        """
        Run command `cmd' on current module and regenerate module code from the output of the command, that is 
        run `cmd < 'path/to/module/src' > 'path/to/module/src''
        does nothing on compilation unit ...
        """
        if not self.compilation_unit_p():
            (code_rc, printcode_rc) = self.__prepare_modification()
            pid = Popen(cmd, stdout=open(code_rc, 'w'), stdin=open(printcode_rc), stderr=PIPE)
            # hmmm, there could be stderr output without errors?
            if pid.wait() != 0:
                print(pid.stderr.readlines(), file=sys.stderr)

    def show(self, rc):
        """
        Get name of `rc' resource
        """
        try:
            return self.__ws.cpypips.show(rc.upper(), self.name).split()[-1]
        except:
            raise RuntimeError('Cannot show resource ' + rc)

    def display(self, activate='print_code', rc='printed_file', **props):
        """
        Display a given resource rc of the module, with the ability to change the properties
        """
        sys.stdout.flush() # empty python internal buffers before C writes to stdout
        self.__ws.activate(activate)  # sg: this should be stack-based ?
        if self.workspace:
            old_props = set_properties(self.workspace, update_props('DISPLAY', props))
        res = self.__ws.cpypips.display(rc.upper(), self.name)
        if self.workspace:
            set_properties(self.workspace, old_props)
        return res

    def _set_code(self, newcode):
        """
        Set module content from a string
        """
        if not self.compilation_unit_p():
            (code_rc, _) = self.__prepare_modification()
            string2file(newcode, code_rc)

    def _get_code(self, activate='print_code'):
        """
        Get module code as a string
        """
        getattr(self, str.lower(activate if isinstance(activate, str) else activate.__name__))()
        rcfile = self.show('printed_file')
        return open(os.path.join(self.__ws.dirname, rcfile)).read()

    code = property(_get_code, _set_code)

    def loops(self, label=None):
        """
        Get desired loop if label given, ith loop if label is an integer and an iterator over outermost loops otherwise
        """
        loops = self.__ws.cpypips.module_loops(self.name, '')
        if label is not None:
            if isinstance(label, int):
                return self.loops()[label]
            else:
                return loop(self, label)  # no check is done here ...
        else:
            return [loop(self, l) for l in loops.split(' ')] if loops else []

    @property
    def all_loops(self):
        """"""
        all_loops = []
        loops = self.loops()
        while loops:
            l = loops.pop()
            all_loops.append(l)
            loops += l.loops()
        return all_loops

    def inner_loops(self):
        """
        Get all inner loops
        """
        inner_loops = []
        loops = self.loops()
        while loops:
            l = loops.pop()
            if not l.loops():
                inner_loops.append(l)
            else:
                loops += l.loops()
        return inner_loops

    @property
    def callers(self):
        """
        Get module callers as modules
        """
        callers = self.__ws.cpypips.get_callers_of(self.name)
        return modules([self.__ws[name] for name in callers.split(' ')] if callers else [])

    @property
    def callees(self):
        """
        Get module callees as modules
        """
        callees = self.__ws.cpypips.get_callees_of(self.name)
        return modules([self.__ws[name] for name in callees.split(' ')] if callees else [])

    @property
    def stub_p(self):
        """
        Test if a module is a stub
        """
        stubs = self.__ws.cpypips.pyps_get_stubs()
        return bool(stubs and self.name in stubs.split(' '))

    def saveas(self, path, activate='print_code'):
        """
        Save module's textual representation in `path' using `activate' printer
        """
        with open(path, 'w') as fd:
            fd.write(self._get_code(str.lower(activate if isinstance(activate, str) else activate.__name__)))


class modules(object):
    """
    High-level representation of a module set
    """

    def __init__(self, modules):
        """
        Init from a list of module `the_modules'
        """
        self.__modules = modules
        self.__modules.sort(key=lambda m: m.name)
        self.__ws = modules[0].workspace if modules else None

    def __str__(self):
        return str(self.__modules)

    def __repr__(self):
        return repr(self.__modules)

    @property
    def workspace(self):
        """
        Workspace containing the modules
        """
        return self.__ws

    def __len__(self):
        """
        Get number of contained module
        """
        return len(self.__modules)

    def __iter__(self):
        """
        Iterate over modules
        """
        return self.__modules.__iter__()

    def display(self, activate='print_code', rc='printed_file', **props):
        """
        Display resource `rc' of each modules under `activate' rule and properties `props'
        """
        for m in self.__modules:
            m.display(activate, rc, **props)

    def loops(self):
        """
        Get concatenation of all outermost loops
        """
        return reduce(lambda l1, l2: l1 + l2.loops(), self.__modules, [])

    @property
    def callers(self):
        """
        Get concatenation of all modules' callers
        """
        callers = [c.name for m in self.__modules for c in m.callers]
        return modules([self.__ws[name] for name in callers] if callers else [])

    @property
    def callees(self):
        """
        Get concatenation of all modules' callers
        """
        callees = [c.name for m in self.__modules for c in m.callees]
        return modules([self.__ws[name] for name in callees] if callees else [])


class workspace(object):
    """
    Top-level element of the pyps hierarchy, it represents a set of source
    files and provides methods to manipulate them.
    """

    def __init__(self, *sources, **kwargs):
        """
        init a workspace from sources
        use the string `name' to set workspace name
        use the boolean `verbose' turn messaging on/off
        use the string `cppflags' to provide extra preprocessor flags
        use the boolean `recoverInclude' to turn include recovering on/off
        use the boolean `deleteOnClose' to turn full workspace deletion on/off
        other kwargs will be interpreted as properties
        """

        # gather relevant keywords from kwargs and set default values
        options_default = {'name':           '',
                           'verbose':        True,
                           'cppflags':       '',
                           'ldflags':        '',
                           'cpypips':        pypips,
                           'recoverInclude': True,
                           'deleteOnClose':  False,
                           'deleteOnCreate': False
                           }
        # set the attribute k with value v taken from kwargs or options_default
        for (k, v) in options_default.items():
            setattr(self, k, kwargs.setdefault(k, v))

            # init some values
        self.__checkpoints = []
        self.__modules = OrderedDict()
        self.__sources = []  # todo: not useful?
        self.log_buffer = False

        # initialize calls
        self.cpypips.verbose(bool(self.verbose))
        self.__sources = list(sources)

        # use random repository name if none given
        if not self.name:
            #  generate a random place in $PWS
            dirname = tempfile.mktemp('.database', 'PYPS', dir='.')
            self.name = os.path.splitext(os.path.basename(dirname))[0]

        # sanity check to fail with a python exception
        if os.path.exists('.'.join([self.name, 'database'])):
            if self.deleteOnCreate:
                self.delete(self.name)
            else:
                raise RuntimeError('Cannot create two workspaces with same database')

        # because of the way we recover include, relative paths are changed, which could be a problem for #includes
        if self.recoverInclude:
            self.cppflags = patchIncludes(self.cppflags)
            kwargs['cppflags'] = self.cppflags

        # setup some inner objects
        self.props = workspace.Props(self)
        self.fun = workspace.Fun(self)
        self.cu = workspace.Cu(self)
        self.__recover_include_dir = None  # holds tmp dir for include recovery

        # SG: it may be smarter to save /restore the env ?
        if self.cppflags:
            self.cpypips.setenviron('PIPS_CPP_FLAGS', self.cppflags)
        if self.verbose:
            print('Using CPPFLAGS =', self.cppflags, file=sys.stderr)

        # before the workspace gets created, set some properties to pyps friendly values
        if not self.verbose:
            self.props.no_user_warning = True
            self.props.user_log_p = False
        self.props.maximum_user_error = 42  # after this number of exceptions the program will abort
        self.props.pyps = True

        # also set the extra properties given in kwargs
        def safe_setattr(p, k, v):  # just in case some extra kwarg are passed for child classes
            try:
                setattr(p, k, v)
            except:
                pass

        for (k, v) in kwargs.items():
            if k not in options_default:
                safe_setattr(self.props, k, v)

        # try to recover includes
        if self.recoverInclude:
            # add guards around #include's, in order to be able to undo the
            # inclusion of headers.
            self.__recover_include_dir = nameToTmpDirName(self.name)
            try:
                shutil.rmtree(self.__recover_include_dir)
            except OSError:
                pass
            os.mkdir(self.__recover_include_dir)

            def rename_and_copy(f):
                """
                Rename file f and copy it to the recover include dir
                """
                fp = f.replace('/', '_') if self.props.preprocessor_file_name_conflict_handling else f
                newfname = os.path.join(self.__recover_include_dir, os.path.basename(fp))
                shutil.copy2(f, newfname)
                guardincludes(newfname)
                return newfname

            self.__sources = [rename_and_copy(f) for f in self.__sources]
            # this not very nice, but if conflict name handling is used, it is emulated at the recover include step and not needed any further
            if self.props.preprocessor_file_name_conflict_handling:
                self.props.preprocessor_file_name_conflict_handling = False

        # remove any existing previous checkpoint state
        for chkdir in glob.glob('.%s.chk*' % self.dirname):
            shutil.rmtree(chkdir)

        # try to create the workspace now
        try:
            self.cpypips.create(self.name, [ensure_binary(x) for x in self.__sources])
        except RuntimeError:
            self.close()
            raise
        self.__build_module_list()

    def __str__(self):
        """"""
        return 'workspace=%s' % self.name

    __repr__ = __str__

    def __enter__(self):
        """
        Handler for the with keyword
        """
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """
        Handler for the with keyword
        """
        if exc_type:  # we want to keep info on why we aborted
            self.deleteOnClose = False
        self.close()
        return False

    @property
    def dirname(self):
        """
        Retrieve workspace database directory
        """
        return self.name + '.database'

    @property
    def tmpdirname(self):
        """
        Retrieve workspace database directory
        """
        return os.path.join(self.dirname, 'Tmp')

    def __iter__(self):
        """
        Provide an iterator on workspace's module, so that you can write
        map(do_something,my_workspace)
        """
        return itervalues(self.__modules)

    def __getitem__(self, module_name):
        """
        Retrieve a module of the module from its name
        """
        self.__build_module_list()
        return self.__modules[module_name]

    def __contains__(self, module_name):
        """
        Test if the workspace contains a given module
        """
        self.__build_module_list()
        return module_name in self.__modules

    def __build_module_list(self):
        """
        Update workspace module list
        """

        def info(ws, topic):
            """"""
            return ws.cpypips.info(topic).split()

        self.__modules = OrderedDict()  # reinit the dictionary to remove old state
        for m in info(self, 'modules'):
            self.__modules[m] = module(self, m, self.__sources[0])

    def add_source(self, fname):
        """
        Add a source file to the workspace, using PIPS guard includes if necessary
        """
        newfname = fname
        if self.recoverInclude:
            newfname = os.path.join(nameToTmpDirName(self.name), os.path.basename(fname))
            shutil.copy2(fname, newfname)
            guardincludes(newfname)
        self.__sources += [newfname]
        self.cpypips.add_a_file(ensure_binary(newfname))  # SWIG requires ASCII here
        self.__build_module_list()

    def checkpoint(self):
        """
        Checkpoints the workspace and returns a workspace id
        """
        self.cpypips.close_workspace(0)
        # not checkpointing in tmpdir to avoid recursive duplications,
        # could be made better
        chkdir = '.%s.chk%d' % (self.dirname, len(self.__checkpoints))
        shutil.copytree(self.dirname, chkdir)
        self.__checkpoints.append(chkdir)
        self.cpypips.open_workspace(self.name)
        return chkdir

    def restore(self, chkdir):
        """
        Restore workspace state from given checkpoint id
        """
        self.props.PIPSDBM_RESOURCES_TO_DELETE = 'all'
        self.cpypips.close_workspace(0)
        shutil.rmtree(self.dirname)
        shutil.copytree(chkdir, self.dirname)
        self.cpypips.open_workspace(self.name)

    def _user_headers(self):
        """
        List the user headers used in self.__sources with the compiler configuration given in compiler,
        as (sources,headers)
        """
        command = ['gcc', '-MM', self.cppflags] + list(self.__sources)

        command = ' '.join(command) + r" | sed -n -r '/^.*\.h$/ p'"
        # ' |sed \':a;N;$!ba;s/\(.*\).o: \\\\\\n/:/g\' |sed \'s/ \\\\$//\' |cut -d\':\' -f2'
        if self.verbose:
            print(command, file=sys.stderr)
        p = Popen(command, shell=True, stdout=PIPE, stderr=PIPE)
        out, err = map(ensure_str, p.communicate())
        if self.verbose:
            print(out, file=sys.stderr)
        rc = p.returncode
        if rc != 0:
            raise RuntimeError('Error while retrieving user headers: gcc returned %d.\n%s' \
                               % (rc, ensure_str(out) + '\n' + ensure_str(err)))

        # Parse the results :
        # each line is split thanks to shlex.split, and we only keep the header files
        lines = [shlex.split(x) for x in ensure_str(out).split('\n')]  # PY3: type(out) is bytes, not str...
        return [s for l in lines for s in l if s.endswith('.h')]

    def save(self, rep=None):
        """
        Save workspace back into source form in directory rep if given.
        By default, keeps it in the workspace's tmpdir
        """
        self.cpypips.apply('UNSPLIT', '%ALL')
        if rep is None:
            rep = self.tmpdirname
        if not os.path.exists(rep):
            os.makedirs(rep)
        if not os.path.isdir(rep):
            raise ValueError("'%s' is not a directory" % rep)

        saved = []
        for s in os.listdir(os.path.join(self.dirname, 'Src')):
            f = os.path.join(self.dirname, 'Src', s)
            if self.recoverInclude:
                # Recover includes on all the files.
                # Guess that nothing is done on Fortran files... :-/
                unincludes(f)
            if rep:
                # Save to the given directory if any
                cp = os.path.join(rep, s)
                shutil.copy(f, cp)
                # Keep track of the file name
                saved.append(cp)
            else:
                saved.append(f)

        headers_basename = self._user_headers()
        for uh in headers_basename:
            shutil.copy(uh, rep)

        headers = [os.path.join(rep, x) for x in headers_basename]

        for f in saved:
            addBeginnning(f, '#include "pipsdef.h"\n')
            # force an update of the modification time, because previous
            # operation might have caused rounded to the second and have broken
            # makefile dependences
            (_, _, _, _, _, _, _, atime, ftime, _) = os.stat(
                f)  # accuracy of os.utime is not enough, so make a trip in the future
            os.utime(f, (atime + 1, ftime + 1))

        shutil.copy(get_runtimefile('pipsdef.h', 'pypsbase'), rep)
        return sorted(saved), sorted(headers + [os.path.join(rep, 'pipsdef.h')])

    def divert(self, rep=None, maker=Maker()):
        """
        Save the workspace and generates a  makefile according to `maker'
        """
        if rep is None:
            rep = self.tmpdirname
        saved = self.save(rep)[0]
        return maker.generate(rep, [os.path.basename(x) for x in saved], cppflags=self.cppflags, ldflags=self.ldflags)

    def compile(self, maker=Maker(), rep=None, outfile='a.out', rule='all', **opts):
        """
        Uses the fabulous makefile generated to compile the workspace.
        Returns the executable's path
        """
        if rep is None:
            rep = self.tmpdirname
        self.divert(rep, maker)
        commandline = gen_compile_command(rep, maker.makefile, outfile, rule, **opts)

        if self.verbose:
            print('Compiling the workspace with', commandline, file=sys.stderr)
        # We need to set shell to False or it messes up with the make command
        p = Popen(commandline, shell=False, stdout=PIPE, stderr=PIPE)
        out, err = map(ensure_str, p.communicate())
        if self.verbose:
            print(out, file=sys.stderr)
        rc = p.returncode
        if rc != 0:
            print(err, file=sys.stderr)
            raise RuntimeError('%s failed with return code %d' % (commandline, rc))

        return os.path.join(rep, outfile)

    def run(self, binary, args=None):
        """
        Runs `binary' with the list of arguments `args'.

        :return: (return_code,stdout,stderr)
        """
        #  Command to execute our binary
        cmd = [os.path.join('./', binary)]
        if args:
            cmd += [str(x) for x in args]
        p = Popen(cmd, stdout=PIPE, stderr=PIPE)
        out, err = map(ensure_str, p.communicate())
        rc = p.returncode
        if rc != 0:
            print(err, file=sys.stderr)
            raise RuntimeError('%s failed with return code %d' % (cmd, rc))
        return rc, out, err

    def activate(self, phase):
        """
        Activate a given phase
        """
        p = str.upper(phase if isinstance(phase, str) else phase.__name__)
        self.cpypips.user_log('Selecting rule: %s\n', p)
        self.cpypips.activate(p)

    def filter(self, matching=lambda x: True):
        """
        Create an object containing current listing of all modules,
        filtered by the filter argument
        """
        self.__build_module_list()
        the_modules = [m for m in self.__modules.values() if matching(m)]
        return modules(the_modules)

    @property
    def compilation_units(self):
        """
        Transform in the same way the filtered compilation units as a pseudo-variable
        """
        return self.filter(lambda m: m.compilation_unit_p())

    @property
    def all_functions(self):
        """
        Build also a pseudo-variable for the set of all the functions of the
        workspace.  We should ask PIPS top-level for it instead of
        recomputing it here, but it is so simple this way...
        """
        return self.filter(lambda m: not m.compilation_unit_p())

    def pre_phase(self, phase, module):
        """"""
        pass

    def post_phase(self, phase, module):
        """"""
        pass

    # Create an "all" pseudo-variable that is in fact the execution of
    # filter with the default filtering rule: True
    all = property(filter)

    @staticmethod
    def delete(name):
        """
        Delete a workspace by name

        It is a static method of the class since an open workspace
        cannot be deleted without creating havoc...
        """
        pypips.delete_workspace(name)
        try:
            shutil.rmtree(nameToTmpDirName(name))
        except OSError:
            pass

    def close(self):
        """
        Force cleaning and deletion of the workspace
        """
        for x in self.__checkpoints:
            shutil.rmtree(x)
        try:
            self.cpypips.close_workspace(0)
        except RuntimeError:
            pass
        if self.deleteOnClose:
            try:
                workspace.delete(self.name)
            except (RuntimeError, AttributeError):
                pass
        if self.__recover_include_dir:
            try:
                shutil.rmtree(self.__recover_include_dir)
            except OSError:
                pass

    class Cu(object):
        """
        Allow user to access a compilation unit by writing w.cu.compilation_unit_name
        """

        def __init__(self, wp):
            """"""
            self.__dict__['_Cu__wp'] = wp
            self.__dict__['_Cu__cuDict'] = self.__cuDict

        def __setattr__(self, name, val):
            """"""
            raise AttributeError('Compilation Unit assignment is not allowed.')

        def __getattr__(self, name):
            """"""
            self.__wp._workspace__build_module_list()
            n = name + '!'
            if n in self.__wp._workspace__modules:
                return self.__wp._workspace__modules[n]
            else:
                raise NameError('Unknown compilation unit : ' + name)

        def __dir__(self):
            """"""
            return list(self.__cuDict().keys())

        def __len__(self):
            """"""
            return len(self.__cuDict())

        def __cuDict(self):
            """"""
            self.__wp._workspace__build_module_list()
            return OrderedDict(((k[:-1], v)
                                for k, v in self.__wp._workspace__modules.items()
                                if k.endswith('!')
                                ))  # generator comprehension wrapped inside an OrderedDict

        def __iter__(self):
            """
            Provide an iterator on workspace's compilation unit, so that you can write
            map(do_something,my_workspace)
            """
            return itervalues(self.__cuDict())

        def __getitem__(self, module_name):
            """
            Retrieve a module of the workspace from its name
            """
            return self.__cuDict()[module_name]

        def __contains__(self, module_name):
            """
            Test if the workspace contains a given module
            """
            return module_name in self.__cuDict()

    class Fun(object):
        """
        Allow user to access a module by writing w.fun.modulename
        """

        def __init__(self, wp):
            """"""
            self.__dict__['_Fun__wp'] = wp
            self.__dict__['_Fun__functionDict'] = self.__functionDict

        def __setattr__(self, name, val):
            """"""
            raise AttributeError('Module assignment is not allowed.')

        def __getattr__(self, name):
            """"""
            if name in self.__functionDict():
                return self.__wp._workspace__modules[name]
            else:
                raise NameError('Unknown function: ' + name)

        def __functionDict(self):
            """"""
            self.__wp._workspace__build_module_list()
            return OrderedDict(((k, v)
                                for k, v in self.__wp._workspace__modules.items()
                                if not k[-1].endswith('!')
                                ))  # generator comprehension wrapped inside an OrderedDict

        def __len__(self):
            """"""
            return len(self.__functionDict())

        def __dir__(self):
            """"""
            return list(self.__functionDict().keys())

        def __getitem__(self, module_name):
            """
            Retrieve a module of the workspace from its name
            """
            return self.__functionDict()[module_name]

        def __iter__(self):
            """
            Provide an iterator on workspace's functions, so that you
            can write map(do_something, my_workspace.fun)
            """
            return itervalues(self.__functionDict())

        def __contains__(self, module_name):
            """
            Test if the workspace contains a given module
            """
            return module_name in self.__functionDict()

    class Props(object):
        """
        Allow user to access a property by writing w.props.PROP,
        this class contains a static dictionary of every properties
        and default value

        all is a local dictionary with all the properties with their initial
        values. It is generated externally.
        """

        def __init__(self, wp):
            """"""
            self.__dict__['_Props__wp'] = wp

        def __setattr__(self, name, val):
            """"""
            if name.upper() in self.all:
                set_property(self.__wp, name, val)
            else:
                raise NameError('Unknown property: ' + name)

        def __getattr__(self, name):
            """"""
            if name.upper() in self.all:
                return get_property(self.__wp, name)
            else:
                raise NameError('Unknown property: ' + name)

        __setitem__ = __setattr__
        __getitem__ = __getattr__

        def __dir__(self):
            """
            We should use the updated values, not the default ones...
            """
            return list(self.all.keys())

        def __len__(self):
            return len(self.all)

        def __iter__(self):
            """
            Provide an iterator on workspace's properties, so that you
            can write map(do_something, my_workspace.props)
            """
            return iteritems(self.all)

        def __contains__(self, property_name):
            """
            Test if the workspace contains a given property
            """
            return property_name in self.all

# Some Emacs stuff:
### Local Variables:
### mode: python
### mode: flyspell
### ispell-local-dictionary: "american"
### tab-width: 4
### End:
