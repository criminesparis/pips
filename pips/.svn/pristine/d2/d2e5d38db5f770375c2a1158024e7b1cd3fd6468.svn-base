#!/usr/bin/env python

"""
This module provide three ways of exploring the transformation space for a given module in a given programm
- brute force exploration
- greedy exploration
- genetic algorithm based exploration
"""

from __future__ import print_function, absolute_import

import operator
import os
import random
import shutil
import subprocess
import sys
import tempfile
from functools import reduce
from operator import xor
from optparse import OptionParser
from string import upper

import six.moves.configparser as configparser
import workspace_gettime

# must set this first, it controls the number of pyro server that can be launched
os.environ['PYRO_PORT_RANGE'] = '1000'
import pyrops


class Transfo(object):
    """
    Stores information concerning a code transformation
    """

    def __init__(self, module, transfo, loop=None, **props):
        """"""
        self.transfo = transfo
        self.modname = module
        self.loop = loop
        self.props = props

    def __str__(self):
        """"""
        s = ' '.join([str(Property(prop, val)) for (prop, val) in self.props.items()]) + \
            ' transformation:' + self.transfo + ' on module ' + self.modname
        if self.loop: s += ' with loop:' + self.loop
        return s

    def run(self, wsp):
        """
        Run this transformation on module `name'
        """
        if self.loop:
            getattr(wsp[self.modname].loops(self.loop), self.transfo.lower())(**self.props)
        else:
            getattr(wsp[self.modname], self.transfo.lower())(**self.props)

    def __hash__(self):
        """"""
        return hash("{}:{}:{}:{}".format(self.transfo, self.modname, self.loop, self.props))

    def __cmp__(self, other):
        """"""
        return cmp(self.__hash__(), other.__hash__())  # todo: replace cmp


class Property(object):
    """
    Stores informations concerning a pips property
    """

    def __init__(self, prop, value):
        """"""
        self.prop = prop.upper()
        self.val = value

    def __str__(self):
        """"""
        return 'property:{} value:{}'.format(self.prop, self.val)

    def run(self, workspace):
        """
        Set the property on current workspace
        """
        if workspace.verbose:
            print('setting property ' + self.prop + ' to ' + str(self.val))
        workspace.set_property(**{self.prop: self.val})

    def __hash__(self):
        """"""
        return hash('{}:{}'.format(self.prop, self.val))

    def __cmp__(self, other):
        return cmp(self.__hash__(), other.__hash__())  # todo: replace cmp


class Mutation(object):
    """
    A mutation contains a transformation with associated properties
    it represents a parametrized transformation on a module
    """

    def __init__(self, *codons):
        """"""
        self.codons = codons

    def run(self, wsp):
        """
        Apply all the transformation in the mutation on module `name'
        """
        for x in self.codons:
            x.run(wsp)

    def __str__(self):
        """"""
        return reduce(lambda x, y: x + str(y), self.codons, '')

    def __hash__(self):
        """"""
        return reduce(xor, [x.__hash__() for x in self.codons])

    def __cmp__(self, other):
        """"""
        return cmp(self.__hash__(), other.__hash__())


def called(self):
    """"""
    callers = self.callers
    while callers:
        caller = callers.pop()
        if caller.name == 'main':
            return True
        else:
            callers += caller.callers
    return self.name == 'main'


class Generator(object):
    """"""
    pass


class DummyGenerator(Generator):
    """
    Generates a transformation without constraints
    """

    def __init__(self, name, **args):
        """"""
        self.name = name
        self.properties = args

    def generate(self, individual):
        """"""
        mutations = []
        for module in individual.ws.fun:
            if called(module):
                mutations.append(Mutation(Transfo(module.name, self.name, **self.properties)))
        return mutations


class UniqGenerator(DummyGenerator):
    """
    Generates a transformation that was not just applied
    """

    def generate(self, individual):
        """"""
        mutations = []
        for module in individual.ws.fun:
            if called(module):
                mutation = Mutation(Transfo(module.name, self.name, **self.properties))
                if not individual.mutations or mutation != individual.mutations[-1]:
                    mutations.append(mutation)
        return mutations


class LoopGenerator(DummyGenerator):
    """
    Generates a parametrized loop transformation
    """

    def generate(self, individual):
        """"""
        mutations = []
        for module in individual.ws.fun:
            if called(module):
                loops = module.loops()
                while loops:
                    loop = loops.pop()
                    # self.properties["LOOP_LABEL"]=loop.label
                    mutations.append(Mutation(Transfo(module.name, self.name, loop=loop.label, **self.properties)))
                    loops += loop.loops()
        return mutations


class ParallelLoopGenerator(Generator):
    """
    Generates a loop parallelization Transformation
    """

    def generate(self, individual):
        """"""
        mutations = []
        for module in individual.ws.fun:
            if called(module) and module.loops:
                mutations.append(
                    Mutation(
                        Transfo(module.name, 'privatize_module'),
                        Transfo(module.name, 'coarse_grain_parallelization'),
                        Transfo(module.name, 'ompify_code'),
                    )
                )
        return mutations


class FusionGenerator(Generator):
    """
    Generates a loop fusion transformation
    """

    def generate(self, individual):
        """"""
        mutations = []
        for m in individual.ws.fun:
            if called(m):
                for l in m.loops()[:-1]:
                    mutations.append(Mutation(Transfo(m.name, 'force_loop_fusion', loop=l.label)))
        return mutations


class UnfoldGenerator(Generator):
    """"""

    def generate(self, individual):
        """
        Otherwise let's lookup everything.
        """
        mutations = []
        for module in individual.ws.fun:
            if module.callees and called(module):
                mutations.append(Mutation(Transfo(module.name, 'unfolding')))
        return mutations


class InlineGenerator(Generator):
    """"""

    def generate(self, individual):
        """
        Otherwise let's lookup everything.
        """
        mutations = []
        for module in individual.ws.fun:
            if called(module):
                for caller in module.callers:
                    mutations.append(Mutation(Transfo(module.name, 'inlining', inlining_purge_labels=True,
                                                      inlining_callers=caller.name)))
        return mutations


#
##
#
def getwdir(sources):
    """"""
    return 'WDIR_' + ''.join('-'.join(sources).split('/'))


class Individual(object):
    """"""

    def __init__(self, args):
        """"""
        self.args = args
        self.mutations = []
        self.execution_time = 0
        self.min_time = 0
        self.max_time = 0
        self.living = True

        self.foutname = '_'.join([str(random.randint(0, 1000000)), os.path.basename(args.sources[0])])
        # create workspace
        self.ws = pyrops.pworkspace(self.args.sources, verbose=args.verbose > 1, recoverInclude=True,
                                    parents=[workspace_gettime.workspace])
        self.ws.activate('MUST_REGIONS')
        self.ws.activate('PRECONDITIONS_INTER_FULL')
        self.ws.activate('TRANSFORMERS_INTER_FULL')
        self.ws.activate('RICE_SEMANTICS_DEPENDENCE_GRAPH')
        self.ws.activate('RICE_REGIONS_DEPENDENCE_GRAPH')
        self.ws.activate('REGION_CHAINS')

        self.ws.props.RICEDG_STATISTICS_ALL_ARRAYS = True
        self.ws.props.C89_CODE_GENERATION = True
        self.ws.props.CONSTANT_PATH_EFFECTS = False
        self.ws.props.PRETTYPRINT_SEQUENTIAL_STYLE = 'seq'

    def push(self, mutation):
        """"""
        # As pointed out by eliott, we have to recompute this each time to ensure we always get the same labels
        for m in self.ws.fun:
            m.flag_loops()
        try:
            if self.args.verbose:
                print('Running %s ...' % mutation, end=' ')
            mutation.run(self.ws)
            self.mutations.append(mutation)
            if self.args.verbose:
                print('ok')
        except RuntimeError as re:
            if self.args.verbose:
                print('disabled (reason is {} )'.format(re.args[0]))
            if self.args.debug:
                print('Input code was:')
                self.ws[mutation.codons[0].modname].display()

    def rate(self):
        """"""
        if not self.execution_time:
            wdir = os.sep.join([getwdir(self.args.sources), self.foutname])
            # random names in case several processes are running at the same time
            randString = str(random.randint(0, 1000000)) + str(random.randint(0, 1000000))
            cflags = os.environ['PIPS_CPP_FLAGS'] + ' -I. -w'
            exec_out = self.ws.compile(CC='gcc', CFLAGS=cflags, rep=wdir, outfile='/tmp/' + randString + '.out')
            if self.args.test:
                runner = [self.args.test, exec_out]
            else:
                runner = [exec_out]

            elapsed = []

            # print('running',exec_out)
            for i in range(0, self.args.get_time):
                t = -1
                while t < 0:
                    if subprocess.Popen(runner, stdout=open(os.devnull), stderr=subprocess.STDOUT).wait() == 0:
                        t = open(workspace_gettime.STAMPFILE).readline()
                        os.remove(workspace_gettime.STAMPFILE)
                    else:
                        raise Exception('Failed to run test, check your test file\nRun command was {}'.format(runner))
                elapsed += [int(t)]
            elapsed.sort()
            self.execution_time = elapsed[len(elapsed) // 2]
            self.min_time = elapsed[0]
            self.max_time = elapsed[-1]
            if not self.args.blork:
                os.remove(exec_out)

    def clone(self):
        """"""
        individual = Individual(self.args)
        for imutation in self.mutations:
            individual.push(imutation)
        return individual

    def rip(self):
        """"""
        if self.living:
            self.ws.close()
            self.living = False

    def __str__(self):
        """"""
        s = reduce(lambda x, y: x + ' ' + y, self.args.sources, 'sources:')
        s += ' out:' + self.foutname + '\n'
        s += 'workspace:' + self.ws.name + '\n'
        s += 'execution time: {} (min: {}, max: {})\n'.format(self.execution_time, self.min_time, self.max_time)
        for t in self.mutations:
            s += str(t)
        return s

    def __hash__(self):
        """"""
        return reduce(xor, [x.__hash__() for x in self.mutations], 42)

    def __cmp__(self, other):
        """"""
        return cmp(self.__hash__(), other.__hash__())  # todo: replace cmp, nonexistent in PY3


#
##
#

class Algo(object):
    """"""

    def __init__(self, args):
        """"""
        self.nbgen = args.gens
        self.args = args
        self.step = 0
        eve = Individual(args)  # we start with a dummy individual
        eve.rate()
        self.pool = {eve}  # who said eve was dummy? because she ate the apple, maybe?

    def __enter__(self):
        """"""
        return self

    def __exit__(self, t, v, tb):
        """"""
        [i.rip() for i in self.pool]
        return True

    def run(self):
        """"""
        # process nbgen generation
        # pdb.set_trace()
        while self.step < self.nbgen:
            self.msg()
            self.populate()
            self.rate()
            self.select()
            self.step += 1
        # make sure all remote workspace are closed
        for individual in self.pool: individual.rip()
        return self.sort()

    def rate(self):
        """"""
        for individual in self.pool:
            individual.rate()

    def msg(self):
        """"""
        print("Step %d: best element score is '%d'" % (
            self.step, min(self.pool, key=operator.attrgetter('execution_time')).execution_time))

    def sort(self):
        """"""
        return sorted(self.pool, key=operator.attrgetter('execution_time'))


class Full(Algo):
    """"""

    def __init__(self, args):
        """"""
        super(Full, self).__init__(args)

    def populate(self):
        """"""
        newpool = set()
        for individual in self.pool:
            if len(individual.mutations) == self.step:
                mutation_candidates = []
                for generator in self.args.generators:
                    mutation_candidates += generator.generate(individual)
                for mutation in mutation_candidates:
                    new_individual = individual.clone()
                    new_individual.push(mutation)
                    if new_individual in newpool or new_individual in self.pool:
                        new_individual.rip()
                    else:
                        newpool.add(new_individual)
                individual.rip()
        self.pool |= newpool

    def select(self):
        """"""
        pass


class Greedy(Algo):
    """"""

    def __init__(self, args):
        """"""
        super(Greedy, self).__init__(args)

    def populate(self):
        """"""
        newpool = set()
        for individual in self.pool:
            mutation_candidates = []
            for generator in self.args.generators:
                mutation_candidates += generator.generate(individual)
            for mutation in mutation_candidates:
                new_individual = individual.clone()
                new_individual.push(mutation)
                if new_individual in newpool or new_individual in self.pool:
                    new_individual.rip()
                else:
                    newpool.add(new_individual)
        self.pool |= newpool

    def select(self):
        eugenism = self.sort()
        for individual in eugenism[self.args.popsize:]:
            individual.rip()
        self.pool = set(eugenism[:self.args.popsize])


#
##
#

class Genetic(Algo):
    """"""

    def __init__(self, args):
        """"""
        super(Genetic, self).__init__(args)

        # init population
        adam = Individual(self.args)
        self.pool.add(adam)
        mutation_candidates = []

        for generator in self.args.generators:
            mutation_candidates += generator.generate(adam)
        random.shuffle(mutation_candidates)

        for mutation in mutation_candidates:
            individual = adam.clone()
            individual.push(mutation)
            if individual in self.pool:
                individual.rip()
            else:
                self.pool.add(individual)
            if len(self.pool) == self.args.popsize:
                break

        if len(self.pool) != self.args.popsize:
            raise Exception('Not enough GeneCandidates, try to increase the number of generators')

        self.rate()

    def best_half(self, individuals):
        """"""
        half_individual = set(random.sample(individuals, len(individuals) / 2))
        other_half_individual = individuals.difference(half_individual)

        def select_individual(i0, i1):
            """"""
            # handle None case
            if not i0:
                return i1
            if not i1:
                return i0
            # other cases
            if i0.execution_time < i1.execution_time:
                if self.args.verbose > 1:
                    print(i0, '<<<<<<<<<<', i1)
                return i0
            else:
                if self.args.verbose > 1:
                    print(i0, '>>>>>>>>>>', i1)
                return i1

        return set(map(select_individual, half_individual, other_half_individual))

    def populate(self):
        """
        Pick up 2*k elements to renew
        """
        try:
            renewed_individuals = set(random.sample(self.pool, 2 * self.args.renewal_rate))
        except:
            print('Sample size is {} and popsize is {} (should be {})'.format(2 * self.args.renewal_rate,
                                                                              len(self.pool),
                                                                              self.args.popsize))
            raise

        # make a tournament to keep only k
        best_individuals = self.best_half(renewed_individuals)

        # make them mutate
        self.newpool = set()
        for individual in best_individuals:
            mutation_candidates = []
            for generator in self.args.generators:
                mutation_candidates += generator.generate(individual)
            # add a random mutation among the existing one
            random.shuffle(mutation_candidates)
            for mutation in mutation_candidates:
                new_individual = individual.clone()
                new_individual.push(mutation)
                if new_individual in self.newpool or new_individual in self.pool:
                    new_individual.rip()
                else:
                    new_individual.rate()
                    self.newpool.add(new_individual)
                    break

    def select(self):
        """"""
        tmp = self.sort()
        baddies = tmp[self.args.popsize - self.args.renewal_rate:]
        goodies = tmp[:self.args.popsize - self.args.renewal_rate]
        for i in baddies:
            i.rip()
        self.pool = set(goodies)
        self.pool |= self.newpool
        if len(self.pool) != self.args.popsize:
            raise Exception(
                'Population size invariant changed from {1} to {0}'.format(len(self.pool), self.args.popsize))


#
##
#

class UnitTest(object):  # todo: use Python's unittest?
    """
    This one is in charge of performing some regression testing
    """

    def __init__(self, args):
        """"""
        self.args = args

    def check(self):
        """"""
        # self.check_sequence_and_quit()
        self.check_newborn_hash()
        self.check_transfo_hash()
        self.check_gene_hash()
        self.check_grownup_hash()
        self.check_grownup_hash2()
        self.check_set_behavior()

    def check_newborn_hash(self):
        """
        Check if two new born have similar hashes
        """
        adam = Individual(self.args)
        eve = Individual(self.args)
        try:
            if adam.__hash__() != eve.__hash__():
                raise Exception('Individual with no mutations have different hash')
        finally:
            adam.rip()
            eve.rip()

    def check_transfo_hash(self):
        """
        Check if two transfo with same arg have same hash
        """
        t0 = Transfo('main', 'UNFOLDING', unfolding_callers='foo')
        t1 = Transfo('main', 'UNFOLDING', unfolding_callers='foo')
        if t0.__hash__() != t1.__hash__():
            raise Exception('Transformations with same parameters have different hash')

    def check_mutation_hash(self):
        """
        Check if two mutation with same arg have same hash
        """
        g0 = Mutation(Transfo('main', 'UNFOLDING'))
        g1 = Mutation(Transfo('main', 'UNFOLDING'))
        if g0.__hash__() != g1.__hash__():
            raise Exception('Mutations with same parameters have different hash')

    def check_grownup_hash(self):
        """
        Check if two individuals with one same mutation have similar hashes
        """
        adam = Individual(self.args)
        eve = Individual(self.args)
        adam.push(Mutation(Transfo('main', 'UNFOLDING')))
        eve.push(Mutation(Transfo('main', 'UNFOLDING')))
        try:
            if adam.__hash__() != eve.__hash__():
                raise Exception('Individual with same mutations have different hash')
        finally:
            adam.rip()
            eve.rip()

    def check_grownup_hash2(self):
        """
        Check if two individuals with the very same mutation have similar hashes
        """
        adam = Individual(self.args)
        eve = Individual(self.args)
        g0 = Mutation(Transfo('main', 'UNFOLDING'))
        adam.push(g0)
        eve.push(g0)
        try:
            if adam.__hash__() != eve.__hash__():
                raise Exception('Individual with same mutations have different hash')
        finally:
            adam.rip()
            eve.rip()

    def check_set_behavior(self):
        """
        Check if two individuals with one same mutation can be inserted in the same set
        """
        adam = Individual(self.args)
        eve = Individual(self.args)
        adam.push(Mutation(Transfo('main', 'UNFOLDING')))
        eve.push(Mutation(Transfo('main', 'UNFOLDING')))
        paradise = set()
        paradise.add(adam)
        try:
            if adam.__hash__() != eve.__hash__():
                raise Exception('Individual with same mutations have different hash')
            if eve not in paradise:
                raise Exception('Individual with same hash can go in the same set')
        finally:
            adam.rip()
            eve.rip()

    def check_sequence_and_quit(self):
        """
        Check a particular transformation sequence
        """
        adam = Individual(self.args)
        adam.push(Mutation(Transfo('main', 'UNFOLDING')))
        eve = adam.clone()
        for mutation in adam.mutations: eve.push(mutation)
        eve.push(Mutation(Transfo('main', 'FLATTEN_CODE')))
        baby = eve.clone()
        for mutation in eve.mutations: baby.push(mutation)
        mutations = FusionGenerator().generate(baby)
        for g in mutations:
            print(g)
        baby.push(mutations[1])
        baby.ws.fun.main.display()
        sys.exit(2)


#
##
#

def ParseConfigFile(args):
    """
    Returns a set of generator
    """

    args.generators = []
    parser = configparser.RawConfigParser()
    parser.read('pypsearch.cfg')

    base = {'inline':               InlineGenerator(),
            'unroll':               UnrollGenerator(),  # todo: undefined function
            'unfold':               UnfoldGenerator(),
            'fusion':               FusionGenerator(),
            'loop_parallelisation': ParallelLoopGenerator()
            }

    try:
        for x in parser.items('CustomGenerator'):
            if x[0] not in base:
                print('Error when parsing config file, as ' + x[0] + ' is not a generator')
            else:
                args.generators += [base[x[0]]]
    except configparser.NoSectionError:
        pass

    def parseGenerator(args, generator, x):
        """"""
        props = x[1].split(',')
        propvals = {}

        for propval in props:
            splitProp = propval.split('=')
            if len(splitProp) != 2 or len(splitProp[1]) == 0:
                continue
            prop = splitProp[0]
            val = splitProp[1]
            if val[0] == '"':
                val = val[1:-1]
            elif upper(val) == 'TRUE':
                val = True
            elif upper(val) == 'FALSE':
                val = False
            else:
                val = int(val)
            propvals[prop] = val
        args.generators.append(generator(x[0], **propvals))

    for generator in [DummyGenerator, UniqGenerator, LoopGenerator]:
        try:
            for x in parser.items(generator.__name__):
                parseGenerator(args, generator, x)
        except configparser.NoSectionError:
            pass

    if not args.generators:
        print('No generator given in the config file (pypsearch.cfg), so using only the inline generator')
        args.generators = [base["inline"]]

    print('Using generators:', end=' ')
    for g in args.generators:
        try:
            print('%s(%s)' % (g.__class__.__name__, g.name), end=' ')
        except AttributeError:
            print(g.__class__.__name__, end=' ')
    print()


def ParseCommandLine():
    """"""
    # todo: use argparse instead
    parser = OptionParser(description='Pypsearch - Automated exploration of the set of transformations with python.',
                          usage='usage: %prog [options] sourcename')
    parser.add_option('--algo', default='genetic', type=str, help='search algorithm to use')
    parser.add_option('--log', help='log file to save the best results')
    parser.add_option('--gens', default=1, type=int, help='Number of generations for the genetic algorithm')
    # parser.add_option('--crossovers', default=1, type=int, help='Number of crossovers to perform each generation')
    # parser.add_option('--tournaments', default=3, type=int, help='Number of winners of a tournament for the genetic algorithm')
    parser.add_option('--popsize', type=int, default=4, help='Number of individuals for the genetic algorithm')
    parser.add_option('--renewal-rate', type=int, default=1, help='Number of individual to renew at each step',
                      dest='renewal_rate')
    parser.add_option('--flags', default='-O0', help='Optional added arguments to the compiler')
    parser.add_option('--test', help='Optionnal test script for benchmarking code', dest='test')
    parser.add_option('--bench-iter', default=50, type=int, help='Number of iteration for benchmarking',
                      dest='get_time')
    parser.add_option('--unit-test', action='store_true', help='perform some unit test', dest='unit_test')
    parser.add_option('--out', help='directory to store result in')
    parser.add_option('--blork', action='store_true', help='Leave a real mess of temporary files, useful for debug')
    parser.add_option('-v', action='count', help='be very talkative', dest='verbose')
    parser.add_option('--debug', action='store_true', help='turn on debug messages')

    (args, files) = parser.parse_args()
    args.sources = files

    if args.blork:
        blork()

    if args.unit_test:
        UnitTest(args).check()

    # verify some settings
    if not args.sources:
        raise Exception('You need to input at least one source file')
    if not isinstance(args.sources, list):
        args.sources = [args.sources]
    available_algos = {'genetic': Genetic, 'greedy': Greedy, 'full': Full}
    args.algo = available_algos[args.algo]

    if args.test:
        if not os.path.isfile(args.test):
            raise Exception("Test file '%s' does not exist" % args.test)
        elif not os.access(args.test, os.X_OK):
            raise Exception("Test file '%s' not executable" % args.test)
    else:
        print('No test file provided, defaulting to bare a.out')

    if 2 * args.renewal_rate > args.popsize:
        print('Warning, renewal rate greater than half the population size, adjusting')
        args.renewal_rate = args.popsize / 2

    if args.out:
        outdir = args.out
        if os.path.exists(outdir):
            print('Warning, {} already exists'.format(outdir), end=' ')
        counter = 0
        while os.path.exists(outdir):
            outdir = '{}{}'.format(args.out, counter)
            counter += 1
        args.out = outdir
        os.mkdir(args.out)
        print(', using {} instead'.format(outdir))
    else:
        args.out = tempfile.mkdtemp(dir='.', prefix='pypsearch_')
        print('No output dir provided, defaulting to {}'.format(args.out))

    if args.log:
        args.log = open(args.log, 'w')

    os.environ['PIPS_CPP_FLAGS'] = args.flags

    ParseConfigFile(args)
    return args


def pypsearch():
    """"""
    print('Initializing Pypsearch')
    args = ParseCommandLine()

    # init 
    workspacedir = getwdir(args.sources)
    if os.path.exists(workspacedir):
        shutil.rmtree(workspacedir)
    os.mkdir(workspacedir)
    for x in args.sources:
        shutil.copy(x, workspacedir)

    # launch algo
    results = []
    print('Running %s algorithm' % args.algo.__name__)
    with args.algo(args) as algo:
        results = algo.run()
    print('Best element in {} with score {}'.format(args.out, results[0].execution_time))

    bestsources = [os.path.join(workspacedir, results[0].foutname, os.path.basename(x)) for x in args.sources]
    for x in bestsources:
        shutil.copy(x, args.out)

    if args.log:
        print('-- best results', file=args.log)
        original = Individual(args)
        original.rate()
        original.rip()
        for r in results:
            print(r, file=args.log)
            print('--', file=args.log)
        print('-- original result --', file=args.log)
        print(original, file=args.log)
        print('done !', file=args.log)

    if not args.blork:
        shutil.rmtree(workspacedir)


# nice kid paddle ref
def blork():
    print("""
         ... .MMZ                       
        .N~.M.~ M                       
          MM+MMM              .MII,     
         .:,M.DN,..         . ..$~      
        ,M D MMN .7 ..      MMM.M.. N.  
        ....... MM .O ..~ M,.MI8,$. .   
            M.... MN=,INM~ ...ZM: 8     
             .M $   ...   .:.OM. D      
            :$:.   .MM.    .MD          
        . 8M  . ...MMM,..  .MM..        
   .~~. ...  M, $.MMMMM:   .O.+         
  . ...$.~8.   . ?MMM MZ. .MMM.         
    :MM.M..,,M~M MMM.M.~:..N  MD.       
   .. .N...N:.MM NO    MMN. ,..       
      .M. .   N M .MZ.  .? ~D.          
     ..M..O.I 7 MMM  ...                
     .MN..M8. ~ MMM,MM,.    ..          
   . .MM      M NM+  . M.   MI.MZM.     
     M M$     .D M     ~ MM.=M.~M:M.    
  M... :=..             O=D M ? .M.     
 ..~OMM...          M.MM 8, O~.     
. M. M7.M$.  D7 ....MM .  ? :           
     . ...      ...      O.M.           
                          .             
""")


if __name__ == '__main__':
    pypsearch()
