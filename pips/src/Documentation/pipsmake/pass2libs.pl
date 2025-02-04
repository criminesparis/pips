#! /usr/bin/perl -w
#
# $Id: pass2libs.pl 23130 2016-07-01 13:42:39Z coelho $
#
# generate a list of libraries for a subset of pips.

use strict;
use warnings;

die "usage: $0 dependences passes" unless @ARGV == 2;

my ($deps, $passes) = @ARGV;

# hard coded library dependencies
# note that they may be different from includes,
# as includes can be conditional to a library availability
my %LIBDEPS = (
  # seems ok? could pointer stuff be avoided? also simple?
  # removed: alias-classes, points-to?
  'effects-convex' => ['effects-simple', 'semantics', 'conversion',
		       'effects-generic',
		       # pointer analysis... what is really required?
		       'pointer_values' ],
  # ok
  'effects-simple' => ['effects-generic'],
  # removed: convex, alias-classes
  # conditional: points-to
  'effects-generic' => ['effects-util'],
  # ok
  'hyperplane' => ['paf-util'],
  # ok
  'hpfc' => ['effects-convex', 'semantics', 'conversion'],
  # ok
  # conditional(path_transformer): 'effects-*' 'points-to'
  'semantics' => ['transformer',
		  # NO!?
		  'c_syntax'],
  # ok
  'wp65' => ['movements'],
  # removed: complexity, simple, convex, semantics...
  # ok
  'icfg' => [],
  # C depends on Fortran?... "syntax-util" is missing?
  'c_syntax' => ['preprocessor'],
  # rmake is called?
  'callgraph' => ['pipsmake'],
  # prettyprint? make_text_resource_and_free
  #   somehow necessary for debug? I'm not sure...
  # effects-util: hmmm, just for one function...
  # preprocessor??
  'syntax' => ['prettyprint','preprocessor'],
  # ??? hmmm... probably each preprocessor should be with its parser
  'preprocessor' => [],
  # hmmm some cleanup is still required: icfg?
  # removed: instrumentation, transformations, alias-classes
  'ricedg' => ['rice', 'icfg', 'effects-generic', 'control', 'semantics' ],
  # removed: transformations
  'rice' => [],
  # removed: instrumentation, accel-util (moved manage_pragma.c)
  # hidden: reductions, chains, simple, convex...
  'transformations' => [],
  # ok
  'instrumentation' => ['effects-convex'],
  # ok?
  # removed: transformations, ricedg
  'alias-classes' => ['effects-convex', 'effects-simple',
		      'effects-generic', 'semantics', 'transformer' ],
  # syntax?
  'prettyprint' => [],
  # ok
  # xml_prettyprint requires complexity and convex... idem claire
  'modeling' => ['complexity', 'effects-convex'],
  'accel-util' => ['expressions', 'ricedg', 'complexity'],
  # removed: alias-classes
  'transformer' => [],
  # removed: atomizer, ricedg, syntax, prettyprint
  'ri-util' => ['pipsdbm'],
  # ok, they are probably needed
  'atomizer' => ['effects-util','effects-generic'],
  # removed 'flint' (type_checker moved to bootstrap)
  # ok
  'bootstrap' => [],
  # ok
  'complexity' => ['prettyprint'],
  # ok
  'flint' => ['effects-util'],
  # ok? chains may be combuted based on simple or convex effects
  'chains' => ['effects-generic'],
  # ??? because of forward_substitution
  'expressions' => [ 'ricedg' ],
  # locality?
  # reindexing?
  # janusvalue?
);

# hard coded for the linker (hmmm... does not really work anyway?)
# note: probably needs to be updated when a new library is added
my @ORDER = qw( top-level pipsmake syntheses static_controlize paf-util
    wp65 hpfc hyperplane to_begin_with instrumentation locality
    expressions transformations accel-util hwac movements bootstrap
    callgraph chains complexity conversion modeling prettyprint atomizer
    c_syntax syntax alias-classes points-to effects-simple pointer_values
    effects-convex effects-generic icfg comp_sections semantics control
    continuation ricedg rice pipsdbm transformer preprocessor effects-util
    ri-util step properties text-util misc reductions flint sac safescale
    phrase gpu scalopes newgen pocc-interface taskify rstream_interface
    regions_to_loops task_parallelization workspace-util
  );

my %ORDER;
for my $i (0 .. $#ORDER) {
  $ORDER{$ORDER[$i]} = $i;
}

# these libs are always needed, whatever
my @LIBS = qw(pipsmake pipsdbm properties ri-util misc top-level
	      callgraph newgen text-util control naming workspace-util
	   );
my %LIBS;
for my $l (@LIBS) {
  $LIBS{$l} = 1;
}

# add generated deps
my %DEPS;
open DEPS, "<$deps" or die "cannot open $deps: $!";
while (<DEPS>) {
  my ($pass, $lib) = split /[:\s]/;
  $DEPS{$pass} = $lib;
}
close DEPS;

# get passes
open PASSES, "<$passes" or die "cannot open $passes: $!";
my @passes = grep /^\s*[a-z]/, <PASSES>;
close PASSES;
chomp @passes;

for my $p (@passes) {
  warn "unkown pass: $p" unless exists $DEPS{$p};
  $LIBS{$DEPS{$p}} = 1;
  # conditional dependency
  $LIBS{icfg} = 1 if $p =~ /_icfg/;
}

# compute transitive closure on dependencies
my $changed = 1;
while ($changed) {
  $changed = 0;
  for my $l (keys %LIBS) {
    if (exists $LIBDEPS{$l}) {
      for my $dl (@{$LIBDEPS{$l}}) {
	if (not exists $LIBS{$dl}) {
	  $LIBS{$dl} = 1;
	  $changed = 1;
	}
      }
    }
  }
}

# final result
print join(' ', sort { $ORDER{$a} - $ORDER{$b} } keys %LIBS), "\n";
