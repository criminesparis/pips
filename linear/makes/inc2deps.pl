#!/usr/bin/perl -w
#
# $Id: inc2deps.pl 1213 2015-07-19 19:09:07Z coelho $
#
# only keep pips libraries from dependencies "lib1:lib2"
# (c) MINES ParisTech 2015, this script is LGPL.

use strict;

my %libs = ();
for my $l (@ARGV) {
  $libs{$l} = 1;
}

while (<STDIN>) {
  my ($l, $d) = split /[:\n]/;
  print if exists $libs{$d} and $l ne $d;
}
