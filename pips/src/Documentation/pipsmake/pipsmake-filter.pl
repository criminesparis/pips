#! /usr/bin/perl -w
#
# $Id: pipsmake-filter.pl 23065 2016-03-02 09:05:50Z coelho $
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

# process "pipsmake-rc.tex" to extract some/all stuff

use strict;

my $makes = 0;
my $props = 0;
my $alias = 0;
my $subset = undef; # filename
my %keep = ();

use Getopt::Long;
GetOptions('makes' => \$makes,
	   'props' => \$props,
	   'alias' => \$alias,
	   'subset=s' => \$subset)
or die "invalid options";

die "expecting an operation"
  unless $makes or $props or $alias;

# restrict pips to a subset of passes provided in a file
if (defined $subset)
{
  open FILE, "<$subset" or die $!;
  while (<FILE>)
  {
    # spacing...
    s/^\s+//; s/\s+$//;
    # skip comments
    next if /^#/;
    die "unexpected format: $_" if /\s/;
    $keep{$_} = 1 if /./;
  }
  close FILE;
  #print STDERR "keeping: ", join(" ", keys %keep), "\n"
}

my $what = $props? 'PipsProp': 'PipsMake';
my $pass = undef;

while (<>)
{
  # fix spacing and other
  s/\t/ /g;
  s/^\s+/    /g;
  s/^\s+(\w)/$1/;
  s/ +$//;
  # skip latex comments
  next if /^\s*%/;
  if (/^\s*\\begin\{$what\}/ ... /^\s*\\end\{$what\}/)
  {
    next if /\{$what\}/ or /^\s+$/;

    #print "current: $_";

    # current pass (name must start in lowercase)
    $pass = $2 if /^(alias\s+)?([a-z][a-zA-Z0-9_]+)\s/;

    next if $subset and (not defined $pass or not exists $keep{$pass});

    if ($alias)
    {
      print if /^\s*alias\s/;
    }
    else
    {
      next if /^\s*alias\s/;
      # skip line before a new rule or property
      print "\n" if /^\s*[a-zA-Z]/;
      print;
    }
  }
}
