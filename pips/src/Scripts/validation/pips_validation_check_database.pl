#! /usr/bin/perl -w
#
# $Id: pips_validation_check_database.pl 22966 2015-12-02 15:41:23Z coelho $
#
# check tpips/test files for the pips database name
# warn if the name does not match the test case...
# this allow to detect script which break parallel validation assumptions
#

use strict;

for my $file (@ARGV)
{
  # expected db name
  my $name = undef;
  $name = $2 if $file =~ /^(.*\/)?([-_A-Za-z0-9]+?)\.(tpips2?|test)$/;
  die "no name for file: $file" unless defined $name;

  # read file
  open FILE, $file or die "cannot open: $file";
  my $lineno = 0;
  while (<FILE>)
  {
    $lineno ++;
    print "dbname: $2 (\"$file\":$lineno)\n"
      if /^\s*(create|delete)\s+([-_A-Za-z0-9]+)/ and $2 ne $name;
  }
  close FILE;
}
