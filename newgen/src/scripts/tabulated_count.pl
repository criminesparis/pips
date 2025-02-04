#! /usr/bin/perl -wn
#
# $Id: tabulated_count.pl 1297 2011-12-31 08:16:18Z coelho $ 
#
# reports the number of tabulated definitions in a file
#

@l = /DT\d+ /g;
$n += @l;

END {
  print "number of tabulated definitions: $n\n";
}
