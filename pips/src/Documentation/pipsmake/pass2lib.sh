#! /bin/bash
#
# $Id: pass2lib.sh 22578 2015-07-12 05:52:09Z coelho $
#
# map all passes found in a file to their library
#
# input: one pass name per line
# output: pass_name:library

conf=$1 sdir=${2:-.}

# list of passes taken from file, ignore comments and empty lines
passes=$(cat $conf | grep '^ *[a-z]' | tr -d ' ' | tr '\012' '|' | sed 's/|$//')

#echo "passes=$passes" >&2

# look for the containing library
find ${sdir}/../../Libs -type f -name '*.[cyl]' -print |
xargs egrep \
  "^bool  *($passes) *\( *(const )? *(string|char *\*) *[a-z][_a-z0-9]* *\)" |
sed -n 's,.*/Libs/\(.*\)/.*:bool  *\([_a-zA-Z0-9]*\)*.*,\2:\1,p' |
sort
