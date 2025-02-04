#!/bin/bash
#
# $Id: inc2deps.sh 1213 2015-07-19 19:09:07Z coelho $
#
# yet another dependency-related script...
# generate library make-dependencies based on declared includes
# (c) MINES ParisTech 2015, this script is LGPL.

# find inc2deps.pl here...
PATH=${0%/*}:$PATH

dirs=''
for path ; do
  if [ -d $path ] ; then
    dirs+=" ${path##*/}"
  fi
done

echo '# automatically generated include dependencies'

for path ; do
  if [ -d $path ] ; then
    lib=${path##*/}
    grep '^ *# *include *' $path/*.[cylh] |
    perl -n -e "print \"$lib:\$1\\n\" if /include *\"([^\"]*)\.h\"/" |
    sort -u
  fi
done | inc2deps.pl $dirs
