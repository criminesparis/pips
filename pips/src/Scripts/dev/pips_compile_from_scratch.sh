#!/bin/bash
#
# $Id: pips_compile_from_scratch.sh 23651 2021-03-15 09:35:59Z coelho $
#
# Compile PIPS from scratch in a temporary directory.
# This contrasts with script "pips_check_compile" which does a faster
# "svn up" to get up-to-date sources and validation.
# Can be run from cron.
#
# $0 [setup_pips.sh options] name log [email]

url="https://scm.cri.mines-paristech.fr/svn/nlpmake/trunk/makes/setup_pips.sh"
dir="/tmp/pips_compile_from_scratch.$$"

is_dynamic=
python=python

# options are passed to setup_pips.sh
options=
while [[ "$1" == -* ]] ; do
  [ "$1" == '--dynamic' ] && is_dynamic=1
  if [[ "$1" == --py* ]] ; then
    python=${1#*=}
    python=${python%-config}
    is_dynamic=1
  fi
  options+=" $1"
  shift
done

# get arguments
name=$1 log=$2 email=$3

# extract revision number
ID='$Id: pips_compile_from_scratch.sh 23651 2021-03-15 09:35:59Z coelho $'
version=${ID//*.sh /}
version=${version// */}

function report()
{
  local status=$1 message=$2
  echo "$name: $message" >&2
  if [ ! "$log" ] ; then
    echo "no log file, exiting without a report" >&2
    exit $status
  fi
  {
      echo "script: $0"
      echo "version: $version"
      echo "name: $name"
      echo "host: $(hostname)"
      echo "dir: $dir"
      echo "setup: $url"
      echo "options: $options"
      echo "python: $python"
      svn info $url | sed -n \
	  -e 's/Last Changed Rev: /revision: /p' \
	  -e 's/Last Changed Date: /date: /p'
      echo "duration: ${SECONDS}s"
      echo "status: $status"
      echo "message: $message"
      lsb_release -d

      if [ $status != 0 ] ; then
        echo
        echo "### OUT/ERR"
        test -f out && tail -200 out
      fi
  } > $log
  # report is public, for nagios
  chmod a+r $log
  if [ "$email" ] ; then
    mail -s "$name $message" $email < $log
  else # report on stdout, cron should send a mail
    [ $status -ne 0 ] && cat $log
  fi
  exit $status
}

# various check & setup
# at least 2 arguments
test $# -ge 2 || report 1 "usage: $0 [opts] name log [email]"
mkdir $dir || report 2 "cannot create $dir"
cd $dir || report 3 "cannot cd to $dir"

# start recording on out
set="./setup.sh"
type curl >> out 2>&1 || report 4 "curl not found"
curl -L -s -o $set $url >> out 2>&1 || report 5 "cannot get $url"
chmod u+rx $set >> out 2>&1 || report 6 "cannot chmod $set"

# must compile pips under 20 minutes
type timeout >> out 2>&1 || report 7 "no timeout command"
timeout 20m $set $options PIPS calvin export < /dev/null >> out 2>&1 || \
  report 8 "error running $set"

######################################################################## CHECKS

# simple checks
root=$dir/PIPS/prod/pips
test -d $root || report 10 "no pips directory: $root"

arch=$root/makes/arch.sh
test -x $arch >> out 2>&1 || report 11 "no arch script: $arch"

tpips=$root/bin/$($arch)/tpips
test -x $tpips >> out 2>&1 || report 12 "no generated tpips ($tpips)"

# to help debug
{
  echo "# pipsrc.sh:"
  cat ./PIPS/pipsrc.sh
} >> out 2>&1

# run something!
source ./PIPS/pipsrc.sh >> out 2>&1 || \
  report 13 "cannot source pips environment"

# create a simple C program
cat > foo.c 2>> out <<EOF
#ifndef N
#define N 3
#endif
int main(void) {
  int i = N;
  i -= N;
  return 0;
}
EOF

# basic tpips script
cat > foo.tpips 2>> out <<EOF
create foo foo.c
activate PRINT_CODE_PRECONDITIONS
display PRINTED_FILE
close
delete foo
EOF

$tpips foo.tpips > tpips.out 2>&1 || report 14 "cannot run tpips ($tpips)"
grep '{i==0}' tpips.out >> out 2>&1 || report 15 "precondition 0 not found"

# and possibly with pyps
if [ "$is_dynamic" ] ; then
  ipyps=$root/bin/ipyps
  test -x $ipyps || report 16 "no generated $ipyps"

  cat > foo.py 2>> out <<EOF
from pyps import workspace, module
w = workspace('foo.c', cppflags='-DN=5', deleteOnClose=True)
w.fun.main.display(module.print_code_preconditions)
w.close()
EOF

  $python foo.py > pyps.out 2>&1 || report 17 "cannot run pyps"
  grep '{i==5}' pyps.out >> out 2>&1 || report 18 "precondition 5 not found"
fi

# final cleanup
cd $HOME
rm -rf $dir > /dev/null 2>&1 || report 19 "cannot remove directory"

# done
report 0 "pips scratch compilation ok"
