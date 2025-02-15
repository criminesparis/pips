#! /bin/bash
#
# $Id: check_pips_status.sh 23368 2017-03-14 17:19:18Z coelho $
#
# check pips compilation & validation status for nagios
# this scripts assumes a setup with pips_check_compile
#
# usage: $0 warn crit /path/to/prod [/path/to/validation...]
#
# status summary:
# - UNKOWN: cannot conclude, error in running script
# - WARNING/CRITICAL: if the compilation/validation are not up to date
# - WARNING: pips validation is failing
# - CRITICAL: pips compilation is failing

# for nagios?
PATH=/usr/lib/nagios/plugins:$PATH

function res()
{
  local status=$1 msg=$2
  case $status in
    0) echo "Pips OK: $msg";;
    1) echo "Pips WARNING: $msg";;
    2) echo "Pips CRITICAL: $msg";;
    3) echo "Pips UNKNOWN: $msg";;
    *) echo "Pips ERROR: $msg";;
  esac
  exit $status
}

[ $# -ge 3 ] || res 3 "expecting at least 3 args"

warn=$1 crit=$2 prod=$3
shift 3

# the name is taken from the basename of the directory
name=$(basename $(dirname $prod))

# for svn 1.9
if test -f $prod/.svn/wc.db ; then
  wc=.svn/wc.db
else
  wc=.svn
fi

# compilation status
cd $prod || res 3 "$name no prod directory '$prod'"
check_file_age -w $warn -c $crit $wc > /dev/null || \
  res $? "$name svn update"
check_file_age -w $warn -c $crit CURRENT > /dev/null || \
  res $? "$name CURRENT file"

test -f STATE || res 3 "$name no STATE file"
read current compile < STATE

case $current in
  ok) ;;
  KO:*)   res 2 "$name state is $current $compile" ;;
  locked) res 3 "$name is locked";;
  *)      res 4 "$name in unexpected state $state $compile" ;;
esac

# validation status
for valid in "$@" ; do
  # ignore empty entries
  [ "$valid" ] || continue
  # else check valid directory
  [ -d $valid ] || res 3 "$name no validation directory '$valid'"
  cd $valid || res 2 "$name cd '$valid'"
  check_file_age -w $warn -c $crit $wc > /dev/null || \
    res $? "$name svn update in $valid"
  summary=SUMMARY.short.saved
  [ -f $summary ] || res 2 "$name no $summary in '$valid'"
  # hmmm... .saved must be regenerated daily
  check_file_age -w 100000 -c 200000 $summary > /dev/null || \
    res $? "$name $summary in $valid"
  status=$(tail -1 $summary)
  read n a v what remain <<EOF
$status
EOF
  case $what in
    SUCCESS) ;;
    ISSUES) res 1 "$name validation failed '$valid' $remain" ;;
    *)      res 3 "$name unexpected status $what in $valid" ;;
  esac
done

res 0 "$name is fine"
