#! /bin/bash
#
# $Id: check_pips_valid.sh 22805 2015-09-06 08:05:02Z coelho $
#
# check whether pips validation contains bugs or laters.
#
# usage: $0 warn crit /path/to/validation
#
# status summary:
# - UNKOWN: cannot conclude, error in running script
# - CRITICAL: there are bugs in the validation
# - WARNING: there are laters (futures/features) in the validation
# - OK: no bugs nor laters

# for nagios?
PATH=/usr/lib/nagios/plugins:$PATH

name='PIPS validation'
function res()
{
  local status=$1 msg=$2
  case $status in
    0) echo "$name OK: $msg";;
    1) echo "$name WARNING: $msg";;
    2) echo "$name CRITICAL: $msg";;
    3) echo "$name UNKNOWN: $msg";;
    *) echo "$name ERROR: $msg";;
  esac
  exit $status
}

[ $# -eq 3 ] || res 3 "expecting at least 3 args"

warn=$1 crit=$2 valid=$3
shift 3

# validation directory must exist
cd $valid || res 3 "no such directory '$valid'"

type check_file_age > /dev/null 2>&1 || res 3 "check_file_age not found"
check_file_age -w $warn -c $crit .svn > /dev/null || \
  res $? "svn update '$validation'"

# check for bugs and laters
nbugs=$(find . -name '*.bug' -print | wc -l)
nlaters=$(find . -name '*.later' -print | wc -l)

# bugs => CRITICAL
[ $nbugs -ne 0 ] && res 2 "$nbugs bugs and $nlaters laters in '$valid'"

# later => WARNING
[ $nlaters -ne 0 ] && res 1 "no bug but $nlaters laters in '$valid'"

# could check the validation status...
# but this is already done in check_pips_status.sh
res 0 "'$validation' is fine"
