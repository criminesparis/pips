#! /bin/sh
#
# $Id: test_newgen_type_translation.sh 1297 2011-12-31 08:16:18Z coelho $
#
# test type translation...
#

test $# -eq 1 || {
    echo "USAGE: $0 database-directory"
    exit 1;
}

database=$1
newgen=$1/Metadata/database.NEWGEN
mv $newgen $newgen.old

test_newgen_type_translation.pl $1/*/* < $newgen.old > $newgen
