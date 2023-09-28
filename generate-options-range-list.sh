#!/bin/sh
egrep "  OPTION \(" options.h |\
grep -v "\<double," |\
sed -e "s/\<bool,//" \
    -e 's/\<unsigned,//' \
    -e 's/,[^,]*$//' \
    -e 's/\<OPTION//' \
    -e 's/,/ /g' \
    -e 's,^[^(]*(,,' |\
awk '{printf "%s %d %d %d\n", $1, $2, $3, $4}' |\
grep -v "witness"
