#!/bin/sh
# Script to test the set of current examples

VERBOSE=no
if [ "$1" = "-v" ] ; then
  VERBOSE=yes
fi

/bin/rm -rf .curry
ECODE=0

for p in *.curry ; do
  if [ $VERBOSE = yes ] ; then
    curry-ctopt $p | tee test.out
  else
    curry-ctopt $p > test.out
  fi
  if [ "`tail -1 test.out`" != "ALL CONTRACTS VERIFIED!" ] ; then
    echo "$p: FULL CONTRACT VERIFICATION FAILED!"
    ECODE=1
  fi
  rm test.out
done
if [ $ECODE -gt 0 ] ; then
  exit $ECODE
fi
