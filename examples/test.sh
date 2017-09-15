#!/bin/sh
# Script to test the set of current examples

VERBOSE=no
if [ "$1" = "-v" ] ; then
  VERBOSE=yes
fi

# Options for the contract prover
CPOPTS=-s

/bin/rm -rf .curry
ECODE=0
FAILEDTESTS=

for p in *.curry ; do
  if [ $VERBOSE = yes ] ; then
    curry-ctopt $CPOPTS $p | tee test.out
  else
    curry-ctopt $CPOPTS $p > test.out
  fi
  if [ "`tail -1 test.out`" != "ALL CONTRACTS VERIFIED!" ] ; then
    echo "$p: FULL CONTRACT VERIFICATION FAILED!"
    FAILEDTESTS="$FAILEDTESTS $p"
    ECODE=1
  fi
  rm test.out
done
if [ $ECODE -gt 0 ] ; then
  echo "FAILURES OCCCURRED IN SOME TESTS:$FAILEDTESTS"
  exit $ECODE
elif [ $VERBOSE = yes ] ; then
  echo "All tests successfully executed!"
fi
