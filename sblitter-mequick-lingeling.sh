#!/bin/sh
[ x"$SBLITTERLIM" = x ] && SBLITTERLIM=100
[ x"$MEQUICKLIM" = x ] && MEQUICKLIM=1000
prefix=/tmp/sblitter-mequick-lingeling.sh-$$
blocked=$prefix-blocked.cnf
rest=$prefix-rest.cnf
simplified=$prefix-simplified
trap "rm -f $prefix*" 2 11
original=$1
shift
sblitter -v -t $SBLITTERLIM $original $blocked $rest
mequick -v -t $MEQUICKLIM $blocked $simplified -c $rest -a
lingeling -v $simplified $*
rm -f $prefix*
