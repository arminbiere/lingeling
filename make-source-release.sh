#!/bin/sh

if [ -t 2 ]
then
  BOLD="\033[1m"
  GREEN="\033[1;32m"
  NORMAL="\033[0m"
  RED="\033[1;31m"
  YELLOW="\033[1;33m"
else
  BOLD=""
  GREEN=""
  NORMAL=""
  RED=""
  YELLOW=""
fi

script=`basename $0`

die () {
  echo "${BOLD}$script: ${RED}error:${NORMAL} $*" 1>&2
  exit 1
}

msg () {
  echo "$script: $*" 1>&2
}

wrn () {
  echo "${BOLD}$script: ${YELLOW}warning:${NORMAL} $*" 1>&2
}

full=no
force=no
tar=""

usage () {
cat <<EOF
usage: $script [-h|--help] [-f|--force] [-full] [-t <file>]
EOF
exit 0
}

while [ $# -gt 0 ]
do
  case "$1" in
    -h|--help) usage;;
    -f|--force) force=yes;;
    --full) full=yes;;
    -t)
      shift
      [ $# = 0 ] && die "argument to '-t' missing"
      tar="$1"
      ;;
    *) die "invalid option '$1' (try '-h')";;
  esac
  shift
done

cd "`dirname $0`"
[ -d .git ] || die "could not find '.git' directory"
FULLID="`git show 2>/dev/null|awk '{print $2; exit}'`"
[ "$FULLID" = "" ] && die "could not get full git ID ('git show' failed)"
if git diff --quiet
then
  CHANGES=no
else
  CHANGES=yes
fi

if [ $force = yes ]
then
  if [ $CHANGES = yes ]
  then
    wrn "uncommitted changes (but forced to continue)"
  else
    msg "no uncommitted changes (no need to use '-f')"
  fi
else
  if [ $CHANGES = yes ]
  then
    die "uncommitted changes ('git commit' or '-f')"
  else
    msg "no uncommitted changes (as expected)"
  fi
fi

SHORTID="`echo $FULLID|sed -e 's,^\(........\).*,\1,'`"
[ "$SHORTID" = "" ] && die "could not get short git ID"
[ -f VERSION ] || die "could not find 'VERSION' file"
VERSION="`cat VERSION`"
[ "$VERSION" = "" ] && die "invalid 'VERSION' file"
NAME=lingeling-$VERSION-$SHORTID
DIR=/tmp/$NAME
ARCHIVE=/tmp/$NAME.tar.xz

if false
then
  msg CHANGES $CHANGES
  msg VERSION $VERSION
  msg FULLID $FULLID
  msg SHORTID $SHORTID
  msg NAME $NAME
  msg DIR $DIR
  msg ARCHIVE $ARCHIVE
  msg LIMIT $LIMIT
fi

if [ -d $DIR ]
then
  msg "reusing '$DIR'"
  rm -rf $DIR/*
else
  msg "new directory '$DIR'"
  mkdir $DIR || exit 1
fi

cp -p \
configure.sh \
COPYING \
getgitid \
lglbnr.c \
lglconst.h \
lgldimacs.c \
lgldimacs.h \
lglib.c \
lglib.h \
lglmain.c \
lgloptl.h \
lglopts.c \
lglopts.h \
makefile.in \
mkconfig.sh \
README \
VERSION \
$DIR

if [ $full = yes ]
then
  cp -p \
  lglmbt.c \
  lgluntrace.c \
  lglddtrace.c \
  ilingeling.c \
  plingeling.c \
  treengeling.c \
  $DIR
else
  sed -i \
    -e "s,^targets: lingeling.*,keep: lingeling," \
    -e "/^targets:/d" \
    -e "s,^keep:,targets:," \
    $DIR/makefile.in
fi

msg "generating archive '$ARCHIVE'"

rm -f $ARCHIVE
cd /tmp
tar cJf $ARCHIVE $NAME || exit 1
msg "generated '${GREEN}$ARCHIVE${NORMAL}'"
BYTES="`ls --block-size=1 -s $ARCHIVE 2>/dev/null |awk '{print $1}'`"
msg "archive has $BYTES bytes"

if [ "$tar" = "" ]
then
  echo "$ARCHIVE"
else
  echo "$ARCHIVE" > "$tar"
  msg "wrote archive name to '$tar'"
fi

exit 0
