#! /bin/bash

set -eo pipefail

DOCGEN4="$1/build/bin/doc-gen4"
MODULES="UnicodeBasic $(find UnicodeBasic -name '*.lean' | sed 's/.lean//;s/\//./g')"

if [ -x $DOCGEN4 ] ; then
    for mod in $MODULES ; do
        echo "Generating ${mod}"
        lake env $DOCGEN4 single $mod
    done
    echo "Generating core"
    lake env $DOCGEN4 genCore
    echo "Generating index"
    lake env $DOCGEN4 index
    cp -r ./build/doc/* ./docs
else
    echo "error: missing doc-gen4 binary" >&2
    exit 1
fi
