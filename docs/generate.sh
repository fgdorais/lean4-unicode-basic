#! /bin/bash

set -eo pipefail

DOCGEN4="$1/.lake//build/bin/doc-gen4"
MODULES="UnicodeBasic $(find UnicodeBasic -name '*.lean' | sed 's/.lean//;s/\//./g')"

if [ -x $DOCGEN4 ] ; then
    for mod in $MODULES ; do
        echo "Generating ${mod}"
        lake env $DOCGEN4 single $mod "https://github.com/fgdorais/lean4-unicode-basic"
    done
    echo "Generating core"
    lake env $DOCGEN4 genCore
    echo "Generating index"
    lake env $DOCGEN4 index "https://github.com/fgdorais/lean4-unicode-basic"
    cp -r .lake/build/doc/* ./docs
else
    echo "error: missing doc-gen4 binary" >&2
    exit 1
fi
