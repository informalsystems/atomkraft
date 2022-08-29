#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

MDX=ocaml-mdx
TRACES_DIR="./traces/"
MD_FILES="${1:-*.md}"

if ! command -v $MDX &> /dev/null; then
    echo "$MDX could not be found"
    echo "Please install MDX (https://github.com/realworldocaml/mdx)"
    exit 1
fi

eval $(opam env)

SCRIPT_EXIT_CODE=0

test_file() {
    echo "Testing file $1..."
    $MDX test -v $1
    if [ -f "$1.corrected" ]; then
        echo "FAILED: see $1.corrected"
        SCRIPT_EXIT_CODE=1
    else
        echo "OK"
    fi
}

for MD_FILE in $MD_FILES; do
    test_file $MD_FILE
done

if (( $SCRIPT_EXIT_CODE != 0 )); then
    echo "Some tests failed"
    exit $SCRIPT_EXIT_CODE
fi
