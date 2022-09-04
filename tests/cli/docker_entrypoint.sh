#!/usr/bin/env bash

# See https://sipb.mit.edu/doc/safe-shell/
set -eu -o pipefail

# Run the following command from `atomkraft/tests/cli` directory
# docker run -it --rm -v $(readlink -f ../../):/atomkraft $(docker build -q .)

cd /atomkraft

poetry install -n

. $(poetry env info -p)/bin/activate
eval $(opam env)

cd tests/cli

function cleanup {
  echo "Removing transfer/"
  rm -rf transfer/
}

trap cleanup EXIT

for f in `ls *md`; do
    echo "testing ${f} ..."
    ocaml-mdx test -v "${f}"
    [ ! -f "${f}.corrected" ] || (diff -u "${f}" "${f}.corrected" && exit 1)
done
