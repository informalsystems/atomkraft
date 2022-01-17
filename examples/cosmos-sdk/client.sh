#!/usr/bin/env bash
#
# Execute the client in a running container.

# if you don't want automatic confirmation, call YES="" ./client.sh
ARG_YES=${YES:-"--yes"}

CHAINID="4040-1"
MONIKER="localtestnet"

if [ "$1" == "tx" ]; then
    MORE_ARGS="-b block --fees 100000stake $ARG_YES"
else
    MORE_ARGS=""
fi


docker exec -i cosmos-container \
    /usr/bin/simd "$@" $MORE_ARGS
# --chain-id "$CHAINID" 
