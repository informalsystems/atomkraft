#!/usr/bin/env bash
#
# Run the server in the docker container

CHAINID="4040"
MONIKER="localtestnet"

# Run the node.
# Expose the port 1317 for REST endpoint (Cosmos).
docker run --rm --name "cosmos-container" \
    -p 0.0.0.0:1317:1317 \
    -i cosmos-image \
    /usr/bin/simd start \
    --pruning=nothing \
    --trace \
    --minimum-gas-prices=0.0001stake \
    --p2p.pex=false --p2p.upnp=false \
    --p2p.laddr=tcp://127.0.0.1:26656 \
    --address=tcp://0.0.0.0:26658 \
    --grpc.enable=false
