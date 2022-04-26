#!/usr/bin/env bash
#
# Execute the client in a running container.

# if you don't want automatic confirmation, call YES="" ./client.sh
ARG_YES=${YES:-"--yes"}

CHAINID="4040-1"
MONIKER="localtestnet"

generate_tx=false
MORE_ARGS="" 

if [ "$1" == "tx" ]; 
then
    for argument in "$@"
    do 
        if [ "$argument" == "--generate-only" ];
        then	
            generate_tx=true
        fi 

    done
            
    if [ "$generate_tx" == "false" ]; 
    then
    	MORE_ARGS=" -b block --fees 100000stake $ARG_YES"
    fi      
fi

CHAIN_ARGS="simd "$@$MORE_ARGS

docker exec -i cosmos-container sh -c "$CHAIN_ARGS"
#--chain-id "$CHAINID"
