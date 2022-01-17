#!/usr/bin/env python3
#
# Replay a trace in the Informal Trace Format in a blockchain.
# This script is tuned towards the cosmos-sdk blockchain.
#
# Requires atomkraft-informal.
#
# Igor Konnov, 2021-2022
#
#   Copyright 2022 Informal Systems
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.


import getopt
import json
import os.path
import sys
import time

from atomkraft.cosmos import *
from atomkraft.itf_parser import trace_from_itf_file, ItfError

# the Cosmos binary to execute
COSMOS_BIN='./client.sh'

# Cosmos REST API
COSMOS_REST='http://localhost:1317'

# Cosmos accounts that we are using for testing.
COSMOS_ACCOUNTS = {
    "user1": {
        "addr": "cosmos19ftpcggezgal5ascglq5m022z4e453khqatpml"
    },
    "user2": {
        "addr": "cosmos1evyv7neax9qtxxzuexnhylxyz4guvsyjmwauct"
    },
    "user3": {
        "addr": "cosmos1fa4283r2r6xfumedmtp68c2j9h82jvspvfe7sh"
    },
    "validator": {
        "addr": "cosmos1uquty6wqc03pqpmz0t5fzh4fd5npfpd23wgr7l"
    }
}

# We have only one validator (set up in the genesis)
COSMOS_VALIDATOR_ADDR = "cosmosvaloper1uquty6wqc03pqpmz0t5fzh4fd5npfpd256ukjv"


def tx_to_fun(scriptf, state):
    """Translate a transaction to a list of callables"""

    def compareBalances(account):
        expected_bal = state["balanceOf"][account] + state["unbonded"][account]
        # retrieve the balances from the node
        addr = COSMOS_ACCOUNTS[account]["addr"]
        balances = CosmosBalance(COSMOS_REST, addr).call()
        cosmos_bal = \
          [ int(coin["amount"])
                  for coin in balances["balances"]
                  if coin["denom"] == "stake" ][0]

        print(f'cosmos balance:   {cosmos_bal}')
        print(f'expected balance: {expected_bal}')
        return cosmos_bal <= expected_bal

    tx = state["lastTx"]
    # tx staking
    if tx["tag"] == "delegate":
        def fun():
            coin = "{d}stake".format(d=int(tx["value"]))
            sender = COSMOS_ACCOUNTS[tx["sender"]]["addr"]
            args = ["tx", "staking", "delegate",
                    COSMOS_VALIDATOR_ADDR, coin, "--from", sender]
            result = CosmosCmd(scriptf, COSMOS_BIN, args, []).call()
            # check that the balance of the sender has decreased as expected
            return result != None and result and compareBalances(tx["sender"])

        return fun
    elif tx["tag"] == "unbond":
        def fun():
            coin = "{d}stake".format(d=int(tx["value"]))
            sender = COSMOS_ACCOUNTS[tx["sender"]]["addr"]
            args = ["tx", "staking", "unbond",
                    COSMOS_VALIDATOR_ADDR, coin, "--from", sender]
            result = CosmosCmd(scriptf, COSMOS_BIN, args, []).call()
            # check that the balance of the sender has increased as expected
            return result != None and result and compareBalances(tx["sender"])

        return fun
    # tx bank send
    elif tx["tag"] == "transfer-cosmos":
        def fun():
            coin = "{d}stake".format(d=int(tx["value"]))
            sender = COSMOS_ACCOUNTS[tx["sender"]]["addr"]
            receiver = COSMOS_ACCOUNTS[tx["toAddr"]]["addr"]
            args = ["tx", "bank", "send",
                    sender, receiver, coin, "--from", sender]
            result = CosmosCmd(scriptf, COSMOS_BIN, args, []).call()
            # did the transaction succeed?
            return result != None and result

        return fun
    elif tx["tag"] == "None":
        return lambda: True
    else:
        print("Unexpected transition: " + tx["tag"], file=sys.stderr)
        return lambda: not tx["fail"]


def print_usage_and_exit():
    print("Use: {name} [--script name.sh] counterexample.itf.json" \
            .format(name = sys.argv[0]))
    print("  --script specifies the name of the bash script to output")
    sys.exit(99)


def parse_args():
    """Parse the command-line arguments"""

    try:
        opts, args = getopt.getopt(sys.argv[1:], "h", ["help", "script="])
        if len(args) < 1:
            print_usage_and_exit()

        filename = args[0]
        print('Input: {f}'.format(f = filename))

        scriptf = None
        for o, a in opts:
            if o == "--script":
                print('Output: {f}'.format(f=a))
                scriptf = open(a, "w+")
            elif o == "--help":
                print_usage_and_exit()
            else:
                print("Unexpected option: " + o)
                print_usage_and_exit

        return (filename, scriptf)
    except getopt.GetoptError as err:
        print(err)
        print_usage_and_exit()


if __name__ == "__main__":
    # parse the arguments and the trace
    (filename, scriptf) = parse_args()        
    try:
        trace = trace_from_itf_file(filename)
    except ItfError as err:
        print("Error in trace", file=sys.stderr)
        print(err.message, file=sys.stderr)
        sys.exit(10)

    # initialize the output script
    print("#!/usr/bin/env bash", file=scriptf)
    print(f"# Generated by atomkraft of Informal Systems on {time.asctime()}\n\n",
            file=scriptf)
    print("set -e", file=scriptf)

    # extract transactions from the states
    trimmed_states = trace["states"][1:]

    # translate the transactions into callables
    callables = [ (state, tx_to_fun(scriptf, state)) for state in trimmed_states]
    # execute all callables and check their status
    for (tx_no, (state, fun)) in enumerate(callables):
        no_fail = fun()
        if no_fail == state["lastTx"]["fail"]:
            print(f"Transaction {tx_no} has failed", file=sys.stderr)
            sys.exit(1)
    else:
        print("Executed {n} transactions".format(n = len(trimmed_states)))

