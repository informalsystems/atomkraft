import asyncio
import json
import logging
import shlex
import socket
import subprocess
import sys
import tempfile
import time
from contextlib import closing
from pathlib import Path
from subprocess import PIPE, Popen
from typing import Dict, List, Optional, Union

import numpy as np
import requests
import tabulate
import terra_proto.cosmos.tx.v1beta1 as tptx
import tomlkit
from atomkraft.chain import Testnet
from atomkraft.chain.node import Account, AccountId, ConfigPort, Node
from atomkraft.chain.testnet import Testnet
from atomkraft.chain.utils import TmEventSubscribe, get_free_ports, update_port
from atomkraft.utils.project import ATOMKRAFT_INTERNAL_DIR, ATOMKRAFT_VAL_DIR_PREFIX
from betterproto.lib.google.protobuf import Any
from grpclib.client import Channel
from modelator.pytest.decorators import step
from terra_proto.cosmos.auth.v1beta1 import BaseAccount
from terra_proto.cosmos.auth.v1beta1 import QueryStub as AuthQueryStub
from terra_proto.cosmos.base.abci.v1beta1 import TxResponse
from terra_proto.cosmos.base.v1beta1 import Coin
from terra_sdk.client.lcd import LCDClient
from terra_sdk.client.lcd.api.tx import CreateTxOptions
from terra_sdk.core import Coins
from terra_sdk.core.bank.msgs import MsgSend
from terra_sdk.core.fee import Fee
from terra_sdk.core.msg import Msg
from terra_sdk.core.tx import TxBody, Tx, AuthInfo
from terra_sdk.key.mnemonic import MnemonicKey


@step("Init")
def init(testnet: Testnet, action, balances):
    logging.info("Step: Init")
    testnet.set_accounts(action.value.wallets)
    testnet.set_account_balances(balances)
    testnet.verbose = True
    testnet.oneshot()
    time.sleep(10)
    logging.info("Status: Testnet launched\n")


@step("Transfer")
def transfer(testnet: Testnet, action):
    action = action.value

    sender_id = action.sender
    receiver_id = action.receiver
    amount = action.amount

    sender_addr = testnet.acc_addr(sender_id)
    receiver_addr = testnet.acc_addr(receiver_id)

    # important that this is imported from terra_sdk, not terra_proto.cosmos
    msg = MsgSend(sender_addr, receiver_addr, f"{amount}{testnet.denom}")

    result = sign_and_broadcast(
        testnet, sender_id, msg, gas=200_000, fee_amount=0)

    logging.info(f"\tSender:    {sender_id} ({sender_addr})")
    logging.info(f"\tReceiver:  {receiver_id} ({receiver_addr})")
    logging.info(f"\tAmount:    {msg.amount}")

    if result.code == 0:
        logging.info("Status: Successful\n")
    else:
        logging.info("Status: Error")
        logging.info(f"\tcode: {result.code}")
        logging.info(f"\tlog:  {result.raw_log}\n")

    logging.debug(f"[MSG] {msg}")
    logging.debug(f"[RES] {result}")

    time.sleep(1)

# tendermock_client.py


DOCKER_PATH = "docker exec -i simapp".split(" ")
SIMD_BINARY = DOCKER_PATH + ["simd"]

TENDERMOCK_HOST = "host.docker.internal"
TENDERMOCK_PORT = "26657"


def sign_and_broadcast(testnet: Testnet,
                       account_id: AccountId,
                       msgs: Union[Msg, List[Msg]],
                       gas: int = 200_000,
                       fee_amount: int = 0,
                       validator_id: Optional[AccountId] = None):

    if not isinstance(msgs, list):
        msgs = [msgs]

    account = testnet.accounts[account_id]
    account_addr = account.address(testnet.hrp_prefix)
    mnemonic = account.mnemonic

    coin_denom = testnet.denom

    body = TxBody(messages=[msg for msg in msgs])
    auth = AuthInfo([], Fee(amount=f"{fee_amount}{testnet.denom}", gas_limit=gas, granter="", payer=""))

    tx = Tx(body=body, auth_info=auth, signatures=[])

    logging.info(json.dumps(tx.to_data()))

    signed_tx = sign_tx(account_addr, mnemonic,
                        testnet.chain_id, tx, testnet.lead_node)
    broadcast_signed_tx(signed_tx, coin_denom, mnemonic, testnet.chain_id,
                        gas, fee_amount, validator_id)


def sign_tx(
        account_addr,
        mnemonic,
        chain_id,
        tx: TxBody,
        lead_node: Node):

    with open("tendermint_client.log", "a") as logfile:

        args = f"query account {account_addr} --node=http://{TENDERMOCK_HOST}:{TENDERMOCK_PORT} --chain-id={chain_id} --output=json"

        logging.info("Calling Cosmos SDK CLI: " + args)

        # get account number and sequence
        cmd = CosmosCmd(
            logfile,
            SIMD_BINARY,
            args.split(
                " "
            ),
            [],
        )
        str_result = cmd.call()
        logging.info("Result: " + str(str_result))
        result = json.loads(str_result)

        account_number = result["account_number"]
        sequence = result["sequence"]

        # store transaction in file
        cmd = CosmosCmd(
            logfile,
            DOCKER_PATH,
            ["tee", "tx_tmp.json"],
            [tx.to_json()],
        )
        cmd.call()

        args = f"tx sign tx_tmp.json --chain-id={chain_id} --from={account_addr} --offline --account-number {account_number} --sequence {sequence} --keyring-backend test --home {lead_node.home_dir}"
        logging.info("Calling Cosmos SDK CLI: " + args)

        # call sign
        cmd = CosmosCmd(
            logfile,
            SIMD_BINARY,
            args.split(
                " "
            ),
            [mnemonic],
        )

        signed_tx = cmd.call()

        return signed_tx


def broadcast_signed_tx(
        signed_tx,
        coin_denom,
        mnemonic,
        chain_id,
        gas: int,
        fee_amount: int,
        validator_id: Optional[AccountId]):

    with open("tendermint_client.log", "a") as logfile:
        # store tx string in file
        cmd = CosmosCmd(
            logfile,
            DOCKER_PATH,
            ["tee", "signed_tx_tmp.json"],
            [signed_tx],
        )
        cmd.call()

        args = f"tx broadcast --node http://{TENDERMOCK_HOST}:{TENDERMOCK_PORT} --fees {fee_amount}{coin_denom} --gas {gas} --chain-id {chain_id} signed_tx_tmp.json"
        logging.info("Calling Cosmos SDK CLI: " + args)

        # call broadcast
        cmd = CosmosCmd(
            logfile,
            SIMD_BINARY,
            args.split(
                " "
            ),
            [mnemonic],
        )
        result = cmd.call()
        return result

# py


class Connector:
    """A generic connector that implements common methods"""

    def __init__(self, shell_out):
        self.shell_out = shell_out

    def shlog(self, text):
        if not text.startswith("#"):
            q = shlex.quote(text)
            print(f"echo {q}", file=self.shell_out)

        print(text, file=self.shell_out)


class SleepCmd(Connector):
    """A single command that delays by n seconds"""

    def __init__(self, shell_out, sleep_sec):
        super().__init__(shell_out)
        self.sleep_sec = sleep_sec

    def call(self):
        """Call a sleep command"""
        self.shlog("sleep {s}".format(s=self.sleep_sec))
        time.sleep(self.sleep_sec)
        return True


class CosmosCmd(Connector):
    """A single command to be executed via CLI"""

    def __init__(self, shell_out, binary, args, input_lines, timeout_sec=60):
        super().__init__(shell_out)
        self.binary = binary
        self.args = args
        self.input_lines = input_lines
        self.timeout_sec = timeout_sec

    def call(self):
        cmd_args_s = [str(a) for a in self.args]
        args_s = self.binary + cmd_args_s
        shell_cmd = " ".join([shlex.quote(a) for a in args_s])
        self.shlog(shell_cmd)
        with subprocess.Popen(
            self.binary + cmd_args_s,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=sys.stderr,
            text=True,
        ) as proc:
            try:
                for line in self.input_lines:
                    proc.stdin.write(line)
                    proc.stdin.write("\n")
                    proc.stdin.flush()

                outs, errs = proc.communicate(timeout=self.timeout_sec)
                self.shlog(outs)
                # if code is 0, then the command was executed successfully
                self.shlog(f"# return code: {proc.returncode}")
                if proc.returncode > 0:
                    if errs != None:
                        for e in errs.split("\n"):
                            self.shlog("# " + e)
                        return False
                    else:
                        self.shlog(
                            "# Transaction command was not valid. Execution was aborted on CLI."
                        )
                        return False
                else:
                    for o in outs.split("\n"):
                        self.shlog("# " + o)
                    return outs
            except subprocess.TimeoutExpired:
                self.shlog("echo 'timeout' && exit 1")
                print("Timeout", file=sys.stderr)
                proc.kill()
                outs, errs = proc.communicate()
                return None
