import asyncio
import logging
import socket
import tempfile
import time
from contextlib import closing
from pathlib import Path
from subprocess import PIPE, Popen
from typing import Dict, List, Optional, Union

import numpy as np
import tabulate
import tomlkit
from atomkraft.chain import Testnet
from atomkraft.chain.node import Account, AccountId, ConfigPort, Node
from atomkraft.chain.utils import TmEventSubscribe, get_free_ports, update_port
from atomkraft.utils.project import ATOMKRAFT_INTERNAL_DIR, ATOMKRAFT_VAL_DIR_PREFIX
from grpclib.client import Channel
from modelator.pytest.decorators import step
from terra_proto.cosmos.auth.v1beta1 import BaseAccount
from terra_proto.cosmos.auth.v1beta1 import QueryStub as AuthQueryStub
from terra_proto.cosmos.base.abci.v1beta1 import TxResponse
from terra_proto.cosmos.tx.v1beta1 import BroadcastMode, ServiceStub
from terra_sdk.client.lcd import LCDClient
from terra_sdk.client.lcd.api.tx import CreateTxOptions
from terra_sdk.core import Coins
from terra_sdk.core.bank import MsgSend
from terra_sdk.core.fee import Fee
from terra_sdk.core.msg import Msg
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

    msg = MsgSend(sender_addr, receiver_addr, f"{amount}{testnet.denom}")

    logging.info(msg.to_json())

    result = testnet.broadcast_transaction(
        sender_id, msg, gas=200_000, fee_amount=0)

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
