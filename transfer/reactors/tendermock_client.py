from typing import List, Optional, Union
from atomkraft.chain.node import AccountId
from atomkraft.chain.testnet import Testnet
import connector
import json
from terra_sdk.core.msg import Msg
import terra_proto.cosmos.tx.v1beta1 as tptx


DOCKER_PATH = "docker exec -i simapp".split(" ")
SIMD_BINARY = DOCKER_PATH + ["simd"]

TENDERMOCK_HOST = "host.docker.internal"
TENDERMOCK_PORT = "26657"


def sign_tx(
        testnet: Testnet,
        account_id: AccountId,
        msgs: Union[Msg, List[Msg]],
        gas: int = 200_000,
        fee_amount: int = 0,
        validator_id: Optional[AccountId] = None,):

    if not isinstance(msgs, list):
        msgs = [msgs]

    account = testnet.accounts[account_id]
    account_addr = account.address

    logfile = open("tendermint_client.log", "w+")

    cmd = connector.CosmosCmd(
        logfile,
        SIMD_BINARY,
        f"query account {account_addr} --node=http://{TENDERMOCK_HOST}:{TENDERMOCK_PORT} --chain-id=tendermock --output=json".split(
            " "
        ),
        [],
    )
    result = json.loads(cmd.call())

    account_number = result["account_number"]
    sequence = result["sequence"]

    tx = tptx.TxBody(messages=msgs)


    cmd = connector.CosmosCmd(
        logfile,
        DOCKER_PATH,
        ["tee", "tx_tmp.json"],
        [tx],
    )
    cmd.call()

    mnemonic = account.mnemonic

    cmd = connector.CosmosCmd(
        logfile,
        SIMD_BINARY,
        f"tx sign tx_tmp.json --chain-id=tendermock --from={account_addr} --offline --account-number {account_number} --sequence {sequence}".split(
            " "
        ),
        [mnemonic],
    )

    signed_tx = cmd.call()

    cmd = connector.CosmosCmd(
        logfile,
        DOCKER_PATH,
        ["tee", "signed_tx_tmp.json"],
        [signed_tx],
    )
    cmd.call()
