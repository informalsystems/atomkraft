import asyncio
import base64
import contextlib
import json
import logging
import time
from typing import Dict

import pytest
from atomkraft.chain import Testnet
from modelator.pytest.decorators import step
from terra_proto.cosmwasm.wasm.v1 import QueryStub
from terra_sdk.core import Coin, Coins
from terra_sdk.core.wasm import MsgExecuteContract, MsgInstantiateContract, MsgStoreCode
from terra_sdk.core.wasm.data import AccessConfig, AccessType


@pytest.fixture
def state():
    return {}


@step("store_cw_contract")
def store_contract(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: store_cw_contract")
    testnet.oneshot()
    time.sleep(10)

    wasm_binary = "cosmwasm-contract/target/wasm32-unknown-unknown/release/counter.wasm"

    with open(wasm_binary, "rb") as f:
        counter_cw_code = base64.b64encode(f.read()).decode("ascii")

    msg = MsgStoreCode(
        sender=testnet.acc_addr(last_msg.sender),
        wasm_byte_code=counter_cw_code,
        instantiate_permission=AccessConfig(AccessType.ACCESS_TYPE_EVERYBODY, None),
    )

    result = testnet.broadcast_transaction(
        last_msg.sender, msg, gas=20000000, fee_amount=2000000
    )

    logging.info(str("Contract is uploaded"))
    logging.info(str(result))

    for event in result.logs[0].events:
        if event.type == "store_code":
            assert event.attributes[0].key == "code_id"
            code_id = event.attributes[0].value
            break
    else:
        raise RuntimeError("Did not find code_id of the uploaded contract")

    state["code_id"] = code_id

    time.sleep(0.5)


@step("instantiate")
def instantiate(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: instantiate")
    dict_msg = {"count": last_msg["cnt"]}

    msg = MsgInstantiateContract(
        sender=testnet.acc_addr(last_msg.sender),
        admin=testnet.acc_addr(last_msg.sender),
        code_id=state["code_id"],
        label="counter 1",
        msg=dict_msg,
    )

    result = testnet.broadcast_transaction(
        last_msg.sender, msg, gas=20000000, fee_amount=2000000
    )

    logging.info(str(msg))
    logging.info(str(result))

    for event in result.logs[0].events:
        if event.type == "instantiate":
            assert event.attributes[0].key == "_contract_address"
            contract_address = event.attributes[0].value
            break
    else:
        raise RuntimeError("Did not find contract_address of the uploaded code")

    state["contract_address"] = contract_address

    time.sleep(0.5)


@step("reset")
def reset(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: reset")
    dict_msg = {"reset": {"count": last_msg["cnt"]}}
    contract_address = state["contract_address"]

    msg = MsgExecuteContract(
        sender=testnet.acc_addr(last_msg.sender),
        contract=contract_address,
        msg=dict_msg,
        coins=Coins([Coin(testnet.denom, 20000)]),
    )

    result = testnet.broadcast_transaction(
        last_msg.sender, msg, gas=20000000, fee_amount=2000000
    )

    logging.info(str(msg))
    logging.info(str(result))

    time.sleep(0.5)


@step("increment")
def increment(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: increment")
    dict_msg = {"increment": {}}
    contract_address = state["contract_address"]

    msg = MsgExecuteContract(
        sender=testnet.acc_addr(last_msg.sender),
        contract=contract_address,
        msg=dict_msg,
        coins=Coins([Coin(testnet.denom, 20000)]),
    )

    result = testnet.broadcast_transaction(
        last_msg.sender, msg, gas=20000000, fee_amount=2000000
    )

    logging.info(str(msg))
    logging.info(str(result))

    time.sleep(0.5)


@step("get_count")
def get_count(testnet: Testnet, state: Dict, count):
    logging.info("Step: get_count")

    dict_msg = {"get_count": {}}
    contract_address = state["contract_address"]

    with contextlib.closing(testnet.get_grpc_channel()) as channel:
        stub = QueryStub(channel)
        result = asyncio.run(
            stub.smart_contract_state(
                address=contract_address, query_data=json.dumps(dict_msg).encode()
            )
        )

    logging.info(str(result))

    data = json.loads(result.data.decode())

    assert data["count"] == count

    time.sleep(0.5)
