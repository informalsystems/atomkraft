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


@step("StoreCwContract")
def store_contract(testnet: Testnet, state: Dict, last_msg):
    last_msg = last_msg.value
    logging.info("Step: StoreCwContract")
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

    if result.code == 0:
        logging.info("Status: Successful\n")
    else:
        logging.info("Status: Error")
        logging.info("\tcode: %s", result.code)
        logging.info("\tlog:  %s\n", result.raw_log)

    for event in result.logs[0].events:
        if event.type == "store_code":
            for e in event.attributes:
                if e.key == "code_id":
                    code_id = e.value
                    break
            else:
                continue
            break
    else:
        raise RuntimeError("Did not find code_id of the uploaded contract")

    state["code_id"] = code_id

    time.sleep(0.5)


@step("Instantiate")
def instantiate(testnet: Testnet, state: Dict, last_msg):
    last_msg = last_msg.value
    logging.info("Step: Instantiate")
    dict_msg = {"count": last_msg.count}

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

    if result.code == 0:
        logging.info("Status: Successful\n")
    else:
        logging.info("Status: Error")
        logging.info("\tcode: %s", result.code)
        logging.info("\tlog:  %s\n", result.raw_log)

    for event in result.logs[0].events:
        if event.type == "instantiate":
            assert event.attributes[0].key == "_contract_address"
            contract_address = event.attributes[0].value
            break
    else:
        raise RuntimeError("Did not find contract_address of the uploaded code")

    state["contract_address"] = contract_address


@step("Reset")
def reset(testnet: Testnet, state: Dict, last_msg):
    last_msg = last_msg.value
    logging.info("Step: Reset")
    dict_msg = {"reset": {"count": last_msg.count}}
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

    if result.code == 0:
        logging.info("Status: Successful\n")
    else:
        logging.info("Status: Error")
        logging.info("\tcode: %s", result.code)
        logging.info("\tlog:  %s\n", result.raw_log)


@step("Increment")
def increment(testnet: Testnet, state: Dict, last_msg):
    last_msg = last_msg.value
    logging.info("Step: Increment")
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

    if result.code == 0:
        logging.info("Status: Successful\n")
    else:
        logging.info("Status: Error")
        logging.info("\tcode: %s", result.code)
        logging.info("\tlog:  %s\n", result.raw_log)


@step("GetCount")
def get_count(testnet: Testnet, state: Dict, count):
    logging.info("Step: GetCount")

    dict_msg = {"get_count": {}}
    contract_address = state["contract_address"]

    with contextlib.closing(testnet.get_grpc_channel()) as channel:
        stub = QueryStub(channel)
        result = asyncio.run(
            stub.smart_contract_state(
                address=contract_address, query_data=json.dumps(dict_msg).encode()
            )
        )

    logging.info("Response: %s\n", json.loads(result.data.decode()))

    data = json.loads(result.data.decode())

    assert data["count"] == count
