"""
The reactor file connects a test scenario described by a trace
(obtained from a model or written by hand) with the actual execution
of the test scenario on the testnet.

It contains one @step decorated function per each action appearing in the trace:
those function implement changes to the blockchain corresponding to the
abstract action from the trace.

All step functions receive the following arguments:
    testnet: a `Testnet` object on which blockchain transactions can be
             executed.
    state: additional logical state, as defined the the `state()`
           function in this file.
    action: object from the trace which corresponds to the parameters
            of the taken step.
"""

import logging
from typing import Dict
import pytest
from atomkraft.chain import Testnet
from modelator.pytest.decorators import step
import asyncio
import base64
import contextlib
import json
import time
from atomkraft.chain import Testnet
from modelator.pytest.decorators import step
from terra_proto.cosmwasm.wasm.v1 import QueryStub
from terra_sdk.core import Coin, Coins
from terra_sdk.core.wasm import MsgExecuteContract, MsgInstantiateContract, MsgStoreCode
from terra_sdk.core.wasm.data import AccessConfig, AccessType

keypath = "last_msg.name"


@pytest.fixture
def state():
    """
    Defines any additional logical state (beyond the state of the chain)
    that needs to be maintained throughout the execution. This state
    will be passed as an argument to @step functions.
    """

    # TODO: replace the empty stub object with a different state object
    # if necessary
    result = {}
    result["update_admin_sender"] = None
    return result

@step("idle")
def idle(testnet: Testnet, state: Dict, last_msg, admins):
    sender = state["update_admin_sender"]
    if(not(sender is None)):
        state["update_admin_sender"] = None
        admin_addrs = [testnet.acc_addr(admin_id) for admin_id in admins]
        dict_msg = {"update_admins": {"admins":admin_addrs}}
        contract_address = state["contract_address"]
        msg = MsgExecuteContract(
            sender=testnet.acc_addr(sender),
            contract=contract_address,
            msg=dict_msg,
            coins=Coins([Coin(testnet.denom, 20000)]),
        )

        result = testnet.broadcast_transaction(
            sender, msg, gas=20000000, fee_amount=2000000
        )

        if result.code == 0:
            logging.info("Status: Successful\n")
        else:
            logging.info("Status: Error")
            logging.info("\tcode: %s", result.code)
            logging.info("\tlog:  %s\n", result.raw_log)
            assert("Unauthorized" in result.raw_log)


@step("store_cw_contract")
def store_contract(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: store_cw_contract")
    testnet.oneshot()
    time.sleep(10)

    wasm_binary = "contract/cw1_whitelist.wasm"

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
    state["sender"] = last_msg.sender
    state["update_admin_sender"] = None
    time.sleep(0.5)


@step("instantiate")
def instantiate(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: instantiate")
    admin_addrs = [testnet.acc_addr(admin_id) for admin_id in last_msg.admins]
    dict_msg = {"admins": admin_addrs , "mutable": last_msg.mutable}
    sender = state["sender"]
    msg = MsgInstantiateContract(
        sender=testnet.acc_addr(sender),
        admin=testnet.acc_addr(sender),
        code_id=state["code_id"],
        label="counter 1",
        msg=dict_msg,
    )

    result = testnet.broadcast_transaction(
        sender, msg, gas=20000000, fee_amount=2000000
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
    state["admin_list"] = admin_addrs


@step("execute")
def execute(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: execute")
    dict_msg = {"execute": {"msgs": []}}
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
        assert("Unauthorized" in result.raw_log)


@step("freeze")
def freeze(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: freeze")
    dict_msg = {"freeze": {}}
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
        assert("Unauthorized" in result.raw_log)



@step("update_admins")
def update_admins(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: update_admins")
    state["update_admin_sender"] = last_msg.sender



@step("get_admin_list")
def get_admin_list(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: get_admin_list")
    dict_msg = {"admin_list": {}}
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
    assert(not (data["mutable"] is None))
    admins1 = data["admins"]
    admins1.sort()
    admins2 = state["admin_list"]
    admins2.sort()
    assert(len(admins1)==len(admins2))
    for i in range(len(admins1)):
        assert(admins1[i]==admins2[i])



@step("get_can_execute")
def get_can_execute(testnet: Testnet, state: Dict, last_msg):
    logging.info("Step: get_can_execute")
    sender = testnet.acc_addr(last_msg.sender)
    dict_msg = {"can_execute": {"msg":{"custom":{}}, "sender":sender}}
    logging.info(f"msg: {json.dumps(dict_msg)}")
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
    admins = state["admin_list"]
    if(data["can_execute"]):
        assert(sender in admins)
    else:
        assert(not(sender in admins))