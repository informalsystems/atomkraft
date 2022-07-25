import time
import pytest
from cosmos_net.pytest import Testnet
from modelator.pytest.decorators import step


keypath = "action"


@pytest.fixture
def state():
    return {}


@step("store_cw_contract")
def act_step(testnet, state, count, last_msg):
    print("Step: store_cw_contract")


@step("instantiate")
def act_step(testnet, state, count, last_msg):
    print("Step: instantiate")


@step("reset")
def act_step(testnet, state, count, last_msg):
    print("Step: reset")


@step("increment")
def act_step(testnet, state, count, last_msg):
    print("Step: increment")


@step("get_count")
def act_step(testnet, state, count, last_msg):
    print("Step: get_count")
