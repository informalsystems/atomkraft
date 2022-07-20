from asyncio import constants
from os import PathLike
import os
from typing import List
import tomli
from . import constants


def generate_reactor(
    actions_list: List[str], variables_list: List[str], stub_file_path: PathLike = None
) -> PathLike:

    with open(stub_file_path, "w") as f:
        f.write("hi")

    # TODO: what is the best way to hanlde potential exceptions here?
    chain_config = tomli.load(open(constants.CHAIN_CONFIG, "rb"))
    atomkraft_config = tomli.load(open(constants.ATOMKRAFT_CONFIG, "rb"))
    print(chain_config)

    imports_stub = _imports_stub()

    init_stub = _testnet_init_stub(
        chain_config=chain_config, atomkraft_config=atomkraft_config
    )
    state_stub = _state_stub()
    actions_stub = "\n".join(
        [
            _action_stub(action_name=act, variables=variables_list)
            for act in actions_list
        ]
    )
    with open(stub_file_path, "w") as f:
        f.write(imports_stub)
        f.write(init_stub)
        f.write(state_stub)
        f.write(actions_stub)

    return stub_file_path


def _action_stub(action_name: str, variables: List[str]):
    stub = f"""
@step({repr(action_name)})
def act_step(chain_testnet, state, {", ".join(variables)}):
    print("Step: {action_name}")
"""
    return stub


def _state_stub():
    stub = f"""

@pytest.fixture
def state():
    return {{}}

"""
    return stub


def _imports_stub():
    stub = """
import time
import pytest
from cosmos_net.pytest import Testnet
from modelator.pytest.decorators import step

    """
    return stub


def _testnet_init_stub(
    chain_config,
    atomkraft_config,
    default_num_validators=3,
    default_num_accounts=3,
    default_account_balance=1000,
    default_validator_balance=1000,
):
    stub = f"""
@pytest.fixture(scope="session")
def chain_testnet(num_validators={default_num_validators}, num_accounts={default_num_accounts}, account_balance={default_account_balance}, validator_balance={default_validator_balance}):
    chain_id = {repr(chain_config['name'])}
    binary = {repr(atomkraft_config['chain']['binary'])}
    denom = {repr(chain_config['denom'])}
    prefix = {repr(chain_config['prefix'])}
    coin_type = {chain_config['coin']}

    genesis_config = {chain_config["genesis"]}

    node_config = {{}}
    node_config["config/app.toml"] = {chain_config["app"]}
    node_config["config/config.toml"] = {chain_config["config"]}


    testnet = Testnet(
        chain_id,
        n_validator=num_validators,
        n_account=num_accounts,
        binary=binary,
        denom=denom,
        prefix=prefix,
        coin_type=coin_type,
        genesis_config=genesis_config,
        node_config=node_config,
        account_balance=account_balance,
        validator_balance=validator_balance,
    )

    testnet.oneshot()
    time.sleep(10)
    yield testnet
    time.sleep(2)

    """

    return stub
