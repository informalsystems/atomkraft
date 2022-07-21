import ast
from os import PathLike
import os
from typing import List
import tomlkit
from . import constants
from . import utils
from .step_functions_visitor import StepFunctionsVisitor
from atomkraft.utils.project import project_root


def check_reactor(trace: PathLike, keypath="action", reactor=None) -> bool:
    """
    returns true if each action appearing in `trace` is matched with a function in `reactor`
    """
    if reactor is None:
        reactor = get_reactor()

    with open(reactor) as f_reactor:
        root_node = ast.parse(f_reactor.read())
    v = StepFunctionsVisitor()
    v.visit(root_node)
    all_trace_actions = utils.get_all_trace_actions(trace, keypath)

    if constants.ALL_ENCOMPASSING_STEP in v.step_functions:
        return True
    else:
        return all_trace_actions.issubset(v.step_functions)


def get_reactor() -> PathLike:
    """
    returns the path to the current reactor from the internal config
    """
    internal_config_file_path = os.path.join(
        project_root(),
        constants.ATOMKRAFT_INTERNAL_FOLDER,
        constants.ATOMKRAFT_INTERNAL_CONFIG,
    )
    with open(internal_config_file_path) as config_f:
        config_data = tomlkit.load(config_f)
        return config_data[constants.REACTOR_CONFIG_KEY]


def generate_reactor(
    actions_list: List[str], variables_list: List[str], stub_file_path: PathLike = None
) -> PathLike:

    with open(stub_file_path, "w") as f:
        f.write("hi")

    imports_stub = _imports_stub()

    state_stub = _state_stub()
    actions_stub = "\n".join(
        [
            _action_stub(action_name=act, variables=variables_list)
            for act in actions_list
        ]
    )
    with open(stub_file_path, "w") as f:
        f.write(imports_stub)
        f.write(state_stub)
        f.write(actions_stub)

    internal_config_file_path = os.path.join(
        project_root(),
        constants.ATOMKRAFT_INTERNAL_FOLDER,
        constants.ATOMKRAFT_INTERNAL_CONFIG,
    )

    atomkraft_internal_config = tomlkit.load(internal_config_file_path)
    atomkraft_internal_config[constants.REACTOR_CONFIG_KEY] = stub_file_path

    with open(internal_config_file_path, "wb") as internal_config_f:
        tomlkit.dump(atomkraft_internal_config, internal_config_f)

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
