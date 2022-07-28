import ast
import os
import os.path
from os import PathLike
from typing import List, Optional

import tomlkit
from atomkraft.utils.project import project_root
from caseconverter import snakecase

from . import constants, utils
from .step_functions_visitor import StepFunctionsVisitor


def check_reactor(trace: PathLike, reactor=None) -> bool:
    """
    returns true if each action appearing in `trace` is matched with a function in `reactor`
    """
    if reactor is None:
        reactor = get_reactor()

    with open(reactor) as f_reactor:
        root_node = ast.parse(f_reactor.read())
    v = StepFunctionsVisitor()
    v.visit(root_node)

    keypath = utils.get_keypath(root_node)
    try:
        all_trace_actions = utils.get_all_trace_actions(trace, keypath)
    except Exception:
        raise ValueError(
            f"Keypath {keypath}, which is set in {reactor} is not present in the trace {trace}"
        )

    if constants.ALL_ENCOMPASSING_STEP in v.step_functions:
        return True
    else:
        return all_trace_actions.issubset(v.step_functions)


def get_reactor() -> PathLike:
    """
    returns the path to the current reactor from the internal config
    """

    root = project_root()

    if not root:
        raise RuntimeError(
            "could not find Atomkraft project: are you in the right directory?"
        )

    internal_config_file_path = os.path.join(
        root,
        constants.ATOMKRAFT_INTERNAL_FOLDER,
        constants.ATOMKRAFT_INTERNAL_CONFIG,
    )

    if not os.path.isfile(internal_config_file_path):
        raise RuntimeError(
            "Atomkraft configuration not found: have you executed `atomkraft init`?"
        )

    with open(internal_config_file_path) as config_f:
        config_data = tomlkit.load(config_f)
        if constants.REACTOR_CONFIG_KEY not in config_data:
            raise RuntimeError(
                "Could not find default reactor; have you ran `atomkraft reactor`?"
            )
        return config_data[constants.REACTOR_CONFIG_KEY]


def generate_reactor(
    actions_list: List[str],
    variables_list: List[str],
    keypath: str = "action",
    stub_file_path: Optional[PathLike] = None,
) -> PathLike:

    imports_stub = _imports_stub()

    state_stub = _state_stub()
    actions_stub = "\n".join(
        [
            _action_stub(action_name=act, variables=variables_list)
            for act in actions_list
        ]
    )
    keypath_stub = _keypath_stub(keypath)
    with open(stub_file_path, "w") as f:
        f.write(imports_stub)
        f.write(keypath_stub)
        f.write(state_stub)
        f.write(actions_stub)

    if "PYTEST_CURRENT_TEST" in os.environ:
        root = "tests/project"
    else:
        root = project_root()

    internal_config_file_path = os.path.join(
        root,
        constants.ATOMKRAFT_INTERNAL_FOLDER,
        constants.ATOMKRAFT_INTERNAL_CONFIG,
    )

    atomkraft_internal_config = tomlkit.load(open(internal_config_file_path))
    atomkraft_internal_config[constants.REACTOR_CONFIG_KEY] = stub_file_path

    with open(internal_config_file_path, "w") as internal_config_f:
        tomlkit.dump(atomkraft_internal_config, internal_config_f)

    return stub_file_path


def _keypath_stub(keypath):
    stub = f"""

{constants.KEYPATH_VAR} = {repr(keypath)}
"""
    return stub


def _action_stub(action_name: str, variables: List[str]):
    stub = f"""


@step({repr(action_name)})
def {snakecase(action_name)}(testnet, state, {", ".join(variables)}):
    print("Step: {action_name}")
"""
    return stub


def _state_stub():
    stub = """


@pytest.fixture
def state():
    return {}
"""
    return stub


def _imports_stub():
    stub = """
import pytest
from modelator.pytest.decorators import step
"""
    return stub
