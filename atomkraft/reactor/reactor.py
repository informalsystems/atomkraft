import ast
import json
from os import PathLike
from pathlib import Path
from typing import List

from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.utils.project import get_absolute_project_path
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


def get_reactor() -> Path:
    """
    returns the path to the current reactor from the internal config
    """
    with AtomkraftConfig() as config:
        try:
            return get_absolute_project_path(config[constants.REACTOR_CONFIG_KEY])
        except KeyError:
            raise RuntimeError(
                "Could not find default reactor; have you ran `atomkraft reactor`?"
            )


def generate_reactor(
    actions_list: List[str],
    variables_list: List[str],
    stub_file_path: Path,
    keypath: str = "action",
) -> Path:

    file_comment = _file_comment()
    imports_stub = _imports_stub()

    state_stub = _state_stub()
    actions_stub = "".join(
        [
            _action_stub(action_name=act, variables=variables_list)
            for act in actions_list
        ]
    )
    keypath_stub = _keypath_stub(keypath)
    with open(stub_file_path, "w") as f:
        f.write(file_comment)
        f.write(imports_stub)
        f.write(keypath_stub)
        f.write(state_stub)
        f.write(actions_stub)

    with AtomkraftConfig() as config:
        config[constants.REACTOR_CONFIG_KEY] = str(stub_file_path)

    return stub_file_path


def _file_comment():
    return '''"""
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
'''


def _keypath_stub(keypath: str):
    stub = f"""
{constants.KEYPATH_VAR} = {json.dumps(keypath)}
"""
    return stub


def _action_description_comment(action_name, variables):
    if len(variables) == 0:
        variables_sentence = ""
    elif len(variables) == 1:
        variables_sentence = f"It additionally has access to the model (trace) state variable `{variables[0]}`."
    elif len(variables) == 2:
        variables_sentence = f"It additionally has access to the model (trace) state variables `{variables[0]}` and `{variables[1]}`."
    else:
        vars_string = "".join([f"\n\t\t-`{v}`" for v in variables])
        variables_sentence = f"It additionally has access to the model (trace) state variables: {vars_string}."
    return f'''"""
    Implements the effects of the step `{action_name}`
    on blockchain `testnet` and state `state`.
    {variables_sentence}
    """
'''


def _action_stub(action_name: str, variables: List[str]):
    stub = f"""

@step({json.dumps(action_name)})
def {snakecase(action_name)}(testnet: Testnet, state: Dict, {", ".join(variables)}):
    {_action_description_comment(action_name, variables)}
    # TODO: replace the logging stub with the effects of the action `{action_name}`
    logging.info("Step: {action_name}")
"""
    return stub


def _state_stub():
    stub = '''

@pytest.fixture
def state():
    """
    Defines any additional logical state (beyond the state of the chain)
    that needs to be maintained throughout the execution. This state
    will be passed as an argument to @step functions.
    """

    # TODO: replace the empty stub object with a different state object
    # if necessary
    return {}
'''
    return stub


def _imports_stub():
    stub = """
import logging
from typing import Dict

import pytest
from atomkraft.chain import Testnet
from modelator.pytest.decorators import step
"""
    return stub
