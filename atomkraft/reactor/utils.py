from modelator.pytest.decorators import dict_get_keypath
from typing import Set
from os import PathLike
import json
import ast
from . import constants


def get_all_trace_actions(trace: PathLike, keypath: str) -> Set[str]:
    all_actions = set()
    with open(trace) as f_trace:
        itf_dict = json.load(f_trace)

    states = itf_dict["states"]
    for state in states:
        action = dict_get_keypath(state, keypath)
        all_actions.add(action)

    return all_actions


def get_keypath(root_node: ast.Module) -> str:
    for el in root_node.body:
        if (
            isinstance(el, ast.Assign)
            and len(el.targets) == 1
            and el.targets[0].id == constants.KEYPATH_VAR
        ):
            return el.value.value
    raise ValueError(
        f"Expression of the form {constants.KEYPATH_VAR} = <val> is missing from the reactor file."
    )
