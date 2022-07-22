from modelator.pytest.decorators import dict_get_keypath
from typing import Set
from os import PathLike
import json


def get_all_trace_actions(trace: PathLike, keypath: str) -> Set[str]:
    all_actions = set()
    with open(trace) as f_trace:
        itf_dict = json.load(f_trace)

    states = itf_dict["states"]
    for state in states:
        action = dict_get_keypath(state, keypath)
        all_actions.add(action)

    return all_actions
