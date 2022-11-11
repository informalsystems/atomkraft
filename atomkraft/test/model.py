import os
from pathlib import Path
from typing import Dict, List, Optional

from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.model.traces import generate_traces
from atomkraft.test.test import Test
from atomkraft.utils.project import (
    get_absolute_project_path,
    get_relative_project_path,
    project_root,
)

from ..reactor.reactor import get_reactor

# a key for the last used model path inside internal config
MODEL_CONFIG_KEY = "model"


def get_model() -> Path:
    """
    returns the path to the current model from the internal config
    """
    with AtomkraftConfig() as config:
        try:
            return get_absolute_project_path(config[MODEL_CONFIG_KEY])
        except KeyError:
            raise RuntimeError("Could not find any last used model.")


def test_model(
    model: Optional[Path],
    tests: List[str],
    reactor: Optional[Path],
    keypath: str,
    checker_params: Dict[str, str],
    verbose: bool,
) -> int:
    """
    Test blockchain by running one trace
    """

    root = project_root()
    if not root:
        raise RuntimeError(
            "Could not find Atomkraft project: are you in the right directory?"
        )

    if model is None:
        model = get_model()

    if reactor is None:
        reactor = get_relative_project_path(get_reactor())

    print(f"Generating traces for {model.name} ...")
    try:
        model_result = generate_traces(
            None, model, tests, checker_params=checker_params
        )
    except Exception as e:
        raise RuntimeError(f"[Modelator] {e}")

    successful_ops = model_result.successful()
    if not successful_ops:
        print("No trace generated.")
        return 1

    for op in successful_ops:
        print(f"Preparing tests for {op} ...")
        trace_paths = [Path(t) for t in model_result.trace_paths(op)]
        trace_dir = Path(os.path.dirname(os.path.commonprefix(trace_paths)))

        test = Test(root, trace_dir)
        test.create_file(trace_paths, reactor, keypath)
        exit_code = test.execute(verbose)
        if exit_code != 0:
            return exit_code

    return 0
