from pathlib import Path
from typing import Dict, List, Optional

import pytest
from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.model.traces import generate_traces
from atomkraft.test.helpers import (
    append_timestamp,
    mk_test_dir,
    prepare_validators,
    save_validator_files,
)
from atomkraft.utils.helpers import remove_suffix
from atomkraft.utils.project import (
    get_absolute_project_path,
    get_relative_project_path,
    project_root,
)

from ..reactor.reactor import get_reactor
from .trace import mk_pytest_args, write_header, write_test

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
            "could not find Atomkraft project: are you in the right directory?"
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
        print("No trace is produced.")
        return 1

    test_name = append_timestamp(model.stem)
    test_dir = mk_test_dir(root, False, test_name)

    test_list = []
    for op in successful_ops:
        print(f"Preparing tests for {op} ...")
        for trace_path in model_result.trace_paths(op):
            trace = Path(trace_path)
            if all(not c.isdigit() for c in trace.name):
                continue

            trace_name = remove_suffix(trace.name, ".itf.json")
            print(f"Using {trace} ...")
            trace = get_relative_project_path(trace)
            test_path = test_dir / test_name / f"test_{op}_{trace_name}.py"
            test_path.parent.mkdir(parents=True, exist_ok=True)
            with open(test_path, "w") as test_file:
                print(f"Writing {test_path.name} ...")
                write_header(test_file, reactor)
                write_test(test_file, trace, keypath)
            test_list.append((trace, test_path))

    print(f"Executing {test_name}...")
    val_root_dir = prepare_validators(root)
    pytest_args, report_dir = mk_pytest_args(test_dir, verbose)
    test_file_paths = [str(test_file) for (_, test_file) in test_list]
    exit_code = pytest.main(pytest_args + test_file_paths)

    trace_paths = [path for path, _ in test_list]
    save_validator_files(val_root_dir, report_dir, trace_paths)
    print(f"Test data is saved at {report_dir}")

    return int(exit_code)
