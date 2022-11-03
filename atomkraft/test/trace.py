from pathlib import Path
from typing import Optional

import pytest
from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.test.helpers import (
    mk_pytest_args,
    mk_test_dir,
    mk_test_name,
    prepare_validators,
    save_validator_files,
    write_header,
    write_test,
)
from atomkraft.utils.filesystem import copy_if_exists
from atomkraft.utils.helpers import natural_key
from atomkraft.utils.project import (
    get_absolute_project_path,
    get_relative_project_path,
    project_root,
)

from ..reactor.reactor import get_reactor

# a key for the last used trace path inside internal config
TRACE_CONFIG_KEY = "trace"


def get_trace() -> Path:
    """
    returns the path to the current trace from the internal config
    """
    with AtomkraftConfig() as config:
        try:
            return get_absolute_project_path(config[TRACE_CONFIG_KEY])
        except KeyError:
            raise RuntimeError("Could not find any last used trace.")


def test_trace(
    trace: Optional[Path], reactor: Optional[Path], keypath: str, verbose: bool
):
    """
    Test blockchain by running one trace
    """

    root = project_root()
    if not root:
        raise RuntimeError(
            "could not find Atomkraft project: are you in the right directory?"
        )

    if trace is None:
        trace = get_trace()

    if reactor is None:
        reactor = get_relative_project_path(get_reactor())

    test_name = mk_test_name(trace)
    test_dir = mk_test_dir(root, trace.is_dir(), test_name)
    test_file_path = test_dir / f"test_{test_name}.py"
    with open(test_file_path, "w") as test_file:
        print(f"Writing {get_relative_project_path(test_file_path)} ...")
        write_header(test_file, reactor)
        write_test(test_file, trace, keypath)

    print(f"Executing {test_name} ...")
    val_root_dir = prepare_validators(root)
    pytest_args, report_dir = mk_pytest_args(test_dir, verbose)
    exit_code = pytest.main(pytest_args + [test_file_path])

    copy_if_exists([trace, val_root_dir], report_dir)
    print(f"Test data is saved at {report_dir}")

    return int(exit_code)


def test_trace_dir(
    trace_dir: Path, reactor: Optional[Path], keypath: str, verbose: bool
):
    """
    Test blockchain by running all available traces in trace_dir.
    """

    root = project_root()
    if not root:
        raise RuntimeError(
            "could not find Atomkraft project: are you in the right directory?"
        )

    if reactor is None:
        reactor = get_relative_project_path(get_reactor())

    trace_paths = list(trace_dir.glob("**/*.itf.json"))
    trace_paths.sort(key=natural_key)
    if not trace_paths:
        print("No trace is present.")
        return 1

    test_name = mk_test_name(trace_dir)
    test_dir = mk_test_dir(root, trace_dir.is_dir(), test_name)
    test_file_path = test_dir / f"test_{test_name}.py"
    with open(test_file_path, "w") as test_file:
        print(f"Writing tests to {get_relative_project_path(test_file_path)}...")
        write_header(test_file, reactor)
        for trace_path in trace_paths:
            write_test(test_file, trace_path, keypath)
            print(f"Added test for {trace_path}")

    print(f"Executing {test_name}...")
    val_root_dir = prepare_validators(root)
    pytest_args, report_dir = mk_pytest_args(test_dir, verbose)
    exit_code = pytest.main(pytest_args + [test_file_path])

    save_validator_files(val_root_dir, report_dir, trace_paths)
    print(f"Test data is saved at {report_dir}")

    return int(exit_code)
