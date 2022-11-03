from io import TextIOWrapper
import json
import shutil
from datetime import datetime
from pathlib import Path
from typing import Optional, Tuple

import pytest
from atomkraft.chain.testnet import VALIDATOR_DIR
from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.utils.filesystem import copy_if_exists, snakecase
from atomkraft.utils.helpers import natural_key, remove_suffix
from atomkraft.utils.project import (
    ATOMKRAFT_INTERNAL_DIR,
    ATOMKRAFT_VAL_DIR_PREFIX,
    get_absolute_project_path,
    get_relative_project_path,
    project_root,
)

from ..reactor.reactor import get_reactor

# a key for the last used trace path inside internal config
TRACE_CONFIG_KEY = "trace"

TEST_FILE_HEADING_STUB = """import logging

from modelator.pytest.decorators import itf

pytest_plugins = {0}
"""

TEST_FILE_TEST_TRACE_STUB = """

@itf({0}, keypath={2})
def test_{1}():
    logging.info("Successfully executed trace " + {0})
"""


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

    test_file_path, test_name = mk_trace_path(root, trace)
    with open(test_file_path, "w") as test_file:
        print(f"Writing {get_relative_project_path(test_file_path)} ...")
        write_header(test_file, reactor)
        write_test(test_file, trace, keypath)

    print(f"Executing {test_name} ...")
    pytest_args, report_dir = mk_pytest_args(root, test_name, verbose)
    exit_code = pytest.main(pytest_args + [test_file_path])

    report_files = [Path(trace), root / ATOMKRAFT_INTERNAL_DIR / VALIDATOR_DIR]
    copy_if_exists(report_files, report_dir)
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

    test_file_path, test_name = mk_trace_path(root, trace_dir)
    with open(test_file_path, "w") as test_file:
        print(f"Writing tests to {get_relative_project_path(test_file_path)} ...")
        write_header(test_file, reactor)
        for trace_path in trace_paths:
            write_test(test_file, trace_path, keypath)
            print(f"Added test for {trace_path}")

    val_root_dir = root / ATOMKRAFT_INTERNAL_DIR / VALIDATOR_DIR
    if val_root_dir.exists():
        shutil.rmtree(val_root_dir)

    print(f"Executing {test_name}...")
    pytest_args, report_dir = mk_pytest_args(root, test_name, verbose)
    exit_code = pytest.main(pytest_args + [test_file_path])

    vals_dirs = list((val_root_dir).glob(f"{ATOMKRAFT_VAL_DIR_PREFIX}*"))
    vals_dirs.sort(key=lambda k: k.stat().st_mtime)

    for (trace_path, vals_dir) in zip(trace_paths, vals_dirs):
        report_files = [Path(trace_path), vals_dir]
        report_subdir = snakecase(remove_suffix(str(trace_path), ".itf.json"))
        copy_if_exists(report_files, report_dir / report_subdir)
    print(f"Test data is saved at {report_dir}")

    return int(exit_code)


def mk_trace_path(root: Path, trace: Path):
    timestamp = datetime.now().isoformat(timespec="milliseconds")
    test_name = snakecase(f"{trace}_{timestamp}")

    if trace.is_dir:
        test_dir = root / "tests" / test_name
    else:
        test_dir = root / "tests"
    test_dir.mkdir(parents=True, exist_ok=True)
    test_path = test_dir / f"test_{test_name}.py"

    return test_path, test_name


def write_header(test_file: TextIOWrapper, reactor: Path):
    reactor_module = remove_suffix(str(reactor).replace("/", "."), ".py")
    test_file.write(TEST_FILE_HEADING_STUB.format(json.dumps(reactor_module)))


def write_test(test_file: TextIOWrapper, trace_path: Path, keypath: str):
    if all(not c.isdigit() for c in trace_path.name):
        return
    trace_path = get_relative_project_path(trace_path)
    test_file.write(
        TEST_FILE_TEST_TRACE_STUB.format(
            json.dumps(str(trace_path)),
            snakecase(remove_suffix(str(trace_path), ".itf.json")),
            json.dumps(keypath),
        )
    )


def mk_pytest_args(root: Path, test_name: str, verbose: bool) -> Tuple[list[str], str]:
    report_dir = root / "reports" / test_name
    report_dir.mkdir(parents=True, exist_ok=True)

    logging_file = report_dir / "log.txt"
    pytest_report_file = report_dir / "report.jsonl"
    pytest_args = [
        "--log-file-level=INFO",
        "--log-cli-level=INFO",
        f"--log-file={logging_file}",
        f"--report-log={pytest_report_file}",
    ]

    if verbose:
        pytest_args.append("-rP")

    return pytest_args, report_dir
