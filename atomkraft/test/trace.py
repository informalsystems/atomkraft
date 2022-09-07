import json
import os.path
import shutil
from datetime import datetime
from pathlib import Path
from typing import List, Optional

import pytest
from atomkraft.chain.testnet import VALIDATOR_DIR
from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.config.model_config import ModelConfig
from atomkraft.utils.project import (
    ATOMKRAFT_INTERNAL_DIR,
    get_absolute_project_path,
    get_relative_project_path,
    project_root,
)

from ..reactor.reactor import get_reactor

# a key for the last used trace path inside internal config
TRACE_CONFIG_KEY = "trace"

TRACE_TEST_STUB = """import logging

from modelator.pytest.decorators import itf

pytest_plugins = {0}


@itf({1}, keypath={2})
def test_trace():
    logging.info("Successfully executed trace " + {1})
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


def copy_if_exists(src_paths: List[Path], dst_path: Path):
    for src in src_paths:
        if src.is_dir():
            shutil.copytree(src, dst_path / src.name)
        elif src.is_file():
            shutil.copy2(src, dst_path)
        else:
            # file does not exist
            pass


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

    tests = root / "tests"
    tests.mkdir(exist_ok=True)

    timestamp = datetime.now().isoformat(timespec="milliseconds")
    test_name = f"test_{str(trace)}_{timestamp}"
    test_name = (
        test_name.replace("/", "_")
        .replace(".", "_")
        .replace(":", "_")
        .replace("-", "_")
    )
    test_path = os.path.join(tests, f"{test_name}.py")
    with open(test_path, "w") as test:
        print(f"Writing {test_name} ...")
        test.write(
            TRACE_TEST_STUB.format(
                json.dumps(str(reactor).replace("/", ".").removesuffix(".py")),
                json.dumps(str(trace)),
                json.dumps(keypath),
            )
        )
    print(f"Executing {test_name} ...")

    report_dir = root / "reports" / test_name
    report_dir.mkdir(parents=True)

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

    exit_code = pytest.main(pytest_args + [test_path])

    copy_if_exists(
        [Path(trace), root / ATOMKRAFT_INTERNAL_DIR / VALIDATOR_DIR], report_dir
    )

    print(f"Test data is saved at {report_dir}")

    return int(exit_code)


def test_all_trace(reactor: Optional[Path], keypath: str, verbose: bool):
    """
    Test blockchain by running all available traces
    """

    root = project_root()
    if not root:
        raise RuntimeError(
            "could not find Atomkraft project: are you in the right directory?"
        )

    with ModelConfig() as config:
        traces_dir = get_absolute_project_path(config["traces_dir"])
        traces = list(traces_dir.glob("**/*.itf.json"))

    if reactor is None:
        reactor = get_relative_project_path(get_reactor())

    timestamp = datetime.now().isoformat(timespec="milliseconds")

    test_group = (
        f"all_{timestamp}".replace("/", "_")
        .replace(".", "_")
        .replace(":", "_")
        .replace("-", "_")
    )

    root_test_dir = root / "tests" / test_group

    test_list = []

    for trace in traces:
        if all(not c.isdigit() for c in trace.name):
            continue
        trace = get_relative_project_path(trace)
        trace_name = (
            str(trace)
            .replace("/", "_")
            .replace(".", "_")
            .replace(":", "_")
            .replace("-", "_")
        )
        test_file_name = f"test_{trace_name}.py"
        test_path = root_test_dir / test_file_name
        test_path.parent.mkdir(parents=True, exist_ok=True)
        with open(test_path, "w") as test:
            print(f"Writing {test_file_name} ...")
            test.write(
                TRACE_TEST_STUB.format(
                    json.dumps(str(reactor).replace("/", ".").removesuffix(".py")),
                    json.dumps(str(trace)),
                    json.dumps(keypath),
                )
            )
        test_list.append((trace, test_path))

    report_dir = root / "reports" / test_group
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

    exit_code = pytest.main(
        pytest_args + [str(test_file) for (_, test_file) in test_list]
    )

    for (trace, _) in test_list:
        copy_if_exists(
            [Path(trace), root / ATOMKRAFT_INTERNAL_DIR / VALIDATOR_DIR], report_dir
        )

    if traces:
        print(f"Test data is saved at {report_dir}")
    else:
        print("No trace is present.")

    return int(exit_code)
