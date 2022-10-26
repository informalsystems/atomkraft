import json
import os.path
import shutil
from datetime import datetime
from pathlib import Path
from typing import List, Optional, Union

import pytest
from atomkraft.chain.testnet import VALIDATOR_DIR
from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.utils.filesystem import clean_tricky_chars
from atomkraft.utils.helpers import natural_sort, remove_suffix
from atomkraft.utils.project import (
    ATOMKRAFT_INTERNAL_DIR,
    ATOMKRAFT_VAL_DIR_PREFIX,
    get_absolute_project_path,
    get_relative_project_path,
    project_root,
)
from caseconverter import snakecase

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


def copy_if_exists(srcs: Union[Path, List[Path]], dst_path: Path):
    if isinstance(srcs, Path):
        srcs = [srcs]
    dst_path.mkdir(parents=True, exist_ok=True)
    for src in srcs:
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
    test_name = clean_tricky_chars(f"test_{str(trace)}_{timestamp}")
    test_path = os.path.join(tests, f"{test_name}.py")
    with open(test_path, "w") as test_file:
        print(f"Writing {get_relative_project_path(test_path)} ...")
        reactor_module = remove_suffix(str(reactor).replace("/", "."), ".py")
        test_file.write(TEST_FILE_HEADING_STUB.format(json.dumps(reactor_module)))
        test_file.write(
            TEST_FILE_TEST_TRACE_STUB.format(
                json.dumps(str(trace)),
                json.dumps(
                    clean_tricky_chars(remove_suffix(str(trace), ".itf.json"))
                ).strip('"'),
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

    trace_paths = list(trace_dir.glob("**/*.itf.json"))
    trace_paths.sort(key=natural_sort)

    if reactor is None:
        reactor = get_relative_project_path(get_reactor())

    timestamp = datetime.now().isoformat(timespec="milliseconds")
    test_group = clean_tricky_chars(f"{trace_dir}_{timestamp}")

    root_test_dir = root / "tests" / test_group
    test_file_name = f"test_{test_group}.py"
    test_path = root_test_dir / test_file_name
    test_path.parent.mkdir(parents=True, exist_ok=True)

    with open(test_path, "w+") as test_file:
        print(f"Writing {get_relative_project_path(test_path)} ...")

        if trace_paths:
            reactor_module = remove_suffix(str(reactor).replace("/", "."), ".py")
            test_file.write(TEST_FILE_HEADING_STUB.format(json.dumps(reactor_module)))

        for trace_path in trace_paths:
            if all(not c.isdigit() for c in trace_path.name):
                continue
            trace_path = get_relative_project_path(trace_path)
            print(f"Adding test for {trace_path} ...")
            test_file.write(
                TEST_FILE_TEST_TRACE_STUB.format(
                    json.dumps(str(trace_path)),
                    json.dumps(
                        clean_tricky_chars(remove_suffix(str(trace_path), ".itf.json"))
                    ).strip('"'),
                    json.dumps(keypath),
                )
            )

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

    val_root_dir = root / ATOMKRAFT_INTERNAL_DIR / VALIDATOR_DIR

    if val_root_dir.exists():
        shutil.rmtree(val_root_dir)

    exit_code = pytest.main(pytest_args + [test_path])

    vals_dirs = list((val_root_dir).glob(f"{ATOMKRAFT_VAL_DIR_PREFIX}*"))
    vals_dirs.sort(key=lambda k: k.stat().st_mtime)

    for (trace_path, vals_dir) in zip(trace_paths, vals_dirs):
        copy_if_exists(
            [Path(trace_path), vals_dir],
            report_dir
            / snakecase(remove_suffix(str(trace_path), ".itf.json"), delimiters="./"),
        )

    if trace_paths:
        print(f"Test data is saved at {report_dir}")
    else:
        print("No trace is present.")

    return int(exit_code)
