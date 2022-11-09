import json
import shutil
from datetime import datetime
from io import TextIOWrapper
from pathlib import Path
from typing import List, Tuple

from atomkraft.chain.testnet import VALIDATOR_DIR
from atomkraft.utils.filesystem import copy_if_exists, snakecase
from atomkraft.utils.helpers import remove_prefix, remove_suffix
from atomkraft.utils.project import (
    ATOMKRAFT_INTERNAL_DIR,
    ATOMKRAFT_VAL_DIR_PREFIX,
    get_relative_project_path,
)

TEST_FILE_HEADING_STUB = """import logging

from modelator.pytest.decorators import itf

pytest_plugins = {0}
"""

TEST_FILE_TEST_TRACE_STUB = """

@itf({0}, keypath={2})
def test_{1}():
    logging.info("Successfully executed trace " + {0})
"""


def path_to_id(path: Path):
    path = str(get_relative_project_path(path))
    path = remove_prefix(path, "test/")
    path = remove_prefix(path, "traces/")
    path = remove_suffix(path, ".itf.json")
    return snakecase(path)


def append_timestamp(name: str):
    timestamp = snakecase(datetime.now().isoformat(timespec="milliseconds"))
    return f"{name}_{timestamp}"


def mk_test_name(trace_path: Path):
    test_name = path_to_id(trace_path)

    if not trace_path.is_dir:
        test_name = append_timestamp(test_name)
    return test_name


def mk_test_dir(root: Path, trace_is_dir: bool, test_name: str):
    if trace_is_dir:
        test_dir = root / "tests" / append_timestamp(test_name)
    else:
        test_dir = root / "tests"
    test_dir.mkdir(parents=True, exist_ok=True)

    return test_dir


def write_header(test_file: TextIOWrapper, reactor: Path):
    reactor_module = remove_suffix(str(reactor).replace("/", "."), ".py")
    test_file.write(TEST_FILE_HEADING_STUB.format(json.dumps(reactor_module)))


def write_test(test_file: TextIOWrapper, trace_path: Path, keypath: str):
    if all(not c.isdigit() for c in trace_path.name):
        return
    trace_path = get_relative_project_path(trace_path)
    test_file.write(
        TEST_FILE_TEST_TRACE_STUB.format(
            json.dumps(str(trace_path)), path_to_id(trace_path), json.dumps(keypath)
        )
    )


def mk_pytest_args(test_dir: Path, verbose: bool) -> Tuple[List[str], str]:
    report_dir = Path(
        str(get_relative_project_path(test_dir)).replace("tests/", "reports/")
    )
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


def prepare_validators(root: Path):
    val_root_dir = root / ATOMKRAFT_INTERNAL_DIR / VALIDATOR_DIR
    if val_root_dir.exists():
        shutil.rmtree(val_root_dir)
    return val_root_dir


def save_validator_files(val_root_dir: Path, report_dir: Path, trace_paths: List[Path]):
    vals_dirs = list(val_root_dir.glob(f"{ATOMKRAFT_VAL_DIR_PREFIX}*"))
    vals_dirs.sort(key=lambda k: k.stat().st_mtime)

    for (trace_path, validator_dir) in zip(trace_paths, vals_dirs):
        report_files = [trace_path, validator_dir]
        report_subdir = path_to_id(trace_path)
        copy_if_exists(report_files, report_dir / report_subdir)
