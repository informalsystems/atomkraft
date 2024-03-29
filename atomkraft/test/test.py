import json
import os
import shutil
from datetime import datetime
from io import TextIOWrapper
from pathlib import Path
from typing import List

import pytest
from atomkraft.chain.testnet import VALIDATOR_DIR
from atomkraft.utils.filesystem import copy_if_exists, snakecase
from atomkraft.utils.helpers import natural_key, remove_prefix, remove_suffix
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


class Test:
    def __init__(
        self,
        root: Path,
        trace: Path,
    ):
        """
        Initialize a test for a given trace, which can be a directory or a file.
        """
        self.root = root
        self.trace = trace
        self.timestamp = snakecase(datetime.now().isoformat(timespec="milliseconds"))

        if trace.is_dir():
            self.name = Test._path_to_id(trace)
            self.tests_dir = root / "tests" / f"{self.name}_{self.timestamp}"
        else:
            self.name = Test._path_to_id(trace) + "_" + self.timestamp
            self.tests_dir = root / "tests"
        self.tests_dir.mkdir(parents=True, exist_ok=True)
        self.file_path = self.tests_dir / f"test_{self.name}.py"

        self.report_dir = root / "reports" / Test._path_to_id(trace) / self.timestamp
        self.report_dir.mkdir(parents=True, exist_ok=True)

    def create_file(self, traces: List[Path], reactor: Path, keypath: str):
        """
        Create a pytest file containing tests for the given traces.
        """
        self.trace_paths = traces
        self.write_file(reactor, keypath)

    def execute(self, verbose: bool):
        """
        Execute an existing test file.
        """
        if not self.file_path.exists():
            raise ValueError("No test file exists.")

        print(f"Executing test {self.name} ...")
        val_root_dir = self.prepare_validators()
        pytest_args = self.make_pytest_args(verbose)
        exit_code = pytest.main(pytest_args + [self.file_path])

        self.save_validator_files(val_root_dir)
        print(f"Test data for {self.name} saved at {self.report_dir}")

        return int(exit_code)

    @staticmethod
    def _path_to_id(path: Path) -> str:
        """
        Make a test string identifier from a path.
        """
        path = str(get_relative_project_path(path))
        path = remove_prefix(path, "test/")
        path = remove_prefix(path, "traces/")
        path = remove_suffix(path, ".itf.json")
        return snakecase(path)

    @staticmethod
    def _append_timestamp(name: str):
        timestamp = snakecase(datetime.now().isoformat(timespec="milliseconds"))
        return f"{name}_{timestamp}"

    def write_file(self, reactor: Path, keypath: str):
        with open(self.file_path, "w") as test_file:
            print(f"Writing tests to {get_relative_project_path(self.file_path)} ...")
            Test._write_header(test_file, reactor)
            for trace_path in self.trace_paths:
                print(f"Writing test for {trace_path}")
                Test._write_test(test_file, trace_path, keypath)

    @staticmethod
    def _write_header(test_file: TextIOWrapper, reactor: Path):
        reactor_module = remove_suffix(str(reactor).replace("/", "."), ".py")
        test_file.write(TEST_FILE_HEADING_STUB.format(json.dumps(reactor_module)))

    @staticmethod
    def _write_test(test_file: TextIOWrapper, trace_path: Path, keypath: str):
        if all(not c.isdigit() for c in trace_path.name):
            return
        trace_path = get_relative_project_path(trace_path)
        test_file.write(
            TEST_FILE_TEST_TRACE_STUB.format(
                json.dumps(str(trace_path)),
                Test._path_to_id(trace_path),
                json.dumps(keypath),
            )
        )

    def make_pytest_args(self, verbose: bool) -> List[str]:
        logging_file = self.report_dir / "log.txt"
        pytest_report_file = self.report_dir / "report.jsonl"
        pytest_args = [
            "--log-file-level=INFO",
            "--log-cli-level=INFO",
            f"--log-file={logging_file}",
            f"--report-log={pytest_report_file}",
        ]
        if verbose:
            pytest_args.append("-rP")

        return pytest_args

    def prepare_validators(self):
        val_root_dir = self.root / ATOMKRAFT_INTERNAL_DIR / VALIDATOR_DIR
        if val_root_dir.exists():
            shutil.rmtree(val_root_dir)
        return val_root_dir

    def save_validator_files(self, val_root_dir: Path):
        vals_dirs = list(val_root_dir.glob(f"{ATOMKRAFT_VAL_DIR_PREFIX}*"))
        vals_dirs.sort(key=lambda k: k.stat().st_mtime)

        # Be careful: zip assumes that trace_paths and the validator directories
        # are sorted in the same order. We should improve this code.
        for (trace_path, validator_dir) in zip(self.trace_paths, vals_dirs):
            subdir = Path(Test._path_to_id(Path(os.path.basename(trace_path))))
            copy_if_exists([trace_path, validator_dir], self.report_dir / subdir)


def all_traces_from(trace_dir: Path):
    trace_paths = list(trace_dir.glob("**/*.itf.json"))
    trace_paths.sort(key=natural_key)
    return trace_paths
