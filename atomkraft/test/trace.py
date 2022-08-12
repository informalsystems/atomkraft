import os.path
import shutil
from datetime import datetime
from os import PathLike

import pytest
from atomkraft.utils.project import project_root

from ..reactor.reactor import get_reactor

TRACE_TEST_STUB = """
from modelator.pytest.decorators import itf

pytest_plugins = "{0}"

@itf("{1}", keypath="{2}")
def test_trace():
    print("Successfully executed trace {1}")
"""


def test_trace(trace: PathLike, reactor: PathLike, keypath: str, verbose: bool):
    """
    Test blockchain by running one trace
    """

    if reactor is None:
        reactor = get_reactor()

    root = project_root()
    if not root:
        raise RuntimeError(
            "could not find Atomkraft project: are you in the right directory?"
        )

    tests = os.path.join(root, "tests")
    if not os.path.isdir(tests):
        raise RuntimeError(
            "Atomkraft tests directory not found: have you executed `atomkraft init`?"
        )

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
                str(reactor).replace("/", ".").removesuffix(".py"), trace, keypath
            )
        )
    print(f"Executing {test_name} ...")

    report_dir = root / "reports" / test_name
    report_dir.mkdir(parents=True)

    logging_file = report_dir / "log.txt"

    pytest_report_file = report_dir / "report.jsonl"

    pytest_args = [
        "--log-file-level=INFO",
        f"--log-file={logging_file}",
        f"--report-log={pytest_report_file}",
    ]

    if verbose:
        pytest_args.append("-rP")
        pytest_args.append("--log-cli-level=INFO")

    pytest.main(pytest_args + [test_path])

    default_nodes_dir = root / ".atomkraft" / "nodes"
    report_nodes_dir = report_dir / "nodes"

    shutil.copytree(default_nodes_dir, report_nodes_dir)

    print(f"Test data is saved at {report_dir}")
