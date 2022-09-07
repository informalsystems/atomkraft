import json
import shutil
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional

import pytest
from atomkraft.chain.testnet import VALIDATOR_DIR
from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.model.traces import generate_traces
from atomkraft.utils.project import (
    ATOMKRAFT_INTERNAL_DIR,
    get_absolute_project_path,
    get_relative_project_path,
    project_root,
)

from ..reactor.reactor import get_reactor
from .trace import TRACE_TEST_STUB

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


def copy_if_exists(src_paths: List[Path], dst_path: Path):
    for src in src_paths:
        if src.is_dir():
            shutil.copytree(src, dst_path / src.name)
        elif src.is_file():
            shutil.copy2(src, dst_path)
        else:
            # file does not exist
            pass


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

    if model is None:
        model = get_model()

    if reactor is None:
        reactor = get_relative_project_path(get_reactor())

    root = project_root()
    if not root:
        raise RuntimeError(
            "could not find Atomkraft project: are you in the right directory?"
        )

    timestamp = time.time()

    print(f"Generating traces for {model.name} ...")

    try:
        model_result = generate_traces(
            None, model, tests, checker_params=checker_params
        )
    except Exception as e:
        raise RuntimeError(f"[Modelator] {e}")

    test_dir = root / "tests"
    test_dir.mkdir(exist_ok=True)

    timestamp = datetime.now().isoformat(timespec="milliseconds")

    test_group = f"{model.stem}_{timestamp}"
    test_group = (
        test_group.replace("/", "_")
        .replace(".", "_")
        .replace(":", "_")
        .replace("-", "_")
    )

    test_name = f"test_{test_group}"

    successul_ops = model_result.successful()

    test_list = []

    for op in successul_ops:
        print(f"Preparing test for {op} ...")
        for trace_path in model_result.trace_paths(op):
            trace = Path(trace_path)
            if all(not c.isdigit() for c in trace.name):
                continue

            trace_name = trace.name.removesuffix(".itf.json")
            print(f"Using {trace} ...")
            trace = get_relative_project_path(trace)
            test_path = test_dir / test_name / f"test_{op}_{trace_name}.py"
            test_path.parent.mkdir(parents=True, exist_ok=True)
            with open(test_path, "w") as test:
                print(f"Writing {test_path.name} ...")
                test.write(
                    TRACE_TEST_STUB.format(
                        json.dumps(str(reactor).replace("/", ".").removesuffix(".py")),
                        json.dumps(str(trace)),
                        json.dumps(keypath),
                    )
                )
            test_list.append((trace, test_path))

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

    exit_code = pytest.main(
        pytest_args + [str(test_file) for (_, test_file) in test_list]
    )

    for (trace, _) in test_list:
        copy_if_exists(
            [Path(trace), root / ATOMKRAFT_INTERNAL_DIR / VALIDATOR_DIR], report_dir
        )

    if successul_ops:
        print(f"Test data is saved at {report_dir}")
    else:
        print("No trace is produced.")

    return int(exit_code)
