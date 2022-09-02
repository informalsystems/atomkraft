import shutil
import time
from datetime import datetime
from pathlib import Path
from typing import List, Optional

import pytest
from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.model.traces import generate_traces
from atomkraft.utils.project import (
    get_absolute_project_path,
    get_relative_project_path,
    project_root,
)

from ..reactor.reactor import get_reactor
from .trace import TRACE_TEST_STUB

# a key for the model path inside internal config
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
    verbose: bool,
):
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
        model_result = generate_traces(None, model, tests)
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

    root_report_dir = root / "reports" / test_group

    successul_ops = model_result.successful()

    for op in successul_ops:
        print(Path(model_result.trace_paths(op)[0]).parent)
        trace_dir = Path(model_result.trace_paths(op)[0]).parent
        trace = max(trace_dir.glob("*.itf.json"), key=lambda x: x.stat().st_mtime)
        trace = get_relative_project_path(trace)
        test_name = f"test_{test_group}"
        test_path = test_dir / test_name / f"test_{op}.py"
        test_path.parent.mkdir(parents=True)
        with open(test_path, "w") as test:
            print(f"Writing {test_name} ...")
            test.write(
                TRACE_TEST_STUB.format(
                    str(reactor).replace("/", ".").removesuffix(".py"), trace, keypath
                )
            )

        report_dir = root_report_dir / test_path.stem
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

        pytest.main(pytest_args + [str(test_path)])

        copy_if_exists([Path(trace), root / ".atomkraft" / "nodes"], report_dir)

    if successul_ops:
        print(f"Test data is saved at {root_report_dir}")
    else:
        print("No trace is produced.")
