from pathlib import Path
from typing import Optional

from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.test.helpers import all_traces_from, create_test, execute_test
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
    Returns the path to the current trace from the internal config.
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
    Test blockchain by running one trace.
    """

    root = project_root()
    if not root:
        raise RuntimeError(
            "Could not find Atomkraft project: are you in the right directory?"
        )

    if trace is None:
        trace = get_trace()

    if reactor is None:
        reactor = get_relative_project_path(get_reactor())

    test_name, test_file_path = create_test(root, trace, [trace], reactor, keypath)
    return execute_test(root, test_name, test_file_path, [trace], verbose)

    # test_name, test_file_path = create_test(root, trace, reactor, keypath)

    # print(f"Executing test {test_name} ...")
    # val_root_dir = prepare_validators(root)
    # pytest_args, report_dir = mk_pytest_args(os.path.dirname(test_file_path), verbose)
    # exit_code = pytest.main(pytest_args + [test_file_path])

    # save_validator_files(val_root_dir, report_dir, [trace])
    # # copy_if_exists([trace, val_root_dir], report_dir)
    # print(f"Test data for {test_name} is saved at {report_dir}")

    # return int(exit_code)


def test_trace_dir(
    trace_dir: Path, reactor: Optional[Path], keypath: str, verbose: bool
):
    """
    Test blockchain by running all available traces in trace_dir.
    """

    root = project_root()
    if not root:
        raise RuntimeError(
            "Could not find Atomkraft project: are you in the right directory?"
        )

    if reactor is None:
        reactor = get_relative_project_path(get_reactor())

    trace_paths = all_traces_from(trace_dir)
    if not trace_paths:
        print(f"No trace found in {trace_dir}.")
        return 1

    test_name, test_file_path = create_test(
        root, trace_dir, trace_paths, reactor, keypath
    )
    return execute_test(root, test_name, test_file_path, trace_paths, verbose)
