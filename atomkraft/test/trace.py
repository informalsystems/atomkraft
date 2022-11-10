from pathlib import Path
from typing import Optional

from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.test.test import Test, all_traces_from
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

    test = Test(root, trace)
    test.create_file([trace], reactor, keypath)
    return test.execute(verbose)


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

    test = Test(root, trace_dir)
    test.create_file(trace_paths, reactor, keypath)
    return test.execute(verbose)
