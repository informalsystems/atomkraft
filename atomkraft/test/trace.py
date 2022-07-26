from os import PathLike
from atomkraft.utils.project import project_root
import os.path
from datetime import datetime


trace_test_stub = """
from modelator.pytest.decorators import itf

pytest_plugins = "{0}"

@itf("{1}", keypath="{2}")
def test_trace():
    print("Successfully executed trace {1}")
"""


def test_trace(trace: PathLike, reactor: PathLike, keypath: str):
    """
    Test blockchain by running one trace
    """

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
    test = os.path.join(tests, f"{test_name}.py")
    with open(test, "w") as test:
        test.write(
            trace_test_stub.format(
                str(reactor).replace("/", ".").replace(".py", ""), trace, keypath
            )
        )
