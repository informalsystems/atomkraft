import subprocess

import atomkraft


def test_version():
    poetry_version = (
        subprocess.check_output(["poetry", "version", "-s"]).decode().strip()
    )
    src_version = atomkraft.__version__
    assert poetry_version == src_version
