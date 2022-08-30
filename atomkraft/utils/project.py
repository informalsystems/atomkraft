import os
from pathlib import Path


class NoProjectError(RuntimeError):
    def __init__(self) -> None:
        super().__init__("Outside of Atomkraft project")


def project_root() -> Path:
    cwd = Path(os.getcwd())
    while cwd != cwd.parent:
        if (
            (cwd / "pyproject.toml").exists()
            and (cwd / "atomkraft.toml").exists()
            and (cwd / ".atomkraft" / "config.toml").exists()
        ):
            return cwd
        cwd = cwd.parent
    raise NoProjectError
