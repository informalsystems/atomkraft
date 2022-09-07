import os
from pathlib import Path
from typing import Union

from atomkraft.config.atomkraft_config import ATOMKRAFT_INTERNAL_DIR


class NoProjectError(RuntimeError):
    def __init__(self) -> None:
        super().__init__("Outside of Atomkraft project")


def project_root() -> Path:
    cwd = Path(os.getcwd())
    while cwd != cwd.parent:
        if (
            (cwd / "pyproject.toml").exists()
            and (cwd / "atomkraft.toml").exists()
            and (cwd / ATOMKRAFT_INTERNAL_DIR / "config.toml").exists()
        ):
            return cwd
        cwd = cwd.parent
    raise NoProjectError


def get_absolute_project_path(path: Union[Path, str]) -> Path:
    if isinstance(path, str):
        return project_root() / Path(path)
    else:
        return path.absolute()


def get_relative_project_path(path: Path) -> Path:
    if path.is_absolute():
        return path.relative_to(project_root())
    else:
        return path.absolute().relative_to(project_root())
