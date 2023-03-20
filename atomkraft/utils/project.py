import os
import imp
import shutil
import logging
from pathlib import Path
from typing import Union

import jinja2

ATOMKRAFT_INTERNAL_DIR = ".atomkraft"

ATOMKRAFT_VAL_DIR_PREFIX = "val_"


class NoProjectError(RuntimeError):
    def __init__(self) -> None:
        super().__init__("Outside of Atomkraft project")


def project_root() -> Path:
    cwd = Path(os.getcwd())
    while cwd != cwd.parent:
        if (cwd / "atomkraft.toml").exists():
            if not (cwd / "pyproject.toml").exists():
                logging.warn(
                    f"Configuration file pyproject.toml not found in root {cwd}"
                )
            if not (cwd / ATOMKRAFT_INTERNAL_DIR / "config.toml").exists():
                logging.warn(
                    f"Configuration file config.toml not found in {cwd/ATOMKRAFT_INTERNAL_DIR}"
                )
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


def init_project(name: str, dir_path: Path, template: str):
    try:
        loader = jinja2.PackageLoader("atomkraft", f"templates/{template}")
    except ValueError:
        raise RuntimeError(
            f"Template {template} does not exist in atomkraft"
        )
    env = jinja2.Environment(loader=loader)
    env.globals["project_name"] = name
    for tmpl_path in env.list_templates():
        tmpl = env.get_template(tmpl_path)
        final_path = dir_path / tmpl_path
        final_path.parent.mkdir(parents=True, exist_ok=True)
        tmpl.stream().dump(str(final_path))
