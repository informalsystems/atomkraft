import os
from pathlib import Path
from typing import List, Optional

import pytest
import typer
from copier import run_auto
from git import Repo

from .. import chain

app = typer.Typer(name="atomkraft", no_args_is_help=True)

cwd = os.getcwd()
git_repo = Repo(cwd, search_parent_directories=True)
git_root = git_repo.git.rev_parse("--show-toplevel")

GH_TEMPLATE = "gh:informalsystems/atomkraft"
LOCAL_TEMPLATE = f"{git_root}"


@app.command()
def init(path: Path):
    Repo.init(path)
    run_auto(GH_TEMPLATE, path, vcs_ref="rano/impl-adr02")


app.add_typer(chain.app, name="chain")


@app.command()
def smoke_test():
    pytest.main([".atomkraft/smoke_tests"])
