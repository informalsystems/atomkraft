from pathlib import Path

import git
import pytest
import typer
from copier import run_auto

from .. import chain

app = typer.Typer(name="atomkraft", no_args_is_help=True)

GH_TEMPLATE = "gh:informalsystems/atomkraft"


@app.command()
def init(path: Path):
    git.Repo.init(path)
    run_auto(GH_TEMPLATE, path, vcs_ref="rano/impl-adr02")


app.add_typer(chain.app, name="chain")


@app.command()
def smoke_test():
    pytest.main([".atomkraft/smoke_tests"])
