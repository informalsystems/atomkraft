from pathlib import Path

import git
import pytest
import typer
from copier import run_auto

from .. import chain, test

app = typer.Typer(rich_markup_mode="rich", add_completion=False, name="atomkraft", no_args_is_help=True)

GH_TEMPLATE = "gh:informalsystems/atomkraft"


@app.command()
def init(path: Path):
    git.Repo.init(path)
    run_auto(GH_TEMPLATE, path, vcs_ref="rano/impl-adr02")


app.add_typer(chain.app, name="chain")
app.add_typer(test.app, name="test", short_help="Test the blockchain based on abstract traces, either explicitly given or produced from models")


@app.command()
def smoke_test():
    pytest.main([".atomkraft/smoke_tests"])
