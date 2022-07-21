from pathlib import Path

import git
import pytest
import typer
import os
from copier import run_auto
from typing import List, Optional

from .. import chain
from ..reactor_room import reactor

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


# run with:
# poetry run atomkraft reactor --actions-list=act1,act2,act3 --variables-list=x,y,z --reactor-stub-file=path/to/the/file
# or
# poetry run atomkraft reactor --actions-list="act1, act2, act3" --variables-list="x, y, z" --reactor-stub-file="path/to/the/file"


@app.command()
def reactor(
    variables_list: str = typer.Option(
        ..., help="A list of state variables to include into reactors as parameters"
    ),
    actions_list: Optional[str] = typer.Option(
        ..., help="A list of actions for which to create reactor stubs."
    ),
    reactor_stub_file: str = typer.Option(
        os.path.abspath("reactors/reactor.py"),
        help="A path where to create the reactors file.",
    ),
):
    actions = [act.strip() for act in actions_list.split(",")]
    variables = [var.strip() for var in variables_list.split(",")]
    reactor.generate_reactor(actions, variables, reactor_stub_file)
