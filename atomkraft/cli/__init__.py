from pathlib import Path

import git
import pytest
import modelator
import typer
import os
from copier import run_auto
from typing import List, Optional
from .. import chain, test
from ..reactor import reactor

app = typer.Typer(
    rich_markup_mode="rich",
    add_completion=False,
    name="atomkraft",
    no_args_is_help=True,
)

GH_TEMPLATE = "gh:informalsystems/atomkraft"


@app.command()
def init(
    name: Path = typer.Argument(..., help="Name of new directory", show_default=False)
):
    """
    Initialize new Atomkraft project in the given directory
    """
    git.Repo.init(name)
    run_auto(GH_TEMPLATE, name, vcs_ref="rano/impl-adr02")


app.add_typer(
    modelator.cli.app,
    name="model",
    short_help="Work with TLA+ models: load, typecheck, check invariants, or sample traces",
)
app.add_typer(chain.app, name="chain")
app.add_typer(
    test.app,
    name="test",
    short_help="Test the blockchain based on abstract traces, either explicitly given or produced from models",
)


@app.command()
def smoke_test():
    pytest.main([".atomkraft/smoke_tests"])


# run with:
# poetry run atomkraft reactor --actions-list=act1,act2,act3 --variables-list=x,y,z --reactor-stub-file=path/to/the/file
# or
# poetry run atomkraft reactor --actions-list="act1, act2, act3" --variables-list="x, y, z" --reactor-stub-file="path/to/the/file"


@app.command("reactor")
def reactor_command(
    actions: str = typer.Option(
        ...,
        help="trace actions for which to create reactor stub functions",
        show_default=False,
    ),
    variables: str = typer.Option(
        ...,
        help="state variables to use as parameters for reactor stub functions.",
        show_default=False,
    ),
    path: typer.FileTextWrite = typer.Option(
        os.path.abspath("reactors/reactor.py"),
        help="path where to create the reactor stub",
    ),
):
    """
    Generate a reactor stub used to interpret test traces
    """
    actions = [act.strip() for act in actions.split(",")]
    variables = [var.strip() for var in variables.split(",")]
    reactor.generate_reactor(actions, variables, stub_file_path=path.name)
