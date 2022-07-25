from pathlib import Path

import git
import pytest
import modelator
import typer
import os
from copier import run_auto
from .. import chain, test
from ..reactor.reactor import generate_reactor

app = typer.Typer(
    add_completion=False,
    name="atomkraft",
    no_args_is_help=True,
)

GH_TEMPLATE = "gh:informalsystems/atomkraft"


@app.command(
    no_args_is_help=True,

)
def init(
    name: Path = typer.Argument(..., help="Name of new directory", show_default=False)
):
    """
    Initialize new Atomkraft project in the given directory
    """
    try:
        git.Repo(os.getcwd(), search_parent_directories=True)
    except git.InvalidGitRepositoryError:
        git.Repo.init(name)
    run_auto(GH_TEMPLATE, name, vcs_ref="dev")


app.add_typer(
    modelator.cli.app,
    name="model",
    short_help="Work with TLA+ models: load, typecheck, check invariants, or sample traces",
    no_args_is_help=True,
)
app.add_typer(
    chain.app,
    name="chain",
    help="Modify or constrol Cosmos-SDK chain",
    no_args_is_help=True,
)
app.add_typer(
    test.app,
    name="test",
    short_help="Test the blockchain based on abstract traces, either explicitly given or produced from models",
    no_args_is_help=True,
)


@app.command(
    no_args_is_help=True,
)
def smoke_test():
    """
    Run smoke tests for a Cosmos-SDK chain
    """
    pytest.main([".atomkraft/smoke_tests"])


# run with:
# poetry run atomkraft reactor --actions-list=act1,act2,act3 --variables-list=x,y,z --reactor-stub-file=path/to/the/file
# or
# poetry run atomkraft reactor --actions-list="act1, act2, act3" --variables-list="x, y, z" --reactor-stub-file="path/to/the/file"


@app.command(
    no_args_is_help=True,
)
def reactor(
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
    generate_reactor(actions, variables, stub_file_path=path.name)
