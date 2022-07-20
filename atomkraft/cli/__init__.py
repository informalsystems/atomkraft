from typing import List, Optional

import pytest
import typer
import os
from copier import run_auto

from .. import chain
from .. import Reactor

app = typer.Typer(name="atomkraft", no_args_is_help=True)


@app.command()
def init(binary: str, include: Optional[List[str]] = typer.Argument(None)):
    print(f"Binary {binary}, include {include}")
    run_auto("gh:informalsystems/atomkraft", ".", vcs_ref="dev")


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
        os.path.abspath("atomkraft/reactors/reactor.py"),
        help="A path where to create the reactors file.",
    ),
):
    actions = [act.strip() for act in actions_list.split(",")]
    variables = [var.strip() for var in variables_list.split(",")]
    Reactor.generate_reactor(actions, variables, reactor_stub_file)
