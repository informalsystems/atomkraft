from typing import List, Optional

import pytest
import typer
from copier import run_auto

from .. import chain, test

app = typer.Typer(name="atomkraft", no_args_is_help=True)


@app.command()
def init(binary: str, include: Optional[List[str]] = typer.Argument(None)):
    print(f"Binary {binary}, include {include}")
    run_auto("gh:informalsystems/atomkraft", ".", vcs_ref="dev")


app.add_typer(chain.app, name="chain")
app.add_typer(test.app, name="test", short_help="Test the blockchain based on abstract traces, either explicitly given or produced from models")


@app.command()
def smoke_test():
    pytest.main([".atomkraft/smoke_tests"])
