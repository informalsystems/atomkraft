from typing import List, Optional

import pytest
import typer
from copier import run_auto

from .. import chain

app = typer.Typer(name="atomkraft", no_args_is_help=True)


@app.command()
def init(binary: str, include: Optional[List[str]] = typer.Argument(None)):
    print(f"Binary {binary}, include {include}")
    run_auto("gh:informalsystems/atomkraft", ".", vcs_ref="dev")


app.add_typer(chain.app, name="chain")


@app.command()
def smoke_test():
    pytest.main([".atomkraft/smoke_tests"])
