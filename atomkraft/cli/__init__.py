from typing import List, Optional

import typer
from copier import run_auto

app = typer.Typer(name="atomkraft", no_args_is_help=True)


@app.command()
def init(binary: str, include: Optional[List[str]] = typer.Argument(None)):
    print(f"Binary {binary}, include {include}")
    run_auto("gh:informalsystems/atomkraft", ".", vcs_ref="rano/prototype")


chain = typer.Typer()


@chain.command()
def config(key: str, value: Optional[str] = typer.Argument(None)):
    print(key, value)


@chain.command()
def test_drive():
    print()


app.add_typer(chain, name="chain")
