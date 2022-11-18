import sys
from pathlib import Path
from typing import Callable, Dict, Optional, Type

import modelator
import pytest
import typer
from atomkraft import __version__
from atomkraft.utils.project import NoProjectError, init_project, project_root
from rich import print

from .. import chain, test
from ..reactor.reactor import generate_reactor


class ErrorHandlingTyper(typer.Typer):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.error_handlers: Dict[Type[Exception], Callable[[Exception], int]] = {}

    def error_handler(self, exc: Type[Exception]):
        def decorator(f: Callable[[Exception], int]):
            self.error_handlers[exc] = f
            return f

        return decorator

    def __call__(self, *args, **kwargs):
        try:
            super(ErrorHandlingTyper, self).__call__(*args, **kwargs)
        except Exception as e:
            try:
                callback = self.error_handlers[type(e)]
                exit_code = callback(e)
                raise typer.Exit(code=exit_code)
            except typer.Exit as e:
                sys.exit(e.exit_code)
            except KeyError:
                print(e)
                raise typer.Exit(1)


app = ErrorHandlingTyper(
    add_completion=False,
    name="atomkraft",
    no_args_is_help=True,
    rich_markup_mode="rich",
)


def debug_callback(flag: bool):
    if not flag:
        app.pretty_exceptions_enable = False

        def exception_handler(exception_type, exception, _):
            print(f"{exception_type.__name__}: {exception}")

        sys.excepthook = exception_handler


@app.callback()
def main(
    ctx: typer.Context,
    debug: bool = typer.Option(None, callback=debug_callback),
):
    pass


@app.error_handler(NoProjectError)
def noproject_error_handler(e) -> int:
    print("You are outside of Atomkraft project")
    print("You can create an Atomkraft project using `atomkraft init <PROJECT-NAME>`")
    return 1


@app.command()
def version():
    """Print version of the atomkraft executable"""
    print(f"atomkraft {__version__}")


@app.command(
    no_args_is_help=True,
)
def init(
    name: str = typer.Argument(..., help="Name of new directory", show_default=False),
):
    """
    Initialize new Atomkraft project in the given directory
    """
    dir_path = Path.cwd() / name

    if (dir_path).exists():
        print(
            f"[red bold]{'Error'.rjust(12)}[/red bold]  A directory `{name}` already exists!"
        )
        raise typer.Exit(1)

    init_project(name, Path.cwd() / name)

    print(
        f"[green bold]{'Created'.rjust(12)}[/green bold]  Atomkraft project `{name}`."
    )


app.add_typer(
    modelator.cli.app,
    name="model",
    short_help="Work with TLA+ models: load, typecheck, check invariants, or sample traces",
    no_args_is_help=True,
)
app.add_typer(
    chain.app,
    name="chain",
    help="Modify or control Cosmos-SDK chain",
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
# atomkraft reactor --actions-list=act1,act2,act3 --variables-list=x,y,z --reactor-stub-file=path/to/the/file
# or
# atomkraft reactor --actions-list="act1, act2, act3" --variables-list="x, y, z" --reactor-stub-file="path/to/the/file"


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
    path: Optional[Path] = typer.Option(
        None,
        file_okay=True,
        dir_okay=False,
        help="path where to create the reactor stub",
    ),
):
    """
    Generate a reactor stub used to interpret test traces
    """
    if path is None:
        path = project_root() / "reactors" / "reactor.py"

    actions = [act.strip() for act in actions.split(",")]
    variables = [var.strip() for var in variables.split(",")]

    if path.is_file():
        typer.confirm(
            "The stub file already exists and it will be overwritten. "
            "Are you sure you want to continue?",
            abort=True,
        )

    generate_reactor(actions, variables, stub_file_path=path)
