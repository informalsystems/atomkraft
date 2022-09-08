from pathlib import Path
from typing import List, Optional

import typer
from atomkraft.config.atomkraft_config import AtomkraftConfig
from atomkraft.utils.project import get_relative_project_path, project_root

from .model import MODEL_CONFIG_KEY, test_model
from .trace import TRACE_CONFIG_KEY, test_trace, test_trace_dir

app = typer.Typer(rich_markup_mode="rich", add_completion=False)


def FileOption(help, default):
    return typer.Option(
        None,
        exists=True,
        file_okay=True,
        dir_okay=False,
        show_default=False,
        help=f"{help} [grey30][default: set via [bold cyan]atomkraft {default}[/bold cyan]][/grey30]",
    )


def PathOption(help, default):
    return typer.Option(
        None,
        exists=True,
        file_okay=True,
        dir_okay=True,
        show_default=False,
        help=f"{help} [grey30][default: set via [bold cyan]atomkraft {default}[/bold cyan]][/grey30]",
    )


def RequiredFileOption(help, default):
    return typer.Option(
        ...,
        exists=True,
        file_okay=True,
        dir_okay=False,
        show_default=False,
        help=f"{help} [grey30][default: set via [bold cyan]atomkraft {default}[/bold cyan]][/grey30]",
    )


@app.command()
def trace(
    # currently, require the trace to be present.
    # later, there will be an option to pick up the last one from the model
    path: Optional[Path] = PathOption(
        "trace or directory of traces to execute", "model"
    ),
    reactor: Optional[Path] = FileOption("reactor to interpret the trace", "reactor"),
    keypath: str = typer.Option(
        "action",
        show_default=True,
        help="Path to key used as step name, extracted from ITF states",
    ),
    all_: bool = typer.Option(
        False,
        "--all",
        show_default=False,
        help="Recursively find and execute traces from default trace directory",
    ),
    verbose: bool = typer.Option(
        False, "--verbose", "-v", help="Output logging on console"
    ),
):
    """
    Test blockchain by running one trace
    """

    if all_ or (path is not None and path.is_dir()):
        if path is None:
            path = project_root() / "traces"
        exit_code = test_trace_dir(path, reactor, keypath, verbose)
    elif path is None or path.is_file():
        exit_code = test_trace(path, reactor, keypath, verbose)
    else:
        raise RuntimeError("--trace and --all can not be used together.")

    if path and path.is_file():
        with AtomkraftConfig() as c:
            c[TRACE_CONFIG_KEY] = str(get_relative_project_path(path))

    raise typer.Exit(exit_code)


@app.command()
def model(
    model: Optional[Path] = FileOption("model used to generate traces", "model"),
    config: Optional[Path] = FileOption("model configuration", "model"),
    test: List[str] = typer.Option(
        None,
        show_default=False,
        help="model operator(s) describing test traces. multiple can be given either comma-separated, or via separate --test options",
    ),
    reactor: Optional[Path] = FileOption("reactor to interpret the traces", "reactor"),
    keypath: str = typer.Option(
        "action",
        show_default=True,
        help="Path to key used as step name, extracted from ITF states",
    ),
    max_trace: Optional[int] = typer.Option(
        None, show_default=False, help="Maximum number of traces to generate"
    ),
    view: Optional[str] = typer.Option(
        None,
        show_default=False,
        help="View projector to generate only interesting traces",
    ),
    verbose: bool = typer.Option(
        False, "--verbose", "-v", help="Output logging on console"
    ),
):
    """
    Test blockchain by running multiple traces generated from a model
    """
    tests = [t.strip() for ts in test for t in ts.split(",")]

    checker_args = dict()

    if max_trace:
        checker_args["max_error"] = str(max_trace)
    if view:
        checker_args["view"] = view

    exit_code = test_model(model, tests, reactor, keypath, checker_args, verbose)

    if model:
        with AtomkraftConfig() as c:
            c[MODEL_CONFIG_KEY] = str(get_relative_project_path(model))

    raise typer.Exit(exit_code)
