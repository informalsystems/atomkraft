from typing import List, Optional

import typer

from .trace import test_trace

app = typer.Typer(rich_markup_mode="rich", add_completion=False)


def FileOption(help, default):
    return typer.Option(
        None,
        show_default=False,
        help=f"{help} [grey30][default: set via [bold cyan]atomkraft {default}[/bold cyan]][/grey30]",
    )


def RequiredFileOption(help, default):
    return typer.Option(
        ...,
        show_default=False,
        help=f"{help} [grey30][default: set via [bold cyan]atomkraft {default}[/bold cyan]][/grey30]",
    )


@app.command()
def trace(
    # currently, require the trace to be present.
    # later, there will be an option to pick up the last one from the model
    trace: typer.FileText = RequiredFileOption("trace to execute", "model"),
    reactor: typer.FileText = FileOption("reactor to interpret the trace", "reactor"),
    keypath: str = typer.Option(
        "action",
        show_default=True,
        help="Path to key used as step name, extracted from ITF states",
    ),
):
    """
    Test blockchain by running one trace
    """

    test_trace(trace.name, reactor if reactor is None else reactor.name, keypath)


@app.command()
def model(
    model: typer.FileText = FileOption("model used to generate traces", "model"),
    config: typer.FileText = FileOption("model configuration", "model"),
    reactor: typer.FileText = FileOption("reactor to interpret the traces", "reactor"),
    test: Optional[List[str]] = typer.Option(
        None,
        show_default=False,
        help="model operator(s) describing test traces. multiple can be given either comma-separated, or via separate --test options",
    ),
):
    """
    Test blockchain by running multiple traces generated from a model
    """
    tests = [ts.split(",") for ts in test]
    tests = [t.strip() for ts in tests for t in ts]
    print(
        f"""
    Model: {model}
    Config: {config}
    Reactor: {reactor}
    Tests: {tests}
    """
    )
