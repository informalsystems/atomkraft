from typing import List, Optional
import typer

app = typer.Typer(rich_markup_mode="rich", add_completion=False)


def FileOption(help, default):
    return typer.Option(
        None,
        show_default=False,
        help=f"{help} [grey30]\[default: set via [bold cyan]atomkraft {default}[/bold cyan]][/grey30]",
    )


@app.command()
def trace(
    trace: typer.FileText = FileOption("trace to execute", "model"),
    reactor: typer.FileText = FileOption("reactor to interpret the trace", "reactor"),
):
    """
    Test blockchain by running one trace
    """
    print(
        f"""
    Trace: {trace}
    Reactor: {reactor}
    """
    )


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
