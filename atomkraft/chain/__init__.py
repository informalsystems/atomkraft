import json
import time
from pathlib import Path
from typing import Optional

import tomlkit
import typer
from atomkraft.utils import project, query, update

from .node import Account, Coin, ConfigPort, Node
from .testnet import Testnet

__all__ = ["Testnet", "Account", "Node", "ConfigPort", "Coin"]


app = typer.Typer()


@app.command()
def config(
    property_path: str = typer.Argument(
        ..., help="Nested keys of a config value, joined by `.`", show_default=False
    ),
    value: Optional[str] = typer.Argument(
        None, help="Update old value with provided value"
    ),
):
    """
    Query or update chain configuration
    """
    if value is None:
        with open(f"{project.project_root()}/chain.toml") as f:
            data = tomlkit.load(f)
        print(json.dumps({property_path: query(data, property_path)}, indent=2))
    else:
        try:
            value = eval(value)
        except (SyntaxError, NameError):
            pass
        with open(f"{project.project_root()}/chain.toml") as f:
            data = update(tomlkit.load(f), property_path, value)
        with open(f"{project.project_root()}/chain.toml", "w") as f:
            tomlkit.dump(data, f)


@app.command()
def testnet(
    silent: bool = typer.Option(False, help="Silent mode. Print no output"),
    config: Optional[Path] = typer.Option(None, help="Path to chain.toml"),
):
    """
    Run a testnet in background
    """
    if config is None:
        testnet = Testnet.load_toml(f"{project.project_root()}/chain.toml")
    else:
        testnet = Testnet.load_toml(config)
    testnet.verbose = not silent

    testnet.oneshot()
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        print("\ntear-down!")
