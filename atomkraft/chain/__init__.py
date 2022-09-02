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

CHAIN_CONFIG_FILE = "chain.toml"


@app.command()
def config(
    property_path: Optional[str] = typer.Argument(
        None, help="Nested keys of a config value, joined by `.`", show_default=False
    ),
    value: Optional[str] = typer.Argument(
        None, help="Update old value with provided value"
    ),
):
    """
    Query or update chain configuration
    """
    if value is None:
        with open(project.project_root() / CHAIN_CONFIG_FILE) as f:
            data = tomlkit.load(f)
        if property_path is None:
            print(json.dumps(data, indent=2))
        else:
            print(json.dumps({property_path: query(data, property_path)}, indent=2))
    else:
        try:
            value = eval(value)
        except (SyntaxError, NameError):
            pass
        with open(project.project_root() / CHAIN_CONFIG_FILE) as f:
            data = update(tomlkit.load(f), property_path, value)
        with open(project.project_root() / CHAIN_CONFIG_FILE, "w") as f:
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
        testnet = Testnet.load_toml(project.project_root() / CHAIN_CONFIG_FILE)
    else:
        testnet = Testnet.load_toml(config)
    testnet.verbose = not silent

    testnet.oneshot()
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        print("\ntear-down!")
