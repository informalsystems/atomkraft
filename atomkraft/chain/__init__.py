import json
import time
from typing import Optional

import tomlkit
import typer
from atomkraft.utils import project

from pathlib import Path

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
            if property_path is not None:
                keys = property_path.split(".")
                for key in keys:
                    match data:
                        case dict():
                            try:
                                data = data[key]
                            except KeyError:
                                try:
                                    data = data[key.replace("-", "_")]
                                except KeyError:
                                    data = data[key.replace("_", "-")]
                                except Exception as e:
                                    raise e
                        case list():
                            data = data[int(key)]
            print(json.dumps({property_path: data}, indent=2))
    else:
        try:
            value = eval(value)
        except:
            pass
        with open(f"{project.project_root()}/chain.toml") as f:
            main_data = tomlkit.load(f)
            if property_path is not None:
                data = main_data
                keys = property_path.split(".")
                for key in keys[:-1]:
                    match data:
                        case dict():
                            try:
                                data = data[key]
                            except KeyError:
                                try:
                                    data = data[key.replace("-", "_")]
                                except KeyError:
                                    data = data[key.replace("_", "-")]
                                except Exception as e:
                                    raise e
                        case list():
                            data = data[int(key)]
                match data:
                    case dict():
                        key = keys[-1]
                        try:
                            data[key] = value
                        except KeyError:
                            try:
                                data[key.replace("-", "_")] = value
                            except KeyError:
                                data[key.replace("_", "-")] = value
                            except Exception as e:
                                raise e
                    case list():
                        data[int(keys[-1])] = value
            else:
                main_data = value
        with open(f"{project.project_root()}/chain.toml", "w") as f:
            tomlkit.dump(main_data, f)


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
    testnet.keep = True
    testnet.overwrite = True
    testnet.data_dir = ".atomkraft"

    testnet.oneshot()
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        print("\ntear-down!")
