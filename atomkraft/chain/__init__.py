import json
import shutil
import subprocess
import time
from pathlib import Path
from typing import Optional

import copier
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
def remote(
    path: str = typer.Argument(..., help="Local path or git URL", show_default=False),
    ref: Optional[str] = typer.Option(
        str, help="VCS tag/commit to use for git URL", show_default=False
    ),
):
    """Setup chain binary from remote or local path

    Raises:
        RuntimeError: If more than one executable is compiled.
    """
    chain_src_dir = project.project_root() / ".atomkraft" / "src" / Path(path).stem

    # use copier to copy to chain_src_dir (supports local or remote Git)
    copier.run_auto(path, chain_src_dir, vcs_ref=ref, quiet=True)

    # to find compiled executable, we store the current timestamp
    ts = time.time()
    # compile the source
    subprocess.run(["make", "build"], capture_output=True, cwd=chain_src_dir)
    # consider the only executables that are modified after the timestamp
    new_files = [
        e
        for e in chain_src_dir.glob("*/*")
        if e.stat().st_mtime > ts and int(oct(e.stat().st_mode)[-3]) & 1
    ]

    if len(new_files) != 1:
        # there should be only one executable
        raise RuntimeError("Expected one executable file")

    # store the executable in `.atomkraft/bin`
    bin_dir = project.project_root() / ".atomkraft" / "bin"
    bin_dir.mkdir(exist_ok=True)
    binary_file = shutil.copy2(new_files[0], bin_dir)

    # update the chain config
    with open(f"{project.project_root()}/chain.toml") as f:
        data = update(tomlkit.load(f), "binary", str(binary_file))
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
