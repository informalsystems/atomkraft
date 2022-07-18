from typing import Optional

import typer

from .node import Account, Coin, ConfigPort, Node
from .testnet import Testnet

__all__ = ["Testnet", "Account", "Node", "ConfigPort", "Coin"]


app = typer.Typer()


@app.command()
def config(key: str, value: Optional[str] = typer.Argument(None)):
    print(key, value)


@app.command()
def testnet(
    chain_id: str,
    validator: int,
    account: int,
    binary: str,
    denom: str,
    prefix: str,
    coin_type: int,
    overwrite: bool,
    keep: bool,
):
    coin_type = 118

    genesis_config = {
        "app_state.gov.voting_params.voting_period": "600s",
        "app_state.mint.minter.inflation": "0.300000000000000000",
    }

    node_config = {
        "config/app.toml": {
            "api.enable": True,
            "api.swagger": True,
            "api.enabled-unsafe-cors": True,
            "minimum-gas-prices": f"0.10{denom}",
            "rosetta.enable": False,
        },
        "config/config.toml": {
            "instrumentation.prometheus": False,
            "p2p.addr_book_strict": False,
            "p2p.allow_duplicate_ip": True,
        },
    }

    net = Testnet(
        chain_id,
        n_validator=validator,
        n_account=account,
        binary=binary,
        denom=denom,
        prefix=prefix,
        coin_type=coin_type,
        genesis_config=genesis_config,
        node_config=node_config,
        account_balance=10**26,
        validator_balance=10**16,
        overwrite=overwrite,
        keep=keep,
    )

    net.oneshot()
    try:
        time.sleep(600)
    except KeyboardInterrupt:
        print("\ntear-down!")
