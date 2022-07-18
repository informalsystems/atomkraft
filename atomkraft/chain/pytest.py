import time

import pytest

from .testnet import Testnet


@pytest.fixture
def testnet():
    chain_id = "test-cosmoshub"
    binary = "gaiad"
    denom = "uatom"
    prefix = "cosmos"
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
            "minimum-gas-prices": "0.10{denom}",
            "rosetta.enable": False,
        },
        "config/config.toml": {
            "instrumentation.prometheus": False,
            "p2p.addr_book_strict": False,
            "p2p.allow_duplicate_ip": True,
        },
    }

    testnet = Testnet(
        chain_id,
        n_validator=3,
        n_account=3,
        binary=binary,
        denom=denom,
        prefix=prefix,
        coin_type=coin_type,
        genesis_config=genesis_config,
        node_config=node_config,
        account_balance=10**26,
        validator_balance=10**16,
    )

    testnet.oneshot()
    time.sleep(10)
    yield testnet
    time.sleep(2)
