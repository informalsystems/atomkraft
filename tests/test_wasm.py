import time

import pytest
from atomkraft.chain.pytest import Testnet
from modelator.pytest.decorators import itf, mbt

pytest_plugins = ["reactors.cosmwasm"]

# add terra-sdk in pyproject.toml
# terra-sdk = {git = "https://github.com/informalsystems/terra.py", rev = "rano/cosmos"}


@pytest.fixture(scope="session")
def testnet():
    chain_id = "test-cw"
    binary = "junod"
    denom = "stake"
    prefix = "juno"
    coin_type = 118

    genesis_config = {
        "app_state.gov.voting_params.voting_period": "600s",
        "app_state.mint.minter.inflation": "0.300000000000000000",
    }

    node_config = {
        "app": {
            "api.enable": True,
            "api.swagger": True,
            "api.enabled-unsafe-cors": True,
            "minimum-gas-prices": f"0.10{denom}",
            "rosetta.enable": False,
        },
        "config": {
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


@pytest.fixture
def contract_data():
    return {}


# @mbt("specs/counter.tla", keypath="last_msg.name", checker_params={"view", "View2"})
# def test_traces_from_model():
#     print("auto-generated traces from tla file executed succesfully")


@itf("tests/traces/example0.itf.json", keypath="last_msg.name")
@itf("tests/traces/example1.itf.json", keypath="last_msg.name")
@itf("tests/traces/example2.itf.json", keypath="last_msg.name")
def test_use_generated_traces():
    print("itf traces executed succesfully")
