import time

from atomkraft.chain import Testnet
from terra_sdk.client.lcd import LCDClient
from terra_sdk.client.lcd.api.tx import CreateTxOptions
from terra_sdk.core import Coins
from terra_sdk.core.fee import Fee
from terra_sdk.core.staking import MsgDelegate
from terra_sdk.key.mnemonic import MnemonicKey

chain_id = "test-cosmoshub"
binary = "gaiad"
denom = "stake"

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
        "rosetta.enable": True,
    },
    "config/config.toml": {
        "instrumentation.prometheus": False,
        "p2p.addr_book_strict": False,
        "p2p.allow_duplicate_ip": True,
    },
}


net = Testnet(
    chain_id,
    n_validator=3,
    n_account=3,
    binary=binary,
    denom=denom,
    coin_type=118,
    genesis_config=genesis_config,
    node_config=node_config,
    account_balance=10**26,
    validator_balance=10**16,
)

net.prepare()

url = net.validator_nodes[0].get_port(net.ports()["lcd"])

net.spinup()

time.sleep(10)

validators = net.validators

client = LCDClient(
    url=url, chain_id=chain_id, gas_prices=f"0.15{denom}", gas_adjustment=1.75
)

wallets = [
    client.wallet(
        MnemonicKey(net.prefix, mnemonic=validator.mnemonic, coin_type=net.coin_type)
    )
    for validator in validators
]

msg_del = MsgDelegate(
    validator_address=validators[1].validator_address(net.prefix),
    delegator_address=validators[2].address(net.prefix),
    amount=f"1000000{denom}",
)

tx = wallets[2].create_and_sign_tx(
    CreateTxOptions(msgs=[msg_del], fee=Fee(200000, Coins.from_str(f"20000{denom}")))
)
result = client.tx.broadcast(tx)
print(f"TXHASH: {result.txhash}")
print("[ping.pub]", f"http://0.0.0.0/localnet/tx/{result.txhash}")

print("Ctrl+C to exit..")

while True:
    try:
        time.sleep(1)
    except KeyboardInterrupt:
        break
