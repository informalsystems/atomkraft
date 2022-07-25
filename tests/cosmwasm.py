import base64
import time

from modelator.pytest.decorators import step
from terra_sdk.client.lcd import LCDClient
from terra_sdk.client.lcd.api.tx import CreateTxOptions
from terra_sdk.core import Coin, Coins
from terra_sdk.core.fee import Fee
from terra_sdk.core.wasm import MsgExecuteContract, MsgInstantiateContract, MsgStoreCode
from terra_sdk.core.wasm.data import AccessConfig, AccessType
from terra_sdk.key.mnemonic import MnemonicKey


@step("store_cw_contract")
def store_contract(testnet, last_msg, contract_data):
    rest_endpoint = testnet.get_validator_port(0, "lcd")
    lcdclient = LCDClient(url=rest_endpoint, chain_id=testnet.chain_id)
    sender_key = testnet.accounts[last_msg["sender"]]
    sender = lcdclient.wallet(
        MnemonicKey(
            testnet.prefix, mnemonic=sender_key.mnemonic, coin_type=testnet.coin_type
        )
    )

    with open("contracts/counter.wasm", "rb") as f:
        counter_cw_code = base64.b64encode(f.read()).decode("ascii")

    msg = MsgStoreCode(
        sender=sender.key.acc_address,
        wasm_byte_code=counter_cw_code,
        instantiate_permission=AccessConfig(AccessType.ACCESS_TYPE_EVERYBODY, None),
    )

    tx = sender.create_and_sign_tx(
        CreateTxOptions(
            msgs=[msg], fee=Fee(20000000, Coins([Coin(testnet.denom, 2000000)]))
        )
    )
    result = lcdclient.tx.broadcast(tx)

    code_id = eval(result.logs[0].events_by_type["store_code"]["code_id"][0])

    contract_data["code_id"] = code_id

    time.sleep(0.5)

    print(msg)
    # print(last_msg)


@step("instantiate")
def instantiate(testnet, last_msg, contract_data):
    rest_endpoint = testnet.get_validator_port(0, "lcd")
    lcdclient = LCDClient(url=rest_endpoint, chain_id=testnet.chain_id)
    sender_key = testnet.accounts[last_msg["sender"]]
    sender = lcdclient.wallet(
        MnemonicKey(
            testnet.prefix, mnemonic=sender_key.mnemonic, coin_type=testnet.coin_type
        )
    )

    dict_msg = {"count": last_msg["cnt"]}

    msg = MsgInstantiateContract(
        sender=sender.key.acc_address,
        admin=sender.key.acc_address,
        code_id=contract_data["code_id"],
        label="counter 1",
        msg=dict_msg,
    )

    tx = sender.create_and_sign_tx(
        CreateTxOptions(
            msgs=[msg], fee=Fee(20000000, Coins([Coin(testnet.denom, 2000000)]))
        )
    )
    result = lcdclient.tx.broadcast(tx)

    contract_address = result.logs[0].events_by_type["instantiate"][
        "_contract_address"
    ][0]

    contract_data["contract_address"] = contract_address

    time.sleep(0.5)

    print(msg)
    # print(last_msg)


@step("reset")
def reset(testnet, last_msg, contract_data):
    rest_endpoint = testnet.get_validator_port(0, "lcd")
    lcdclient = LCDClient(url=rest_endpoint, chain_id=testnet.chain_id)
    sender_key = testnet.accounts[last_msg["sender"]]
    sender = lcdclient.wallet(
        MnemonicKey(
            testnet.prefix, mnemonic=sender_key.mnemonic, coin_type=testnet.coin_type
        )
    )

    dict_msg = {"reset": {"count": last_msg["cnt"]}}
    contract_address = contract_data["contract_address"]

    msg = MsgExecuteContract(
        sender=sender.key.acc_address,
        contract=contract_address,
        msg=dict_msg,
        coins=Coins([Coin(testnet.denom, 20000)]),
    )

    tx = sender.create_and_sign_tx(
        CreateTxOptions(
            msgs=[msg], fee=Fee(20000000, Coins([Coin(testnet.denom, 2000000)]))
        )
    )
    lcdclient.tx.broadcast(tx)

    time.sleep(0.5)

    print(msg)
    # print(last_msg)


@step("increment")
def increment(testnet, last_msg, contract_data):
    rest_endpoint = testnet.get_validator_port(0, "lcd")
    lcdclient = LCDClient(url=rest_endpoint, chain_id=testnet.chain_id)
    sender_key = testnet.accounts[last_msg["sender"]]
    sender = lcdclient.wallet(
        MnemonicKey(
            testnet.prefix, mnemonic=sender_key.mnemonic, coin_type=testnet.coin_type
        )
    )

    dict_msg = {"increment": {}}
    contract_address = contract_data["contract_address"]

    msg = MsgExecuteContract(
        sender=sender.key.acc_address,
        contract=contract_address,
        msg=dict_msg,
        coins=Coins([Coin(testnet.denom, 20000)]),
    )

    tx = sender.create_and_sign_tx(
        CreateTxOptions(
            msgs=[msg], fee=Fee(20000000, Coins([Coin(testnet.denom, 2000000)]))
        )
    )
    lcdclient.tx.broadcast(tx)

    time.sleep(0.5)

    print(msg)
    # print(last_msg)


@step("get_count")
def get_count(testnet, count, last_msg, contract_data):
    rest_endpoint = testnet.get_validator_port(0, "lcd")
    lcdclient = LCDClient(url=rest_endpoint, chain_id=testnet.chain_id)

    dict_msg = {"get_count": {}}
    contract_address = contract_data["contract_address"]

    result = lcdclient.wasm.contract_query(contract_address, dict_msg)

    assert result["count"] == count

    time.sleep(0.5)

    # print(last_msg)
