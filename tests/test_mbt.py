from frozendict import frozendict
from modelator.pytest.decorators import itf, mbt, step
from terra_sdk.client.lcd.api.tx import CreateTxOptions
from terra_sdk.core import Coins, Coin
from terra_sdk.core.fee import Fee
from terra_sdk.core.staking import MsgDelegate, MsgUndelegate
from terra_sdk.core.bank import MsgSend
import time

# TODO: fix nested decorator for steps


def map_account(accounts, validators, account_str):
    match account_str:
        case "user1":
            return accounts[0]
        case "user2":
            return accounts[1]
        case "user3":
            return accounts[2]
        case "validator":
            return validators[0]
        case _:
            raise RuntimeError(f"unknown account: {account_str}")


def convert(obj):
    if type(obj) == int or type(obj) == str or type(obj) == bool:
        # return the literal as is
        return obj
    elif type(obj) == list:
        # convert to a tuple, so we can put it into a set or a dict
        return tuple([convert(e) for e in obj])
    elif type(obj) == dict:
        keys = obj.keys()
        if "#bigint" in keys:
            return int(obj["#bigint"])
        if "#tup" in keys:
            return tuple([convert(e) for e in obj["#tup"]])
        if "#set" in keys:
            # use a frozenset, so we can put them into a set or a dict
            return frozenset([convert(e) for e in obj["#set"]])
        if "#map" in keys:
            # convert to a frozendict
            return frozendict({convert(k): convert(v) for (k, v) in obj["#map"]})
        else:
            # use a frozendict, so we can put it into a set or another dict
            return frozendict({k: convert(v) for (k, v) in obj.items()})
    else:
        raise RuntimeError(f"Unexpected input: {obj}")


@step("None")
def init(lastTx):
    assert lastTx["tag"] == "None"


@step("delegate")
def delegate(lcdclient, validators, accounts, lastTx, balanceOf, unbonded):
    (lastTx, balanceOf, unbonded) = (
        convert(lastTx),
        convert(balanceOf),
        convert(unbonded),
    )
    coin = Coin("stake", lastTx["value"])
    sender = map_account(accounts, validators, lastTx["sender"])
    validator = map_account(accounts, validators, "validator")
    # delegate coin to validator
    msg_del = MsgDelegate(
        validator_address=validator.key.val_address,
        delegator_address=sender.key.acc_address,
        amount=coin,
    )
    tx = sender.create_and_sign_tx(
        CreateTxOptions(msgs=[msg_del], fee=Fee(200000, Coins.from_str("20000stake")))
    )
    result = lcdclient.tx.broadcast(tx)
    # wait for transaction to be included
    time.sleep(10)
    # check that the balance of the sender has decreased as expected
    cosmos_bal = lcdclient.bank.balance(sender.key.acc_address)[0]["stake"].amount
    expected_bal = balanceOf[lastTx["sender"]] + unbonded[lastTx["sender"]]
    print(f"cosmos balance:   {cosmos_bal}")
    print(f"expected balance: {expected_bal}")
    if cosmos_bal > expected_bal:
        diff = cosmos_bal - expected_bal
        print(f"{lastTx['sender']} has {diff} more coins as expected (due to rewards?)")


@step("unbond")
def unbond(lcdclient, validators, accounts, lastTx, balanceOf, unbonded):
    (lastTx, balanceOf, unbonded) = (
        convert(lastTx),
        convert(balanceOf),
        convert(unbonded),
    )
    coin = Coin("stake", lastTx["value"])
    sender = map_account(accounts, validators, lastTx["sender"])
    validator = map_account(accounts, validators, "validator")
    # unbond coin from validator
    msg_del = MsgUndelegate(
        validator_address=validator.key.val_address,
        delegator_address=sender.key.acc_address,
        amount=coin,
    )
    tx = sender.create_and_sign_tx(
        CreateTxOptions(msgs=[msg_del], fee=Fee(200000, Coins.from_str("20000stake")))
    )
    result = lcdclient.tx.broadcast(tx)
    # wait for transaction to be included
    time.sleep(10)
    # check that the balance of the sender has increased as expected
    cosmos_bal = lcdclient.bank.balance(sender.key.acc_address)[0]["stake"].amount
    expected_bal = balanceOf[lastTx["sender"]] + unbonded[lastTx["sender"]]
    print(f"cosmos balance:   {cosmos_bal}")
    print(f"expected balance: {expected_bal}")
    if cosmos_bal > expected_bal:
        diff = cosmos_bal - expected_bal
        print(f"{lastTx['sender']} has {diff} more coins as expected (due to rewards?)")


@step("transfer-cosmos")
def transfer_cosmos(lcdclient, accounts, validators, lastTx):
    lastTx = convert(lastTx)
    coin = Coin("stake", lastTx["value"])
    sender = map_account(accounts, validators, lastTx["sender"])
    receiver = map_account(accounts, validators, lastTx["toAddr"])
    # send coin from sender to receiver
    msg_del = MsgSend(
        from_address=sender.key.acc_address,
        to_address=receiver.key.acc_address,
        amount=Coins([coin]),
    )
    tx = sender.create_and_sign_tx(
        CreateTxOptions(msgs=[msg_del], fee=Fee(200000, Coins.from_str("20000stake")))
    )
    result = lcdclient.tx.broadcast(tx)
    # wait for transaction to be included
    time.sleep(10)
    # did the transaction succeed?


@itf("examples/cosmos-sdk/traces/trace2.itf.json", keypath="lastTx.tag")
def test_sample_itf():
    print("itf-single-trace")


# @mbt("model.tla", "model.cfg")
# def test_sample_model():
#     print("tla-multi-trace")
