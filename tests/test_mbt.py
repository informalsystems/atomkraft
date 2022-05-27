from modelator.pytest.decorators import itf, mbt, step

# TODO: fix nested decorator for steps


@step("None")
def init(testnet, balanceOf, delegated, failed, lastTx, nextTxId, unbonded):
    assert lastTx["tag"] == "None"


@step("delegate")
def delegate(testnet, balanceOf, delegated, failed, lastTx, nextTxId, unbonded):
    assert lastTx["tag"] == "delegate"


@step("transfer-cosmos")
def transfer(testnet, balanceOf, delegated, failed, lastTx, nextTxId, unbonded):
    assert lastTx["tag"] == "transfer-cosmos"


@itf("examples/cosmos-sdk/traces/trace2.itf.json", keypath="lastTx.tag")
def test_sample_itf():
    print("itf-single-trace")


# @mbt("model.tla", "model.cfg")
# def test_sample_model():
#     print("tla-multi-trace")
