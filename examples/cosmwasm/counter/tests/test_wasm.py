from modelator.pytest.decorators import itf, mbt


@mbt("models/counter.tla", keypath="last_msg.name", checker_params={"view", "View2"})
def test_traces_from_model():
    print("auto-generated traces from tla file executed succesfully")


@itf("traces/example0.itf.json", keypath="last_msg.name")
@itf("traces/example1.itf.json", keypath="last_msg.name")
@itf("traces/example2.itf.json", keypath="last_msg.name")
def test_use_generated_traces():
    print("itf traces executed succesfully")
