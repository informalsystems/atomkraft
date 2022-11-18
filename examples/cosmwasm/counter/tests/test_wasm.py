from modelator.pytest.decorators import itf, mbt


@mbt("models/counter.tla", keypath="last_msg.tag", checker_params={"view", "View2"})
def test_traces_from_model():
    print("auto-generated traces from tla file executed succesfully")


@itf("traces/example0.itf.json", keypath="last_msg.tag")
@itf("traces/example1.itf.json", keypath="last_msg.tag")
@itf("traces/example2.itf.json", keypath="last_msg.tag")
def test_use_generated_traces():
    print("itf traces executed succesfully")
