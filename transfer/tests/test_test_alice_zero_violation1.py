import logging

from modelator.pytest.decorators import itf

pytest_plugins = "reactors.reactor"


@itf("traces/TestAliceZero/violation1.itf.json", keypath="action.tag")
def test_test_alice_zero_violation1():
    logging.info("Successfully executed trace " + "traces/TestAliceZero/violation1.itf.json")
