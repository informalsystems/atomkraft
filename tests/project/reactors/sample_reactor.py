import logging

import pytest
from modelator.pytest.decorators import step

keypath = "last_msg.name"


@pytest.fixture
def state():
    return {}


@step()
def act_step(chain_testnet, state, a):
    logging.info("Step: act")
