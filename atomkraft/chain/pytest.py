import time

import pytest
from atomkraft.utils.project import project_root

from .testnet import Testnet


@pytest.fixture
def testnet():
    testnet = Testnet.load_toml(f"{project_root()}/chain.toml")

    testnet.oneshot()
    time.sleep(10)
    yield testnet
    time.sleep(2)
