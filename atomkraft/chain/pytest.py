import pytest

from ..utils.project import project_root
from .testnet import Testnet


@pytest.fixture
def testnet():
    testnet = Testnet.load_toml(f"{project_root()}/chain.toml")

    yield testnet
