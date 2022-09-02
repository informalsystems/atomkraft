import pytest

from ..utils.project import project_root
from . import CHAIN_CONFIG_FILE
from .testnet import Testnet


@pytest.fixture
def testnet():
    testnet = Testnet.load_toml(
        project_root() / CHAIN_CONFIG_FILE,
        data_dir=project_root() / ".atomkraft",
        keep=True,
        overwrite=True,
    )

    yield testnet
