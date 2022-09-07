import pytest

from ..utils.project import ATOMKRAFT_INTERNAL_DIR, project_root
from . import CHAIN_CONFIG_FILE
from .testnet import Testnet


@pytest.fixture
def testnet():
    testnet = Testnet.load_toml(
        project_root() / CHAIN_CONFIG_FILE,
        data_dir=project_root() / ATOMKRAFT_INTERNAL_DIR,
        keep=True,
        overwrite=True,
    )

    yield testnet
