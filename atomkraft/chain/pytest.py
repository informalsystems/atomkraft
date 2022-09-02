import pytest

from ..utils.project import project_root
from .testnet import Testnet


@pytest.fixture
def testnet():
    testnet = Testnet.load_toml(
        project_root() / "chain.toml",
        data_dir=project_root() / ".atomkraft",
        keep=True,
        overwrite=True,
    )

    yield testnet
