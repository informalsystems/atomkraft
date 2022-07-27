import json
import os

import py
import pytest
from atomkraft.cli import app
from typer.testing import CliRunner


@pytest.fixture(scope="session")
def runner():
    return CliRunner()


@pytest.fixture(scope="session")
def init_project(tmpdir_factory, runner):
    with tmpdir_factory.mktemp("test_data").as_cwd():
        project_name = "atomkraft_project"
        result = runner.invoke(app, ["init", project_name])
        assert result.exit_code == 0
        yield py.path.local(os.getcwd()) / project_name


config_tests = [
    ("chain_id", "cosmoshub-4", "juno-1"),
    ("coin_type", 118, 529),
    ("config.node.app.api.enable", True, False),
]


@pytest.mark.parametrize("key, old_value, new_value", config_tests)
def test_chain_config(init_project, runner, key, old_value, new_value):
    with init_project.as_cwd():
        # test query
        result = runner.invoke(app, ["chain", "config", key])
        data = json.loads(result.stdout)
        assert result.exit_code == 0
        assert data[key] == old_value
        # test update
        result = runner.invoke(app, ["chain", "config", key, str(new_value)])
        result = runner.invoke(app, ["chain", "config", key])
        data = json.loads(result.stdout)
        assert result.exit_code == 0
        assert data[key] == new_value
