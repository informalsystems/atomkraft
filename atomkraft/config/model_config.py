import os
from typing import Optional
from atomkraft.config.config_file import ConfigFile
from atomkraft.utils.project import project_root

MODEL_CONFIG_PATH = "model.toml"


class ModelConfig(ConfigFile):
    def __init__(self, path: Optional[str] = None):
        if not path:
            if "PYTEST_CURRENT_TEST" in os.environ:
                root = "tests/project"
            else:
                root = project_root()
            self.path = os.path.join(root, MODEL_CONFIG_PATH)
        super(path)
