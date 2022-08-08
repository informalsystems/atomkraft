import os
from typing import Optional

from atomkraft.config.config_file import ConfigFile
from atomkraft.utils.project import project_root

ATOMKRAFT_INTERNAL_DIR = ".atomkraft"

# the file that contains internal configurations for atomkraft
ATOMKRAFT_INTERNAL_CONFIG = "config.toml"


class AtomkraftConfig(ConfigFile):
    def __init__(self, path: Optional[str] = None):
        if not path:
            if "PROJECT_ROOT" in os.environ:
                root = os.environ["PROJECT_ROOT"]
            else:
                root = project_root()
            path = os.path.join(
                root,
                ATOMKRAFT_INTERNAL_DIR,
                ATOMKRAFT_INTERNAL_CONFIG,
            )
        super().__init__(path)
