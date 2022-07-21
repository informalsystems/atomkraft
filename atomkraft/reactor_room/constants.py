from atomkraft.utils.project import project_root
import os

# the file that contains public chain configuration (in the generated project)
CHAIN_CONFIG = os.path.join(project_root(), "chain.toml")

# the file that contains public atomkraft configuration
ATOMKRAFT_CONFIG = os.path.join(project_root(), "atomkraft.toml")

# the file that contains internal configurations for atomkraft
ATOMKRAFT_INTERNAL_CONFIG = os.path.join(project_root(), ".atomkraft", "config.toml")

# a key for the reactor path inside internal config
REACTOR_CONFIG_KEY = "reactor"

# a special value used to indicate that there is a @step-decorated function that matches all actions
# (because it has no arguments)
ALL_ENCOMPASSING_STEP = object()
