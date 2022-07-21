# the file that contains public chain configuration (in the generated project)
CHAIN_CONFIG = "chain.toml"

# the file that contains public atomkraft configuration
ATOMKRAFT_CONFIG = "atomkraft.toml"

# the file that contains internal configurations for atomkraft
ATOMKRAFT_INTERNAL_CONFIG = ".atomkraft/config.toml"

# a key for the reactor path inside internal config
REACTOR_CONFIG_KEY = "reactor"

# a special value used to indicate that there is a @step-decorated function that matches all actions
# (because it has no arguments)
ALL_ENCOMPASSING_STEP = object()
