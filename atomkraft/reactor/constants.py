ATOMKRAFT_INTERNAL_FOLDER = ".atomkraft"

# the file that contains internal configurations for atomkraft
ATOMKRAFT_INTERNAL_CONFIG = "config.toml"

# a key for the reactor path inside internal config
REACTOR_CONFIG_KEY = "reactor"

# a special value used to indicate that there is a @step-decorated function that matches all actions
# (because it has no arguments)
ALL_ENCOMPASSING_STEP = object()

# a variable created under generated `reactor.py` file which stores the value of the keypath
KEYPATH_VAR = "keypath"
