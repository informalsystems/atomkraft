# ADR-04: Atomkraft reactor stub command

## Context
This ADR describes one component of Atomkraft, as decribed in [ADR-01](01adr-principles-architecture.md).

## Status
This is an early version of the ADR, meant for the first prototype.
Major changes to the scope are very likely.

## Reactor Stub

Once the user has a trace (either written by hand, or obtained from the system model),  they need to write a *reactor*.
A reactor is a set of Python functions connecting the actions of the trace to executions of the code.

In this ADR we describe a command `atomkraft reactor ...` which creates a stub of the reactor,
auto-generating all the boilerplate, and leaving it to the user to only fill in the application-specific parts.

## Command Line Interface

The interface of the command looks like this:
`atomkraft reactor <actions_list> <variables_list> [<reactor-stub-file>]`
where
 - `actions_list` is a list of actions for which to generate stubs
 - `variables_list` is a list of all relevant state variables (those that could appear in traces of interest)
 - `reactor_stub_file` is a path at which the reactor file should be created.
 If omitted, a default path is used: `atomkraft/reactors/reactor.py`

## Implementation

 The `Reactor` class implements the desired behavior.
 Its member functions are:
  - `generate_reactor(actions_list, variables_list, stub_file_path=None) -> Path`:
  generates the stub, containing one `@step` function for each action from the `action_list`,
  and each of these functions takes variables from the `variables_list` as arguments.
  The reactor stub is created at `stub_file_path` name location
  (if it is `None`, a default location is used).
  The function returns the path to the generated reactor stub and updates the value of `reactor` under `atomkraft.toml`.

  - `check_reactor(trace, keypath="action", reactor=None) -> bool`: it checks if the `reactor` (default reactor if `None`) is compatible with the `trace`. A reactor is compatible with a trace if each action appearing in `trace` is matched with a function in `reactor`. The `keypath` argument defines which field of the ITF trace contains the action (if omitted, it takes the default value "action"). The function returns `True` if the check is successful, and `False` otherwise.

  - `get_reactor() -> Path`: returns the path to the reactor from `atomkraft.toml`


### Stub content

 The stub should include:


  - a stub for the `chain_testnet` initialization function
  ```python
  @pytest.fixture(scope="session")
  def chain_testnet(num_validators=3, num_accounts=3, account_balance=1000, validator_balance=100):
    chain_id = "test-cw" # read from chain config
    binary = "binary" # read from chain config
    denom = "stake" # read from chain config
    prefix = "juno" # read from chain config
    coin_type = 118 # read from chain config

    genesis_config = {
        "app_state.gov.voting_params.voting_period": "600s",
        "app_state.mint.minter.inflation": "0.300000000000000000",
    }

    node_config = {
        "config/app.toml": {
            "api.enable": True,
            "api.swagger": True,
            "api.enabled-unsafe-cors": True,
            "minimum-gas-prices": f"0.10{denom}",
            "rosetta.enable": False,
        },
        "config/config.toml": {
            "instrumentation.prometheus": False,
            "p2p.addr_book_strict": False,
            "p2p.allow_duplicate_ip": True,
        },
    }

    testnet = Testnet(
        chain_id,
        n_validator=num_validators,
        n_account=num_accounts,
        binary=binary,
        denom=denom,
        prefix=prefix,
        coin_type=coin_type,
        genesis_config=genesis_config,
        node_config=node_config,
        account_balance=account_balance
        validator_balance=validator_balance,
    )

    testnet.oneshot()
    time.sleep(10)
    yield testnet
    time.sleep(2)
  ```

  - a stub for the state function. The `state` is meant to serve any additional state that the user wants to maintain besides the blockchain state.

  ```python
    @pytest.fixture
    def state():
        return {}
  ```

  - for each action `<act>` from `actions_list`, a stub for the step function connecting the abstract action to the code execution.

  ```python
    @step("<act>")
    def act_step(chain_testnet, state, var1, var2,..., vark):
        print("Step: <act>")
  ```
  where `var1`, `var2`,...,`vark` are all the variables from the `variables_list`
  (and `state` is the state provided by the function `state`,
  while `chain_testnet` is provided by the function `chain_testnet`).


### Programmatic dependencies
Implicit dependency on `Init` to generate the `chain_testnet` variable.

 ### Environment Interaction
This command updates the value of the `reactor` field in the config file `.atomkraft.toml`.
The reason for updating the config file is to give users a way to silently refer to the most recent model and reactor files.


  ## Future work
   - allowing to infer `actions_list` and `variables_list` from the model
   - the stub should contain comments with guidance on how to use the stub
  together with a pointer towards the tutorial on writing Reactors.
