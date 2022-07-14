# ADR-04: Atomkraft reactor stub command

## Context
This ADR describes one component of the command-line tool of Atomkraft.
The goal of the command-line tool `atomkraft` is to make it easy for users to setup their Atomkraft projects
and run basic commands.

## Scope
This is an early version of the ADR, meant for the first prototype.
Major changes to the scope are very likely.

## Reactor

Once the user has a TLA+ model (either written by hand, or one provided by Atomkraft), they need to write a *reactor*: 
a set of Python functions connecting the actions of the model to executions of the code.

In this ADR we describe a command `atomkraft reactor ...` which creates a stub of the reactor, 
auto-generating all the boilerplate, and leaving it to the user to only fill in application-specific parts.

## Task

The interface of the command looks like this: 
`atomkraft reactor <action-list> <model>.tla [<reactor-stub-file>]`
where
 - `action-list` is a list of actions for which to generate stubs
 - `model` is the TLA model for which we are implementing a reactor
 - `reactor-stub-file` is a path at which the reactor file should be created. 
 If omitted, a default path is used: `atomkraft/reactors/<model>_reactor.py`

 ### Config updates
 This command updates the content of the config file `.atomkraft.toml`.
 In particular, if updates:
  - the value of the `model` field
  - the value of the `reactor` field

The reason for updating the config file is to give users a way to silently refer to the most recent model and reactor files.


### Stub content
The code assumes the access to the `config` dictionary, which has access to everything written in the `.atomkraft` file.
Furthermore, it assumes imported `Testnet` from `cosmos_net.pytest`.

 The stub should include:

 - a stub for the testnet initialization function, based on the value of the `binary` that was put into `.atomkraft` by the command `atomkraft init`.
 
  ```python
@pytest.fixture(scope="session")
def chain_testnet():
    chain_id = "test-cw"
    binary = config["binary"] # as setup in the init command
    denom = "stake"
    prefix = "juno" #TODO: clarify
    coin_type = 118 # TODO: clarify

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
        n_validator=3,
        n_account=3,
        binary=binary,
        denom=denom,
        prefix=prefix,
        coin_type=coin_type,
        genesis_config=genesis_config,
        node_config=node_config,
        account_balance=10**26,
        validator_balance=10**16,
    )

    testnet.oneshot()
    time.sleep(10)
    yield testnet
    time.sleep(2)
 ```
 
  - a stub for the state function
  ```python
    @pytest.fixture
    def state():
        pass

  ```

  - for each action `act` from `action-list`, a stub for the step function connecting the abstract action to the code execution.

  ```python
    @step("act")
    def act_step(chain_testnet, state, var1, var2,..., vark):
        pass
  ```
  where `var1`, `var2`,...,`vark` are all the variables of the model, `state` is the state provided by the function `state`, and `chain_testnet` is the blockchain client provided by the function `chain_testnet`


  Finally, the stub should contain comments with guidance on how to use the stub 
  (the content of the docs).

  ## Future work
   - removing the need to specify the action list and instead inferring it from `model`