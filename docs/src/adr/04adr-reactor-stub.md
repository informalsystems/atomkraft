# ADR-04: Atomkraft reactor stub command

## Context
This ADR describes one component of Atomkraft, as decribed in [ADR-01](01adr-principles-architecture.md).

## Status
This is an early version of the ADR, meant for the first prototype.
Major changes to the scope are very likely.

## Reactor

Once the user has a trace (either written by hand, or obtained from the system model),  they need to write a *reactor*.
A reactor is a set of Python functions connecting the actions of the trace to executions of the code.

In this ADR we describe a command `atomkraft reactor ...` which creates a stub of the reactor, 
auto-generating all the boilerplate, and leaving it to the user to only fill in the application-specific parts.

## Task

The interface of the command looks like this: 
`atomkraft reactor <actions_list> <variables_list> [<reactor-stub-file>]`
where
 - `actions_list` is a list of actions for which to generate stubs
 - `variables-list` is a list of all relevant state variables (those that could appear in traces of interest)
 - `reactor_stub_file` is a path at which the reactor file should be created. 
 If omitted, a default path is used: `atomkraft/reactors/reactor.py`

## Implementation
 
 The `ReactorRoom` class implements the desired behavior.
 Its member function are:
  - `generate_reactor(actions_list, variables_list, stub_file_path=None)`: generates the stub
  - `check_reactor(trace, reactor=None)`: it checks if the `reactor` (default reactor if `None`) is compatible with the `trace`. A reactor is compatible with a trace if each action appearing in `trace` is matched with a function in `reactor`. (TODO: in order to know what is *an action in trace*, I need to get a `keypath` argument from `Execute` (or some place else))


 ### Config updates
 This command updates the value of the `reactor` field in the config file `.atomkraft.toml`.
  
The reason for updating the config file is to give users a way to silently refer to the most recent model and reactor files.


### Stub content

 The stub should include:

 
  - a stub for the state function
  ```python
    @pytest.fixture
    def state():
        pass

  ```

  - for each action `<act>` from `actions_list`, a stub for the step function connecting the abstract action to the code execution.

  ```python
    @step("<act>")
    def act_step(chain_testnet, state, var1, var2,..., vark):
        pass
  ```
  where `var1`, `var2`,...,`vark` are all the variables from the `variables_list` and `state` is the state provided by the function `state`.


  Finally, the stub should contain comments with guidance on how to use the stub 
  (the content of the docs).

  ## Future work
   - allowing to infer `actions_list` and `variables_list` from the model