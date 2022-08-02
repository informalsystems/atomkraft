# ADR-04: Atomkraft reactor stub command

## Context

This ADR describes one component of Atomkraft, as decribed in [ADR-01](01adr-principles-architecture.md).

## Status

This is an early version of the ADR, meant for the first prototype.
Major changes to the scope are very likely.

## Reactor Stub

Once the user has a trace (either written by hand, or obtained from the system model), they need to write a _reactor_.
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

The following three functions implement the desired functionality:

- `generate_reactor(actions_list, variables_list, keypath="action", stub_file_path=None) -> Path`:
  generates the stub, containing one `@step` function for each action from the `action_list`,
  and each of these functions takes variables from the `variables_list` as arguments,
  as well as the assignment to the `keypath` value.
  The reactor stub is created at `stub_file_path` name location
  (if it is `None`, a default location is used).
  The function returns the path to the generated reactor stub and updates the value of `reactor` under `atomkraft.toml`.

- `check_reactor(trace, reactor=None) -> bool`: it checks if the `reactor` (default reactor if `None`) is compatible with the `trace`. A reactor is compatible with a trace if each action appearing in `trace` (lookig under key defined by the variable `keypath` from `reactor`) is matched with a function in `reactor`. The function returns `True` if the check is successful, and `False` otherwise.

- `get_reactor() -> Path`: returns the path to the reactor from `atomkraft.toml`

### Stub content

The stub should include:

- an assignment defining what is the keypath for the steps, e.g.

```python
  keypath = 'action'
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
  def act_step(testnet, state, var1, var2,..., vark):
      print("Step: <act>")
```

where `var1`, `var2`,...,`vark` are all the variables from the `variables_list`
(and `state` is the state provided by the function `state`,
while `testnet` is a fixture generated when calling `atomkraft init`).

### Programmatic dependencies

Implicit dependency on `Init` to generate the `testnet` variable.

### Environment Interaction

This command updates the value of the `reactor` field in the config file `.atomkraft.toml`.
The reason for updating the config file is to give users a way to silently refer to the most recent model and reactor files.

## Future work

- allowing to infer `actions_list` and `variables_list` from the model
- the stub should contain comments with guidance on how to use the stub
  together with a pointer towards the tutorial on writing Reactors.
