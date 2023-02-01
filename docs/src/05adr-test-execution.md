# ADR-05: Test execution

| authors          | revision | revision date  |
| ---------------- | --------:| --------------:|
| Andrey Kuprianov |        1 | July 18, 2022  |

The present ADR describes the external interfaces of the `Execute` component that deals with test execution, either from a given abstract trace, or from (a set of) traces generated from a TLA+ model.

`Execute` component is the main integration point between other component. It doesn't do much work on its own; most of it is delegated, or should be already done at previous stages. The essence of what its doing can be described in a simple sentence:
> Collect all pieces together, generate a test file, and call Pytest on it.

All test files from all invocations are collected in the `tests` folder. So, the user can at any point in time run `pytest`, and all tests will be reproduced.

**NB**: The current version provides only rudimentary reproducibility by preserving abstract traces. All other artifacts (chain configuration, reactor) are not preserved; so if a user modifies them, the tests may cease to become reproducible.

## Command line interface

Test execution CLI provides two main entry points:

- `test trace [--trace <trace-file>] [--reactor <reactor-file>]` allows to execute an abstract test trace against the chain. All additional parameters are optional; when omitted, the defaults will be used.
  - `--trace <trace-file>` allows to specify which test trace file to execute. 
  - `--reactor <reactor-file>` allows to provide explicitly the reactor to employ; when omitted, the reactor previously generated via `reactor` command will be used.
- `test model [--model <model-file>] [--config <config-file>] [--sample <sample-operator>]` allows to execute test traces generated from a TLA+ model. All additional parameters are optional; when omitted, the defaults will be used.
  - `--model <model-file>` allows to specify which TLA+ model to use.
  - `--config <config-file>` specifies the model configuration file.
  - `--sample <sample-operator>` gives the name of the sample operator describing the test traces.

**TODO**: add configuration capabilities, e.g.:
- `test set timeout <TIMEOUT>` allows to specify the timeout (in seconds) for execution of a single test.

## Programmatic dependencies

`Execute` component depends on all three upstream components:

From `Setup` component it needs three functions provided via an agreed upon entry point:
- `setup()` sets up the chain with the default configured parameters;
  - **TODO**: agree upon the way to provide initialization parameters (e.g. the set of users and their wallets)from the trace into the chain genesis.
- `get_client()` provides the configured `LCDClient` ready to be used with the chain;
- `teardown()` destroys the previously set up chain.

From `Model` component it needs two functions provided via an agreed upon entry point:
- `get_trace(trace = None)` retrieves the ITF trace, either the default one, or from the provided location;
- `get_model_trace(model = None, config = None, sample = None)` provides a trace from the model, using either default, or the provided parameters.

From `React` component it needs one function provided via an agreed upon entry point:
- `get_trace_reactor(trace, reactor = None)` takes the optional path to the reactor as argument, and returns the path to the reactor file if it matches the provided trace, or raises an exception if it doesn't. If `reactor` argument is omitted, the default reactor should be used.

In the current version, `Execute` doesn't provide any programmatic service to other components.

## Environment interaction

### File read

`Execute` doesn't read any files by itself, all read access is mediated programmatically via other components. A non-exhaustive list of possible read dependencies:
- `Setup`-mediated: chain configuration
- `React`-mediated: reactor file (either default or from provided location)
- `Model`-mediated: model, config & trace files (either default or from provided locations)

### File write

`Execute` writes into the following locations:
- `tests` folder: writes the generated Pytest-based test file, that links together the setup, the reactor, and the execution of the ITF trace

### Processes

`Execute` runs the following (non-exhaustive) list of processes, mediated by other components:
- `Setup`-mediated: blockchain binary
- `Model`-mediated: model checker (Apalache)

By itself, `Execute` runs `Pytest`, by supplying it the name of the generated test file. In the current version, the output of Pytest is passed unmodified to the user.