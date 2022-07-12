# ADR-02: Atomkraft trace executor

| authors         | revision | revision date |
| --------------- | -------: | ------------: |
| Ranadeep Biswas |        1 | July 11, 2022 |

## Status

Proposed

## Context

Atomkraft is a Cosmos-SDK E2E testing toolkit with batteries included.

1. A testing framework to write/create model-based tests effortlessly.
2. Communicate with model-checkers to send model specifications and receive generated traces.
3. Setting up a blockchain.
4. Executing/driving a test on the blockchain following the received traces.
5. Generate a report of successful/failed tests.

Trace executor is one of the top-level components of Atomkraft.
Given model specifications of Cosmos-SDK modules and _abstract_ test scenarios,
the _trace executor_ will be responsible for generating and executing multiple _interesting_ traces of the _abstract_ test scenarios as end-to-end tests.

When an E2E test succeeds, it should print a _report_ as output. When it fails, it should save the failed trace or generate a concrete test as a regression test.

_Trace executor_ should also be able to execute a test given a single pre-generated or failed trace.

As an architecture, I propose decomposing trace executor into a few sub-components.

- Testing framework: to write the test, test drivers, and pass appropriate parameters.
- Model executor: to communicate with model checkers and generate traces.
- Cosmos-SDK blockchain client: to communicate with blockchain to perform transactions and query to drive the tests.
- Cosmos-SDK blockchain testnet spinner: to set up blockchain(s) to perform the tests on them.

We choose Python as our implementation language for ease of prototyping and scriptability.

### Testing framework

[Pytest](https://docs.pytest.org) is one of the main testing frameworks for Python.
Since we are using Python, it only makes sense to adapt pytest as our base framework.
So we provide a [pytest plugin](https://github.com/informalsystems/modelator) which includes `@mbt`, `@itf`, `@step` decorators for easy test creation.

### Model executor

We choose in-house [Modelator](https://github.com/informalsystems/modelator) to do this task. It is already available as a Python library.
Therefore, we can directly import and use it where it is needed.

### Cosmos-SDK testnet

Frankly, there are many other solutions to spin a Cosmos-SDK testnet.
But we are not aware of any Python based library. We already have a prototype at cosmos.net repository.
Since the codebase remained small and reasonably simple, we decided to maintain it and make it a standard in the future.

### Cosmos-SDK client

We found Terra-Money has a [python Terra-SDK client](https://github.com/terra-money/terra.py).
But it only works with terra chains because of some hardcoded constants and checks.
However, we made it work with any Cosmos-SDK chain by 15 lines of modification.

## Decision

- Python as the implementation language
- Adapt pytest as testing framework
- Convenient `@mbt`, `@itf`, `@step` decorators
- Continue with cosmos.net as testnet spinner
- Continue with terra-SDK fork
  - Or, submit a PR to terra-SDK

## Consequences

- There may be some overhead when we add support for Go or Rust in the future.
- We need to maintain Cosmos.net and Cosmos.py.
