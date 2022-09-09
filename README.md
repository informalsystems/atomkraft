# Atomkraft: E2E testing for Cosmos blockchains

Below we describe what Atomkraft is about, and explain the concepts behind the tool. In case you would like to skip that, and jump directly into action, please read our [Installation guide](./INSTALLATION.md) to install the tool; afterwards it's worth following either our [Cosmos SDK Token Transfer tutorial](examples/cosmos-sdk/transfer/transfer.md), or [CosmWasm tutorial](examples/cosmwasm/counter/README.md).

We cover the following topics in this file:

- [Atomkraft Introduction](#atomkraft-introduction)
- [Conceptual overview](#conceptual-overview)
  - [Atomkraft project](#atomkraft-project)
  - [Local testnets](#local-testnets)
  - [Traces and reactors](#traces-and-reactors)
  - [Generating traces from TLA+ models](#generating-traces-from-tla-models)
  - [Running the tests against testnet](#running-the-tests-against-testnet)
- [What's next: Atomkraft's immediate future](#whats-next-atomkrafts-immediate-future)
- [Introductory video](#introductory-video)

## Atomkraft Introduction

The [Cosmos Network](https://cosmos.network) of [IBC](https://ibcprotocol.org)-connected blockchains is growing tremendously fast. There is one aspect though, which has not been fully addressed yet, namely **quality assurance**: how do we make sure that Cosmos-based blockchains are secure, and don't contain security issues that pose hazards for user funds?

**Atomkraft** is our answer to that question: it allows to generate and execute massive end-to-end (E2E) test suites for Cosmos SDK based blockchains. When designing the tool, we keep two main categories of users for it: **security auditors**, and **Cosmos SDK blockchain developers**. Those roles are abstract and non-exclusive, and they serve only to summarize some important concerns wrt. the deployed blockchains. Is Atomkraft the right tool for you? Below are some possible hints.

Atomkraft is likely to benefit you as a _Security auditor_ if:

- your blockchain (or the new version of it) is about to be launched, but you are unsure whether incentivized testnets allowed you to discover all critical vulnerabilities;
- you are on tight time schedule for the new release, and you feel that the implementation has been rushed a little, so you are unsure that all corner cases of the new functionality has been covered.

Atomkraft is likely to benefit you as a _Cosmos SDK developer_ if:

- the new functionality you've implemented interacts in non-trivial ways with other important modules (e.g. with [bank](https://docs.cosmos.network/master/modules/bank/), [staking](https://docs.cosmos.network/master/modules/staking/), [authz](https://docs.cosmos.network/master/modules/authz/), etc.), and you are unsure whether some important invariants of those modules are preserved;
- you want to grow and maintain a regression test suite for the blockchain modules you are developing, to make sure of their correctness as your blockchain evolves;
- you want to automate quality assurance for your blockchain modules, and integrate fast E2E testing solution that's executed on every PR.

**Key Atomkraft features** that allow to address the above concerns:

- Push-button, but fully customizable, automation of local testnet creation
- Clean, fully customizable trajectory from test case generation to its execution on the local testnet
- Support for automatic generation of massive test suites from compact TLA+ models
- Easy execution of test cases generated via other means (e.g. manual, BDD, PBT)
- Anytime ready-to-integrate regression test suite in the form of a standard Pytest project
- Ready-to-execute standard test suites for important Cosmos SDK modules (coming soon!)
- Generation of reports and dashboards for presentation and analysis of testing results (coming soon!)

## Conceptual overview

In itself, Atomkraft is nothing more than a command-line application, which is as easy to obtain for your system as executing `pip install atomkraft`; please consult the detailed [Installation Instructions](INSTALLATION.md) if needed. At the top-level, Atomkraft provides you the commands illustrated in the diagram below.

![Atomkraft users](docs/images/atomkraft-users.svg)

### Atomkraft project

Working with Atomkraft takes place in the scope of an _Atomkraft project_, which is initialized via `atomkraft init` command. The command will setup a new project in a given directory and install all necessary software for it, all fully automatically.

The good news is that an Atomkraft project is simultaneously a [Pytest](https://docs.pytest.org/) project! At any point in time you can execute `pytest` inside your Atomkraft project, and this command will rerun all tests you've created in the scope of this project. So, when you've executed `atomkraft init`, you've also started to create your regression test suite; congratulations!

More than that, an Atomkraft project is also a [Python Poetry](https://python-poetry.org) project: you can treat it just as a normal Python project, and add your custom Python tests there.

At the top level, an Atomkraft project contains the following:

- Folders that hold the corresponding artifacts:
  - `models` is meant to keep your TLA+ models, if you are willing to generate test cases from formal models;
  - `traces` contain abstract test cases, represented in the form of [ITF traces](https://apalache.informal.systems/docs/adr/015adr-trace.html) (a JSON encoding of a sequence of test case steps);
  - `reactors` hold Python functions that interpret ITF traces, and map trace steps to concrete blockchain transactions;
  - in `tests` we collect all reproducible Pytest tests that are executed in the scope of this Atomkraft project;
  - finally, `reports` hold the test reports.
- Configuration files:
  - `atomkraft.toml` contains Atomkraft project configuration;
  - `chain.toml` contains the blockchain configuration parameters, such as the number of nodes or the number of validators;
  - `model.toml` contains the TLA+ model configuration parameters, used to run model checkers;
  - `pyproject.toml` contains the Poetry project configuration.

All of the above configuration files are filled with the default configuration, so you don't need to worry about them, if you don't want to. On the other hand, when needed, everything is fully customizable.

### Local testnets

With Atomkraft project created, you should be ready to go. By default, we configure local testnets to use the `gaiad` (Cosmos Hub) binary. If it is available via your `PATH`, executing `atomkraft chain testnet` should bring up a local testnet with 2 nodes and 3 validators. If you would like to configure any parameters differently (e.g. to run your custom blockchain binary), you can do it either via `atomkraft chain config` command, or by directly editing `chain.toml` config file. Please make sure your changes are valid by executing `atomkraft chain testnet`; we use the local testnet to run the tests.

### Traces and reactors

For describing test cases we use the [_Informal Trace Format_](https://apalache.informal.systems/docs/adr/015adr-trace.html), which is a JSON encoding of a sequence of steps, and each step encodes values of key state variables; please see [this example trace](examples/cosmos-sdk/transfer/example_trace.itf.json). The trace has been produced by our in-house [Apalache model checker](https://apalache.informal.systems) from [this TLA+ model](examples/cosmos-sdk/transfer/transfer.tla).

ITF traces are abstract; in the example trace above, it holds wallet balances as a simple mapping `balances` from abstract addresses, represented as integers, to their balances, also represented as integers without denomination. There are two abstract actions in this trace: `Init`, and `Transfer`. In order to be able to replay the abstract trace on a blockchain, each of those abstract actions needs to be translated to a concrete transaction, as well as all abstract parameters of an action need to be translated to concrete values (e.g. an abstract integer address needs to be translated into a concrete Cosmos address). This translation step is performed by a component that we call `reactor`: a reactor is a centerpiece for an Atomkraft project, without which it can't function, similar to a nuclear reactor for the atomic power plant. You can see [this example reactor](examples/cosmos-sdk/transfer/reactor.py) that is able to playback the above trace on the blockchain.

This separation between abstract traces and reactors, which apply abstract traces to concrete blockchains, is the crucial aspect of Atomkraft infrastructure; here is why:

- Abstract traces are more maintainable than concrete tests. Concrete tests need to be updated on every small change in encoding, API, etc.; we have seen PRs with thousands of LOC concerning only with updating manually written tests. With the separation into traces and reactors, traces won't need to be updated in most cases; only the relatively small reactors will need small tweaks.
- Abstract traces can be generated by whatever means: from model checkers such as [Apalache](https://apalache.informal.systems), via fuzzing, PBT, BDD, or even manually. How the abstract trace is produced, doesn't matter; it still can be executed using Atomkraft's infrastructure.
- It is much easier to understand the intent of a test case expressed as an abstract trace, because of absence of excessive details.
- Abstract traces are lightweight in terms of storage, which allows us to generate and maintain thousands of them, covering many corner cases, at no extra cost.

We have automated the process of writing a reactor via `atomkraft reactor` command. A user needs only to supply the lists of actions, and of state variables, and the command will generate a reactor stub with a function for each action; what remains is only to fill the body of each such function.

### Generating traces from TLA+ models

As explained above, abstract traces can be obtained by whatever means; we do not constrain the user in this respect. The most time efficient method, from our point of view, is to generate traces from formal models expressed in [TLA+](https://lamport.azurewebsites.net/tla/tla.html), the specification language designed by Leslie Lamport. For a gentle introduction to TLA+ you may use the Informal's [TLA+ Language Reference Manual](https://apalache.informal.systems/docs/lang/index.html) and [TLA+ Basics Tutorial](https://mbt.informal.systems/docs/tla_basics_tutorials/). While TLA+ may look scary for beginners, we can assure you that learning it will greatly improve your productivity when reasoning about (and testing!) both protocols and code.

The good news is that we have done a thorough work in making user's life as easy as possible when working with TLA+ models, and using them to generate abstract test traces. All heavy-lifting work wrt. TLA+ models is done by our [Apalache](https://apalache.informal.systems) model checker. The model checker itself is meant for expert users; Atomkraft tries its best to hide excessive complexity from its users and exposes only the most essential functionality for working with models. You can access this functionality via `atomkraft model` command, which provides you with the functions like listed in the screenshot below:

![Atomkraft model](docs/images/atomkraft-model.png)

The most important command in the scope of test case generation is `atomkraft model sample`. E.g. the command below (assuming you are in the Atomkraft project)

```sh
atomkraft model sample --model-path models/transfer.tla --traces-dir traces --tests Ex
```

will generate an abstract trace from the [transfer.tla](examples/cosmos-sdk/transfer/transfer.tla) model and the test predicate `Ex`, and store the generated trace in the `traces` directory of your Atomkraft project.

### Running the tests against testnet

Let's assume you've done all the steps outlined above:

1. created a fresh Atomkraft project using `atomkraft init`
2. configured a Cosmos-based blockchain of your choice using `atomkraft chain`
3. created a reactor stub using `atomkraft reactor`, and populated it with code
4. generated abstract traces from a TLA+ model using `atomkraft model sample`, or created abstract traces by some other means

Then you are ready to go, and execute your tests! We provide two commands for doing that:

- `atomkraft test trace` will accept an abstract trace and a reactor, spin the local testnet, and execute the trace against the testnet
- `atomkraft test model` is a convenience shorthand that combines step 4 above (`atomkraft model sample`) with `atomkraft test trace`, and allows you to execute tests directly from a TLA+ model, sidestepping explicit trace generation.

Both of the above `atomkraft test` commands populate the `tests` directory of your project with Pytest-based tests; so executing `pytest` inside your Atomkraft project at any point in time will reproduce all of your tests. In fact, the complete Atomkraft project directory is ready at any point in time to be exported, and used as a Pytest project, for example for reproducing your tests in the CI.

## What's next: Atomkraft's immediate future

Atomkraft's functionality outlined above represents the tool MVP: please feel free to employ it in your projects, and let us know of your experience: we are always ready to assist!

There are many more features that are planned or are already being implemented; so stay tuned. Below is the preview of the future Atomkraft functionality:

- **Standard test suites**: we have already started the effort to provide standard reactors and tests for most important Cosmos SDK modules: [bank](https://docs.cosmos.network/master/modules/bank/), [staking](https://docs.cosmos.network/master/modules/staking/), [authz](https://docs.cosmos.network/master/modules/authz/); you name it! This will serve the community at large, and will allow you, as an Atomkraft user, to easily bootstrap your new Atomkraft projects:
  - running standard test suites in your CI will make sure that your new functionality doesn't break the important blockchain invariants;
  - using standard test suites as blueprints will allow you to easily create your own tests suites via examination and adaptation of already existing tests.
- **Test understanding and debugging**: we started to work in the direction of assisting the user in simplified creation and understanding of the test scenarios, as well as debugging the failed test runs:
  - for the former, we will provide the differential trace viewer, which highlights only the changes between the trace steps;
  - for the latter, we will provide the built-in blockchain explorer, and integrate into it the capabilities to trace back and forth between abstract trace steps and concrete blockchain transactions.
- **Test reports and dashboards**: we plan to implement the functionality for generation of test reports as well as live dashboards that would provide an easy-to-grasp overview and categorization of executed and running tests.
- **Exhaustiveness**: we plan to implement certain coverage metrics (e.g. transaction sequences up to specified length), and to help user achieving full coverage according to those metrics to provide confidence in the code in case no bugs are discovered.

## Introductory video

We have recorded a short video illustrating the basic Atomkraft usage:

[![Atomkraft Introduction](https://img.youtube.com/vi/EBPypESyzqo/0.jpg)](https://www.youtube.com/watch?v=EBPypESyzqo)
