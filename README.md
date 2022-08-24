# Atomkraft: E2E testing for Cosmos blockchains

- [Atomkraft: E2E testing for Cosmos blockchains](#atomkraft-e2e-testing-for-cosmos-blockchains)
  - [Introduction](#introduction)
  - [Conceptual overview](#conceptual-overview)
    - [Atomkraft project](#atomkraft-project)

## Introduction

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

- Push-button automation of local testnet creation (fully customizable)
- Clean, fully customizable path from test case generation to its execution on the local testnet
- Automatic generation of massive test suites from compact TLA+ models possible
- Easy execution of test cases generated via other means (e.g. BDD, PBT) possible
- Anytime ready-to-integrate regression test suite in the form of a standard Pytest project
- Ready-to-execute standard test suites for important Cosmos SDK modules (coming soon!)
- Generation of reports and dashboards for presentation and analysis of testing results (coming soon!)

## Conceptual overview

In itself, Atomkraft is nothing more that a command-line application, which is as easy to obtain for your system as executing `pip install atomkraft`; please consult the detailed [Installation Instructions](INSTALLATION.md) if needed. At the top-level, Atomkraft provides you the commands illustrated in the diagram below.

![Atomkraft users](docs/images/atomkraft-users.svg)

### Atomkraft project

Every work with Atomkraft happens in the scope of an _Atomkraft project_; you create an Atomkraft project via `atomkraft init` command. The command will initialize a new project in a given directory, and install all necessary software for it; all fully automatically.

The good news is that an Atomkraft project is simultaneously a [Pytest](https://docs.pytest.org/) project! At any point in time you can execute `pytest` inside your Atomkraft project, and this command will rerun all tests you've created or executed with Atomkraft in the scope of this project. So, when you've executed `atomkraft init`, you've also started to create your regression test suite; congratulations!

More than that, an Atomkraft project is also a [Python Poetry](https://python-poetry.org) project: you can treat is just as a normal Python project, and add your custom Python tests there.

At the top level, an Atomkraft project contains the following:

- Folders that hold the corresponding artifacts:
  - `models` is meant to keep your TLA+ models, if you are willing to generate test cases from formal models;
  - `traces` contain abstract test cases, represented in the form of [ITF traces](https://apalache.informal.systems/docs/adr/015adr-trace.html) (ITF stands for _Informal Trace Format_, a JSON encoding of a sequence of test case steps);
  - `reactors` hold Python functions that interpret ITF traces, and map trace steps to concrete blockchain transactions;
  - in `tests` we collect all Pytest tests that you execute in the scope of this Atomkraft project;
  - finally, `reports` hold the test reports.
- Configuration files:
  - `atomkraft.toml` contains Atomkraft project configuration;
  - `chain.toml` contains the blockchain configuration parameters, such as the number of nodes or the number of validators;
  - `model.toml` contains the TLA+ model configuration parameters, used to run model checkers;
  - `pyproject.toml` contains the Poetry project configuration.

All of the above configuration files are filled with the default configuration, so you don't need to worry about them, if you don't want to. On the other hand, when needed, everything is fully customizable.
