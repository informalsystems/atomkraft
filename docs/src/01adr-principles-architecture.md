# ADR-01: Atomkraft principles and architecture

| authors           | revision | revision date  |
| ----------------- | --------:| --------------:|
| Andrey Kuprianov  |        1 | July 14, 2022  |

This ADR describes Atomkraft general organizational principles, how it is supposed to be used by the users, which artifacts it produces, and how it is decomposed into main components. Concrete functionality of those components is delegated to subsequent ADRs.


![Atomkraft high-level architecture](atomkraft-high-level-arch.svg)

## Workflow with users

Initially we plan to target two main user categories: security auditors and cosmos developers. They both share the correctness concern for a particular codebase (a Cosmos project), but from slightly different perspectives:
- a security auditor has a limited time frame to look at the project, and wants to uncover as many bugs as possible in that period;
- a Cosmos developer wants to uncover as many bugs as possible e.g. before the next release (hence the auditor engagement), without diverging much from their main activity (feature development), but also wants to ensure that code correctness is maintained long-term after the release.

Below we outline one possible workflow between auditor, developer, and the Atomkraft tool, which provides a preview of possible tool usage.

1. Auditor comes to the new Cosmos project, represented by a blockchain binary (e.g. `gaiad`). They want to check that Atomkraft is able to interact with it, so they run `atomkraft init ...`, which:
   - creates new Atomkraft project with all necessary file structure
   - produces blockchain configuration and a Python script that sets up a testnet using the configuration. The user can customize the both the configuration and the script; it will be picked up at later stages.
   - spins the testnet, and performs basic blockchain checks;
2. Auditor can check that the updated configuration is still functional via `atomkraft chain ...`, which spins or shuts down the testnet.
3. Auditor examines the Cosmos project, and writes one or multiple TLA+ models, each exercising a particularly critical aspect of project functionality. Some basic checks can be performed on the model using `atomkraft model ...`
4. Auditor wants generate some example test scenarios, for which purpose they use `atomkraft trace ...`. 
5. Auditor wants to connect TLA+ models to the testnet that is set up in step 1. They run `atomkraft reactor ...`, which generates the reactor stub: the set of Python handlers that map abstract model actions to concrete blockchain transactions. As project expertise is required to implement the handlers correctly, auditor contacts developer for the help implementing the handlers correctly.
   - The reactor can be combined with the blockchain setup script stub, and some manual tests can be written utiilizing it. The reactor will be picked automatically at later stages.
6. Now auditor has all components to connect TLA+ models to the testnet. They execute `atomkraft run ...` to run a single test trace against the testnet, or `atomkraft mbt` to perform the complete MBT workflow, starting from a TLA+ model and a test assertion, down to executing the generated traces on the testnet. Auditor tweaks the model, its parameters, and experiments with different test assertions, trying to uncover possible bugs.
   - Test traces that are failing on the testnet, are stored together with all artifacts that were used to produce them, as well as with all information obtained from the blockchain, thus forming the regression test suite.
7. Auditor asks the tool to generate a report for the failed tests, using `atomkraft report ...`, and submits the report to the developer.
8. Developer fixes the bugs, and asks auditor to recheck the them. Auditor runs `atomkraft test ...`, which automatically reruns previously stored regression tests.
9. Developer is happy about the interaction, and asks the auditor to provide them the regression tests. Auditor sends them the regression test suite generated in step 6.


## General principles

### Pytest integration

We don't want to reinvent the wheel wrt. such things as test execution or reporting. Instead, we want to plug in Atomkraft into [Pytest](https://pytest.org/), an established testing framework.

### Clean and transparent project structure

We aim to provide a valuable service to our users, and not to hide everything behind the wall of obscurity. Thus we want to give user the possibility to fully understand at least how our artifacts are structured, and to intervene/customize this structure if necessary. To that end, upon setting up an Atomkraft project, we will have the top-level project structure containing the folders:
- `chain`
- `models`
- `traces`
- `reactors`
- `tests`
- `reports`

We want to exactly explain to our users what each high-level Atomkraft command does, so that it is clear to them how to interface with the tool if needed, either manually or automated.

### Independently reusable artifacts

We don't want to force our tool on developers, if they don't want it. We want to provide a CLI for users who are not comfortable programming in Python, or for those who prefer CLI tools to writing their own scripts. But at every stage of Atomkraft project evolution, we produce artifacts which a user can pick up and employ independently of Atomkraft. Those artifacts should be either in the form of human-readable data (e.g. test traces in JSON), or in the form of independently executable Python scripts (e.g. setup scripts,  or generated tests).

### Reproducibility

Whenever a test is executed on the testnet and fails, we want to store
 - all artifacts necessary to reproduce the failure (model, test assertion, and/or test trace, chain setup, reactor)
 - all information relevant to the failure upon test execution (transactions, logs, error messages)

Wrt. the failed tests, it should be possible:
 - to generate reports with different degree of verbosity;
 - to export test suites containing reproducible tests.

### Configuration flexibility with sensible defaults

In general, Atomkraft commands will depend on a lot of parameters. In order to simplify user's life, we want to use default parameters whenever possible:
 - use default testnet configuration, that needs to be modified only rarely. At the same time provide the possibility to tweak any parameter;
 - save preconditions for the subsequent Atomkraft commands upon execution of the former ones.
   - E.g., when a TLA+ model is configured using `atomkraft model <file>`, subsequent invocation of `atomkraft trace` should implicitly assume the model provided previously, but also provide the possibility to specify an alternative one using `--model <file>` option.
   - Similarly, `atomkraft reactor` should store the name of generated reactor in the configuration, and this name should be later picked up automatically by `atomkraft run`, but with the possibility for an alternative reactor via `--reactor` option.

## Everything below is WIP 

## Command-line interface

Below we specify only the outcomes for successful command execution. Upon unsuccessful command execution, the error should be reported to the user, and no remnants (e.g. zombie processes, or additional files beyond requested) should remain.


The tool CLI commands represent top-level user workflows, where each workflow is able to bring value to a user. Our primary user for the CLI is the auditor, who comes to a new Cosmos-SDK based project, and wants to test it in a limited amount of time.

Each CLI command produces a certain artifact (e.g. a blockchain configuration, or a Python reactor stub). Those intermediate artifacts can be customized, and then seamlessly integrated back in the workflows that depend on them.

An example workflow with customization points:

1. A user comes to the new blockchain. They want to check that Atomkraft is able to interact with it, so they run `atomkraft testnet ...`
   - The produced configuration and a Python script that sets up a blockchain using the configuration is independently runnable. The user can customize the script; it will be picked up at later stages.
2. The user writes a TLA+ spec, and wants to connect it to the blockchain they set up in step 1. They run `atomkraft reactor ...`; the reactor stub is generated.
   - The user customizes the stub, and fills the gaps. The stub, together with the previous script for blockchain setup is runnable independently, but are also picked up automatically at later stages.
3. The user wants to test the blockchain set up in step 1, using the model and the reactor developed in step 2. They run `atomkraft test ...`. They experiment with different test assertions.
   - For the test traces that they find interesting, or that are failing on the blockchain, the user tells the tool to store them as regression tests. The regression Python script is generated, which can be executed independently.
4. The user asks the tool to generate a report for the failed tests, using `atomkraft report ...`. The user sends the report to the developers.
   - The developers fix the bugs, and ask the user to recheck the regression test on them. The user runs `atomkraft regression ...`, which automatically reruns previously stored regression tests.
5. The blockchain developers are happy about the interaction, and ask the auditor to provide them the regression tests. The auditor sends them the Python regression test generated in step 4. 

From the scenario outlined above, we start with the very minimal set of commands that will constitute the Atomkraft prototype.


## Initialize the project

A user wants to start applying Atomkraft to a new Cosmos SDK based project defined by a specialized binary (such as `gaiad`), so that the command checks that it can interoperate with the provided binary, and sets up all necessary folder structure and files in it.

Upon successful command execution, it should be guaranteed that Atomkraft is able to interact with it; also possibly some set of basic tests should be executed against it. The proposed command format:

```
atomkraft init <binary> [<config>]
```

where: 
- `<binary>` is the (path to) blockchain binary;
- `<config>` is the (path to) TOML file with the genesis and node configuration.


## Generate test trace

A user has written a TLA+ model, and wants to generate some traces for test assertions from the model, so that they can understand the model behavior, and use some of the generated test traces later for executing on a testnet. 

Upon successful command execution, the generated test trace in the ITF format should be saved to disk. The proposed command format:

```
atomkraft trace <model> <model-config> <test-assertion> <path-to-trace>
```
where: 
- `<model>` is the (path to) TLA+ model;
- `<model-config>` is the (path to) TOML file with the model and model checker configuration;
- `<test-assertion>` is the name of the model operator describing the desired test trace.
- `<path-to-trace>` is the path where to store the generated trace.


## Generate reactor stub

A user has either a TLA+ model, or a test trace, and wants to write a reactor that transforms trace steps into transactions, so that they can be executed on a testnet. For that purpose, Atomkraft generates a reactor stub, which user only needs to fill with concrete actions.

Upon successful command execution, a Python file should be generated, which contains Python function stubs for all relevant model actions.

```
atomkraft reactor [<action-list>] [<model-or-trace>] <reactor-stub-file> 
```
where: 
- `<model-or-trace>` is the (path to) TLA+ model, or to ITF trace;
- `<reactor-stub-file>` is the (path to) Python reactor stub to be generated.



## Run a trace against the testnet

WIP name: **Thrust a trace**

```
atomkraft run <trace> 
```

## Test the blockchain

WIP name: **Blast the testnet**

```
atomkraft test <model> <test-assertion>
```


## Launch a testnet (nice-to-have)

A user wants to set up a Cosmos-SDK testnet, using a specific binary of their choice, so that the testnet can later be used either for exploration or testing.  

Upon successful command execution, the testnet should be in operational step, and keep running; the testnet mnemonic is returned to the user. The proposed command format:

```
atomkraft testnet <binary> <genesis-config> <node-config>
```

where: 
    
- `<binary>` is the name or path to a Cosmos-SDK based blockchain binary (e.g. `gaiad`);
- `<genesis-config>` is the (path to) TOML file with the genesis configuration;
- `<node-config>` is the (path to) TOML file with the node configuration.

It should be possible to terminate one or all of the previously launched testnets:
- `atomkraft terminate <mnemonic>` should terminate the testnet launched previously under `<mnemonic>`;
- `atomkraft terminate <binary>` should terminate all testnets launched previously using `<binary>`;
- `atomkraft terminate` should terminate all previously launched testnets.

## Explore a testnet (nice-to-have)

A user wants to explore the running testnet visually (e.g. validators or transactions), so that they see the transactions live as they are executed. 

Upon successful command execution, a browser window is opened with the blockchain explorer for the specified testnet. The proposed command format:

```
atomkraft explorer [<address>]
```

where `<address>` is the optional address for the blockchain explorer to connect to. If omitted, the explorer should connect to the testnet launched last.
