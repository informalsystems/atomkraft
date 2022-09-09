# Atomkraft test project: token transfer

We will see the basic functionality of Atomkraft in testing a basic token-transfer application.
Note that Atomkraft is typically used for testing Cosmos-SDK modules,
but we are using a simple, restricted token-transfer example here.
This will allow us to cover key Atomkraft concepts without introducing additional complexity.
For examples of using Atomkraft on Cosmos-SDK modules, check the [atomkraft-cosmos](https://github.com/informalsystems/atomkraft-cosmos) repository.

This document will cover the following:

- how to initialize Atomkraft project
- how to use Atomkraft to automatically generate test scenarios from a model
- how to generate stubs of reactor files (which connect generated test scenarios with the software under test)

## Installation

Before starting, make sure to install Atomkraft and its dependencies, as described in [INSTALLATION.md](/INSTALLATION.md).

## Initialize project

`atomkraft init` creates a new directory and initializes a Poetry project in it.
It auto-installs Poetry if needed and create a new virtual environment (available via `poetry shell`).
This environment contains all necessary dependencies.

```
atomkraft init transfer
cd transfer
```

Let's inspect the structure of the generated `transfer` project.
Two directories deserve special attention: those are `models` and `reactors`.
In those two directories we will put files which specify what kind of tests we want to generate.

## Create a model specification

We will model a simple token transfer between two users.
Alice and Bob both start with 100 tokens.
At each step, Alice or Bob will send some amount of tokens to the other person.
We will use TLA+ to specify this model.
You can use the following code to _jump-start_ a new model at `models/transfer.tla`.
(For a gentle introduction to modelling with TLA+, see [this tutorial](https://mbt.informal.systems/docs/tla_basics_tutorials/))

```
curl -Lo models/transfer.tla https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/transfer.tla
```

## Generate test scenarios

Atomkraft can use different model checkers to generate test scenarios from the model.
Let us use [Apalache](https://apalache.informal.systems/) as our checker.
To get it, run

```
atomkraft model apalache get
```

### Simulation

Having obtained the checker, we can sample test scenarios from the model.
One way to do so is by simulating the evolution of the model.

By running the following command,
we instruct the model checker to simulate 4 (`max-trace`) potential evolutions of the
model up to length 3.

```
atomkraft model simulate --model-path models/transfer.tla --max-trace 4 --length 3 --traces-dir simulation_traces
```

Indeed, if you check the `simulation_traces` directory, you will find the `example<1-4>.itf.json` files in it, where each trace will consist of 3 steps.

### Test predicates

We can do more than a mere simulation:
Atomkraft can generate tests corresponding to the behavior we would like to see.
For instance, we can run:

```
atomkraft model sample --model-path models/transfer.tla --traces-dir traces --tests TestAliceZero
```

If you inspect the `transfer.tla` file, you will find that the predicate `TestAliceZero` was defined to mean that Alice is out of funds.
Atomkraft has generated exactly such a scenario: `traces/TestAliceZero` directory contains the `violation1.itf.json` file in it.
This file contains a test scenario satisfying the desired property.

While Atomkraft can generate test scenarios from the model, it would also be able to work with test scenarios created some other way (e.g., by hand).
Furthermore, Atomkraft can generate not only one, but an arbitrary number of scenarios satisfying a desired property.
(As a side note, for every `atomkraft` command, you can inspect all options by appending `--help`.
For instance, `atomkraft model sample --help`.)

## Generate reactors

In the previous step, we have generated test scenarios (also called _traces_).
However, we are still missing a link from those `json` scenarios to the actual execution on chain.
_Reactors_ provide this missing link.
With some traces at hand, we need to write reactors corresponding to them.
Atomkraft can help us generate stubs for such reactors.

In our `transfer.tla` model, the `action` variable had two tags - `Init`, `Transfer`.
We will generate a reactor stub by running

```
atomkraft reactor --actions "Init,Transfer" --variables "action"
```

Inspect the `reactors` directory now: it contains a generator stub named `reactor.py`.
For the moment, `reactor.py` is a stub, which will for every step of the test scenario simply print the information about the action.
We will see how to extend the stub in section [Expanding reactors](#expanding-reactors).

## Setting up chains

Our ultimate goal is to execute tests on a chain.
Now we set up the testnet to be used with Atomkraft.

If you were following along the instructions in [INSTALLATION.md](/INSTALLATION.md#blockchain-binary), you already have `simd` compiled (or installed to system).
`simd` is the default testnet in Atomkraft.

If you have `simd` in your system path, there is nothing else to be done.
Otherwise, you only need to set the chain binary path invoking:

```
atomkraft chain config binary <path-to-the-chain-binary>
```

Working with other chains is possible too, by installing them and then invoking:

```
atomkraft chain config chain_id <name_of_the_chain>
atomkraft chain config binary <path-to-the-chain-binary>
atomkraft chain config prefix <prefix?>
```

## Executing tests

All three elements for running a test are now in place: a testnet, a test scenario, and a reactor.
Thus, we are ready to run some tests (though, trivial ones since the reactor is still only a stub).

```
atomkraft test trace --path traces/TestALiceZero/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
```

The output of the command contains

```
Successfully executed trace traces/TestAliceZero/violation1.itf.json
```

Other than that, it only names the actions executed at each step.
We will now expand the reactor to execute on chain the transactions from the test scenario.

## Expanding reactors

Update `reactors/reactor.py` with the complete reactor code from [here](https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/reactor.py).

While explaining the reactor code is out of the scope of this tutorial, you can skim through it and notice that it describes transfering coins from one account to another by broadcasting messages to the chain.

```
curl -Lo reactors/reactor.py https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/reactor.py
```

## Re-executing tests with complete reactors

Finally, we can run the complete test with the completed reactor.

```
atomkraft test trace --path traces/TestAliceZero/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
```
