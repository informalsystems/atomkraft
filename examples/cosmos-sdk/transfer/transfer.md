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
It auto-installs Poetry if needed and activates a new virtual environment (by running `poetry shell`).
This environment contains all necessary dependencies.

<!--
```sh
$ poetry run atomkraft init transfer
...
```
 -->

```
atomkraft init transfer
cd transfer
poetry shell
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

<!--

```sh
$ cd transfer; pwd; curl -Lo models/transfer.tla https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/transfer.tla
...
$ cd transfer; cat models/transfer.tla
---- MODULE transfer ----
EXTENDS Apalache, Integers, FiniteSets

VARIABLES
    \* @type: Int -> Int;
    balances,
    \* @type: [tag: Str, value: [n_wallet: Int, sender: Int, receiver: Int, amount: Int]];
    action,
    \* @type: Int;
    step

WALLETS == 0..1

Init ==
    /\ balances = [wallet \in WALLETS |-> 100]
    /\ action = [tag |-> "Init", value |-> [n_wallet |-> Cardinality(WALLETS)]]
    /\ step = 0

Next ==
    \E sender \in WALLETS:
    \E receiver \in WALLETS:
    \E amount \in 0..balances[sender]:
        /\ sender /= receiver
        /\ balances' = [
            balances EXCEPT
            ![sender] = @ - amount,
            ![receiver] = @ + amount
            ]
        /\ action' = [tag |-> "Transfer", value |-> [sender |-> sender, receiver |-> receiver, amount |-> amount]]
    /\ step' = step + 1

View ==
    IF action.tag = "Transfer"
    THEN action.value
    ELSE [sender |-> -1, receiver |-> -1, amount |-> 0]

...

====
```
-->

```
curl -Lo models/transfer.tla https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/transfer.tla
```

## Generate test scenarios

Atomkraft can use different model checkers to generate test scenarios from the model.
Let us use [Apalache](https://apalache.informal.systems/) as our checker.
To get it, run

<!--
```sh
$ poetry run atomkraft model apalache get
...
```
-->

```
atomkraft model apalache get
```

Having obtained the checker, we can smaple test scenarios from the model.

<!--
```sh
$ cd transfer; atomkraft model sample --model-path models/transfer.tla --traces-dir traces --examples Ex
...
```
-->

```
atomkraft model sample --model-path models/transfer.tla --traces-dir traces --examples Ex
```

If you inspect the `transfer.tla` file, you will find that the predicate `Ex` was defined as `step > 3`.
This requires that sampled test scenarios contain more than 3 transactions.

Indeed, if you check the `traces` directory, you will find a set of `json` files in it.
Each file contains one test scenario satisfying the property that there are more than 3 transactions.

While Atomkraft can generate test scenarios from the model, it would also be able to work with test scenarios created some other way (e.g., by hand).
As a side note, for every `atomkraft` command, you can inspect all options by appending `--help`.
For instance, `atomkraft model sample --help`.)

## Generate reactors

In the previous step, we have generated test scenarios (also called _traces_).
However, we are still missing a link from those `json` scenarios to the actual execution on chain.
_Reactors_ provide this missing link.
With some traces at hand, we need to write reactors corresponding to them.
Atomkraft can help us generate stubs for such reactors.

In our `transfer.tla` model, the `action` variable had two tags - `Init`, `Transfer`.
We will generate a reactor stub by running

<!--
```sh
$ cd transfer; poetry run atomkraft reactor --actions "Init,Transfer" --variables "action"
...
```
-->

```
atomkraft reactor --actions "Init,Transfer" --variables "action"
```

Inspect the `reactors` directory now: it contains a generator stub named `reactor.py`.
For the moment, `reactor.py` is a stub, which will for every step of the test scenario simply print the information about the action.
We will see how to extend the stub in section [Expanding reactors](#expanding-reactors).

## Setting up chains

Our ultimate goal is to execute tests on a chain.
Now we set up the testnet to be used with Atomkraft.

If you were following along the instructions in [INSTALLATION.md](/INSTALLATION.md), you are already have `gaiad` installed.
Since `gaiad` is a default testnet in Atomkraft, there is nothing else to be done.

Working with other chains is possible too, by installing them and then invoking:

```
atomkraft chain config chain_id <name_of_the_chain>
atomkraft chain config binary <path-to-the-chain-binary>
atomkraft chain config prefix <prefix?>
```

## Executing tests

All three elements for running a test are now in place: a testnet, a test scenario, and a reactor.
Thus, we are ready to run some tests (though, trivial ones since the reactor is still only a stub).

<!--
```sh
$ cd transfer; poetry run atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
...
Successfully executed
...
```
-->

```
atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
```

The output of the command contains

```
Successfully executed trace traces/violation1.itf.json
```

Other than that, it only names the actions executed at each step.
We will now expand the reactor to execute on chain the transactions from the test scenario.

## Expanding reactors

Update `reactors/reactor.py` with the complete reactor code from [here](https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/reactor.py).

While explaining the reactor code is out of the scope of this tutorial, you can skim through it and notice that it describes transfering coins from one account to another by broadcasting messages to the chain.

<!--
```sh
$ cd transfer; curl -Lo reactors/reactor.py https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/reactor.py
...
```
-->

```
curl -Lo reactors/reactor.py https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/reactor.py
```

## Re-executing tests with complete reactors

Finally, we can run the complete test with the completed reactor.

<!--
```sh
$ cd transfer; poetry run atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
...
Successfully executed
...
```
-->

```
atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
```
