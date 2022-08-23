# Atomkraft test project: token transfer

We will see the basic functionality of Atomkraft on testing a basic token-transfer application.
Note that Atomkraft is typically used for testing Cosmos-SDK modules,
and we are using a simple, restricted token-transfer example here to illustrate Atomkraft concepts
without introducing additional complexity.
For examples on using Atomkraft on Cosmos-SDK modules, check the [atomkraft-cosmos](https://github.com/informalsystems/atomkraft-cosmos) repository.


This document will cover the following:

- how to initialize Atomkraft project
- how to use Atomkraft to automatically generate test scenarios from a model
- how to generate stubs of reactor files (which connect generated test scenarios with the software under test)


## Installation
Before starting, make sure to install Atomkraft and its dependencies, as decribed in [INSTALLATION.md](/INSTALLATION.md).



## Initialize project

`atomkraft init` creates a new directory and initializes a Poetry project in it.
It auto-installs Poetry if needed and activates a new virtual environment (by running `poetry shell`).
This environment contains all necessary dependencies.

<!--
```sh
$ atomkraft init transfer
...
$ cd transfer
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

<!-- $MDX dir=transfer
```sh
$ curl -Lo models/transfer.tla https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/transfer.tla
...
$ cat models/transfer.tla
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

<!-- $MDX dir=transfer
```sh
$ atomkraft model apalache get
...
```
-->

```
atomkraft model apalache get
```

Having obtained the checker, we can smaple test scenarios from the model.


<!-- $MDX dir=transfer
```sh
$ atomkraft model sample --model-path models/transfer.tla --examples Ex
...
```
-->

```
atomkraft model sample --model-path models/transfer.tla --examples Ex
```

If you inspect the `transfer.tla` file, you will find that the predicate `Ex` was defined as `step > 3`.
This requires that sampled test scenarios contain more than 3 transactions.

Indeed, if you check the `traces` directory, you will find a set of `json` files in it.
Each file contains one test scenario satisfying the property that there are more than 3 transactions.

While Atomkraft can generate test scenarios from the model, it would also be able to work with test scenarios created some other way (e.g., by hand).
As a side note, for every `atomkraft` command, you can inspect all options by appending `--help`. 
For instance, `atomkraft model sample --help`.)


## Generate reactors

In the previous step, we have generated test scenarios.
However, we are still missing a link from those `json` scenarios to the actual execution on chain.
*Reactors* provide this missing link.
Once we have some traces, we can generate reactor stubs for the traces
and Atomkraft can help us generaing stubs for reactors.

In our `transfer.tla` model, the `action` variable had two tags - `Init`, `Transfer`.
We will generate a reactor stub by running

<!-- $MDX dir=transfer 
```sh
$ atomkraft reactor --actions "Init,Transfer" --variables "action"
```
-->
```
atomkraft reactor --actions "Init,Transfer" --variables "action"
```

Inspect the `reactors` directory now: it contains a generator stub named `reactor.md`. 

### Setting up chains

Once we have the stub ready, we can set up the chain binary for the testnet.

We will use vanilla `cosmos-sdk` chain. Any other Cosmos-SDK derived chain should work too.

#### Chain binary compilation

<!-- $MDX dir=transfer -->
```sh
$ git clone --depth 1 --branch v0.45.7 https://github.com/cosmos/cosmos-sdk
...
$ (cd cosmos-sdk; make build)
...
```

The binary will be at `./cosmos-sdk/build/simd`

### Chain parameters

Now we can update the chain parameters.

<!-- $MDX dir=transfer -->
```sh
$ atomkraft chain config chain_id test-sdk
$ atomkraft chain config binary ./cosmos-sdk/build/simd
$ atomkraft chain config prefix cosmos
```

### Executing tests

We have some traces and a reactor stub ready. Now we can smoke-test the test.

<!-- $MDX dir=transfer -->
```sh
$ poetry run atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
...
Successfully executed trace traces/violation1.itf.json
...
```

For now, this just prints the name of the action tag. Let's complete the reactor stub.

### Updating reactors

Update `reactors/reactor.py` with the following complete reactor code.

<!-- $MDX dir=transfer -->
```sh
$ curl -Lo reactors/reactor.py https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/reactor.py
...
$ cat reactors/reactor.py
import time

from modelator.pytest.decorators import step
from terra_sdk.client.lcd import LCDClient
from terra_sdk.client.lcd.api.tx import CreateTxOptions
from terra_sdk.core import Coin, Coins
from terra_sdk.core.bank import MsgSend
from terra_sdk.core.fee import Fee
from terra_sdk.key.mnemonic import MnemonicKey


@step("Init")
def init(testnet, action):
    print("Step: Init")
    testnet.n_account = action["value"]["n_wallet"]
    testnet.verbose = True

    testnet.oneshot()
    time.sleep(10)


@step("Transfer")
def transfer(testnet, action):
    print("Step: Transfer")

    rest_endpoint = testnet.get_validator_port(0, "lcd")
    lcdclient = LCDClient(
        url=rest_endpoint,
        chain_id=testnet.chain_id,
        gas_prices=f"10{testnet.denom}",
        gas_adjustment=0.1,
    )

    sender_id = action["value"]["sender"]
    receiver_id = action["value"]["receiver"]
    amount = action["value"]["amount"]

    sender = testnet.accounts[sender_id].address(testnet.prefix)
    receiver = testnet.accounts[receiver_id].address(testnet.prefix)

    sender_wallet = lcdclient.wallet(
        MnemonicKey(
            mnemonic=testnet.accounts[sender_id].mnemonic,
            coin_type=testnet.coin_type,
            prefix=testnet.prefix,
        )
    )

    msg = MsgSend(sender, receiver, Coins([Coin(testnet.denom, amount)]))

    tx = sender_wallet.create_and_sign_tx(
        CreateTxOptions(
            msgs=[msg], fee=Fee(20000000, Coins([Coin(testnet.denom, 2000000)]))
        )
    )

    result = lcdclient.tx.broadcast(tx)

    print("[MSG]", msg)
    print("[RES]", result)

    time.sleep(2)
```

### Re-executing tests with complete reactors

Finally, you can run the complete test with the completed reactor and a trace.

<!-- $MDX dir=transfer -->
```sh
$ poetry run atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
...
Successfully executed trace traces/violation1.itf.json
...
```
