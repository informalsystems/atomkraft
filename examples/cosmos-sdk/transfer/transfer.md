# Atomkraft test project

## Token transfer

### Prerequisite

- [`pip3.10`](https://pip.pypa.io/en/stable/installation) for `python3.10`: To install Atomkraft executable
  - If `python3.10` is unavailable for your distribution, you can use `pyenv` to setup `python3.10`.
    - `pyenv install 3.10.5; pyenv global 3.10.5`.
    - When you're done, you can revert back by `pyenv global system`.
- [`poetry`](https://python-poetry.org/docs/#installation): For Atomkraft project
  - It will be auto-installed if not present.
- [`git`](https://github.com/git-guides/install-git): To clone Atomkraft template and Cosmos-SDK chain repo
- [`make`](https://www.gnu.org/software/make): Compile Cosmos-SDK chain binary
- [`go`](https://go.dev/doc/install): Compile Cosmos-SDK chain binary
- [`java`](https://www.java.com/download): For [Apalache](https://apalache.informal.systems) model checker

#### `ubuntu`

```
apt update -y && apt upgrade -y
apt install python3-pip git golang curl default-jre -y
pip install --upgrade poetry
```

#### `macOS`

```
brew install pyenv git go java
pyenv install 3.10.5
pyenv global 3.10.5
```

#### `archlinux`

```
pacman -Syu python-pip python-poetry git make go jre-openjdk gcc --noconfirm --needed
```

### Install Atomkraft

```sh
$ pip install --upgrade atomkraft
...
```

### Initialize project

```sh
$ atomkraft init transfer
...
$ cd transfer
```

`atomkraft init` creates a new directory and initializes a Poetry project in it.
It also auto-installs Poetry if needed. It also adds required dependencies to the project.

### Activate Poetry shell

```
poetry shell
```

### Create a model specification

We will model a simple token transfer between two users.
Alice and Bob both start with 100 tokens.
At each step, Alice or Bob will send some amount of tokens to the other person.
We will use TLA+ to specify this model.
You can use the following code to _jump-start_ a new model at `models/transfer.tla`.

<!-- $MDX dir=transfer -->
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

Inv == step < 10

====
```

### Generate traces

We will use Apalache model checker to generate traces from our model.

#### Download Apalache

<!-- $MDX dir=transfer -->
```sh
$ curl -Lo- https://github.com/informalsystems/apalache/releases/download/v0.26.0/apalache-0.26.0.tgz | tar -zxf-
...
```

The Apalache executable will be at `./apalache-0.26.0/bin/apalache-mc`.

The following will generate traces at `traces/`.

<!-- $MDX dir=transfer -->
```sh
$ ./apalache-0.26.0/bin/apalache-mc check --init=Init --next=Next --inv=Inv --view=View --max-error=10 --run-dir=mc_traces models/transfer.tla
...
[12]
$ find mc_traces -type f -iname "violation*.itf.json" -not -iname "violation.itf.json" -exec cp {} traces \;
$ rm -r mc_traces
```

### Generate reactors

Once we have some traces, we can generate reactor stubs for the traces.

In our model, the `action` variable had two tags - `Init`, `Transfer`.

<!-- $MDX dir=transfer -->
```sh
$ atomkraft reactor --actions "Init,Transfer" --variables "action"
```

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
    testnet.n_accounts = action["value"]["n_wallet"]
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
$ poetry run atomkraft test trace --trace traces/violation2.itf.json --reactor reactors/reactor.py --keypath action.tag
...
Successfully executed trace traces/violation2.itf.json
...
$ poetry run atomkraft test trace --trace traces/violation3.itf.json --reactor reactors/reactor.py --keypath action.tag
...
Successfully executed trace traces/violation3.itf.json
...
```
