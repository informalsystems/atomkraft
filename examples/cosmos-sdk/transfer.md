# Atomkraft test project

## Token transfer

### Prerequisite

- [`python`](https://www.python.org/downloads) 3.10: For Atomkraft
- [`pip`](https://pip.pypa.io/en/stable/installation): To install Atomkraft executable
  - Normally after installing Python, you may just want to execute `python -m ensurepip --upgrade` to have `pip` installed.
- [`poetry`](https://python-poetry.org/docs/#installation): For Atomkraft project
- [`git`](https://github.com/git-guides/install-git): To clone Atomkraft template and Cosmos-SDK chain repo
- [`make`](https://www.gnu.org/software/make): Compile Cosmos-SDK chain binary
- [`go`](https://go.dev/doc/install): Compile Cosmos-SDK chain binary
- [`java`](https://www.java.com/download): For [Apalache](https://apalache.informal.systems) model checker

#### `ubuntu`

```
apt update -y && apt upgrade -y
apt install pip3 git golang curl default-jre -y
pip install --upgrade poetry
```

#### `archlinux`

```
pacman -Syu python-pip python-poetry git make go jre-openjdk gcc --noconfirm --needed
```

### Install Atomkraft

```
pip install --upgrade atomkraft
```

### Initialize project

```
atomkraft init transfer
cd transfer
```

### Turn on Poetry shell

```
poetry shell
```

### Create a model specification

We will model a simple token transfer between two users.
Alice and Bob both start with 100 tokens.
At each step, Alice or Bob will send some amount of tokens to the other person.
We will use TLA+ to specify this model.
You can use the following code to _jump-start_ a new model at `models/transfer.tla`.

```
cat > models/transfer.tla << EOF
---- MODULE transfer ----
EXTENDS Apalache, Variants, Integers, FiniteSets

VARIABLES
    \* @type: Int -> Int;
    balances,
    \* @type: Init({n_wallet: Int}) | Transfer({sender: Int, receiver: Int, amount: Int});
    action,
    \* @type: Int;
    step

WALLETS == 0..1

Init ==
    /\ balances = [wallet \in WALLETS |-> 100]
    /\ action = Variant("Init", [n_wallet |-> Cardinality(WALLETS)])
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
        /\ action' = Variant("Transfer", [sender |-> sender, receiver |-> receiver, amount |-> amount])
    /\ step' = step + 1

View ==
    IF VariantTag(action) = "Transfer"
    THEN VariantGetUnsafe("Transfer", action)
    ELSE [sender |-> -1, receiver |-> -1, amount |-> 0]

Inv == step < 10

====
EOF
```

### Generate traces

#### Download Apalache

We will use Apalache to generate traces from our model.

```
curl -Lo- https://github.com/informalsystems/apalache/releases/download/v0.26.0/apalache-0.26.0.tgz | tar -zxf-
```

The Apalache executable will be at `./apalache-0.26.0/bin/apalache-mc`.

The following will generate traces at `traces/`.

```
./apalache-0.26.0/bin/apalache-mc check --features=rows --init=Init --next=Next --inv=Inv --view=View --max-error=10 --run-dir=mc_traces models/transfer.tla
ls -1I violation.itf.json mc_traces/violation*itf.json | xargs cp -t traces
rm -r mc_traces
```

### Generate reactors

Once we have some traces, we can generate reactor stubs for the traces.

In our model, the `action` variable had two tags - `Init`, `Transfer`.

```
atomkraft reactor --actions "Init,Transfer" --variables "action"
```

### Setting up chains

Once we have the stub ready, we can set up the chain binary for the testnet.

We will use `juno` chain binary. But any Cosmos-SDK derived chain should work.

#### Binary

```
git clone --depth 1 --branch v9.0.0 https://github.com/CosmosContracts/juno
(cd juno; make build)
```

The binary will be at `./juno/bin/junod`

### Chain parameters

Now we can update the chain parameters.

```
atomkraft chain config chain_id test-cw
atomkraft chain config binary ./juno/bin/junod
atomkraft chain config prefix juno
```

### Executing tests

We have some traces and a reactor stub ready. Now we can smoke-test the test.

```
atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
```

For now, this just prints the name of the action tag. Let's complete the reactor stub.

### Updating reactors

Update `reactors/reactor.py` with the following complete reactor code.

```
cat > reactors/reactor.py << EOF
import time

from modelator.pytest.decorators import step
from terra_sdk.client.lcd import LCDClient
from terra_sdk.client.lcd.api.tx import CreateTxOptions
from terra_sdk.core import Coins, Coin
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
    lcdclient = LCDClient(url=rest_endpoint, chain_id=testnet.chain_id)

    sender_id = action["value"]["sender"]
    receiver_id = action["value"]["receiver"]
    amount = action["value"]["amount"]

    sender = testnet.accounts[sender_id].address(testnet.prefix)
    receiver = testnet.accounts[receiver_id].address(testnet.prefix)

    sender_wallet = lcdclient.wallet(
        MnemonicKey(
            testnet.prefix,
            mnemonic=testnet.accounts[sender_id].mnemonic,
            coin_type=testnet.coin_type,
        )
    )

    msg = MsgSend(
        sender, receiver, Coins([Coin(testnet.denom, amount)])
    )

    tx = sender_wallet.create_and_sign_tx(
        CreateTxOptions(
            msgs=[msg], fee=Fee(20000000, Coins([Coin(testnet.denom, 2000000)]))
        )
    )

    result = lcdclient.tx.broadcast(tx)

    print("[MSG]", msg)
    print("[RES]", result)

    time.sleep(2)
EOF
```

### Re-executing tests with complete reactors

Finally, you can run the complete test with the completed reactor and a trace.

```
atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
atomkraft test trace --trace traces/violation2.itf.json --reactor reactors/reactor.py --keypath action.tag
atomkraft test trace --trace traces/violation3.itf.json --reactor reactors/reactor.py --keypath action.tag
```
