# Cosmwasm Counter: Atomkraft example project

This example showcases Atomkraft on CosmWasm. The example is already instantiated as an Atomkraft project and contains an example `cw-contract`. You only need to build the `cw-contract` and the `wasmd` before running the tests.

## Instructions

### Compile `cw-contract`

```sh
rustup target add wasm32-unknown-unknown
# we provided one cw-contract at cosmwasm-contract/
RUSTFLAGS='-C link-arg=-s' cargo build --release --target wasm32-unknown-unknown --manifest-path cosmwasm-contract/Cargo.toml
ls cosmwasm-contract/target/wasm32-unknown-unknown/release/counter.wasm # wasm binary
```

### Compile `wasmd`

```sh
git clone --depth 1 https://github.com/CosmWasm/wasmd
(cd wasmd; make build)
ls wasmd/build/wasmd # wasmd binary
```

### Make sure Atomkraft is installed and set up Apalache

```
atomkraft model apalache get # to download and set up apalache
atomkraft model apalache info # confirm apalache distribution
```

### Generate traces

```sh
atomkraft model simulate --model-path models/counter.tla --max-trace 10 --length 10 --traces-dir traces --view=View
```

### Run tests on generated traces

```sh
# just one trace
atomkraft test trace --path traces/example1.itf.json --reactor reactors/reactor.py --keypath last_msg.tag
# or all traces in a directory
atomkraft test trace --path traces --reactor reactors/reactor.py --keypath last_msg.tag
```

## Recipe for this example project

### Install/update `atomkraft` cli

```sh
pip install -U atomkraft
```

### Initialize atomkraft project

```sh
atomkraft init counter
cd counter
```

### Generate and update reactors

```sh
atomkraft reactor --actions store_cw_contract,instantiate,reset,increment,get_count --variables count,last_msg
# update the `reactors/reactor.py`
```

### Create tests

- Add ITF traces in `traces/`
- Add TLA+ models in `models/`
- Add tests in `tests/`
  - Soon we will provide CLI commands to auto-generate test files from traces or models)

### Update chain config

```sh
atomkraft chain config chain_id test-cosmos
atomkraft chain config binary ./wasmd/build/wasmd
atomkraft chain config hrp_prefix wasm
atomkraft chain config coin_type 118

atomkraft chain config accounts 3
atomkraft chain config validators 2

atomkraft chain config denom stake
atomkraft chain config config_node.app.minimum-gas-prices 0.10stake
```
