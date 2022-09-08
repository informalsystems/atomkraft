# Cosmwasm Counter: Atomkraft example project

## Install/update `atomkraft` cli

```sh
pip install -U atomkraft
```

## Initialize atomkraft project

```sh
atomkraft init counter
cd counter
```

## Compile CosmWasm binary

```sh
rustup target add wasm32-unknown-unknown
# we provided one at examples/cosmwasm/counter/cosmwasm-contract
RUSTFLAGS='-C link-arg=-s' cargo build --release --target wasm32-unknown-unknown --manifest-path cosmwasm-contract/Cargo.toml
ls cosmwasm-contract/target/wasm32-unknown-unknown/release/counter.wasm # wasm binary
```

## Generate and update reactors

```sh
atomkraft reactor --actions store_cw_contract,instantiate,reset,increment,get_count --variables count,last_msg
# update the `reactors/reactor.py`
```

## Create tests

- Add ITF traces in `traces/`
- Add TLA+ models in `models/`
- Add tests in `tests/`
  - Soon we will provide CLI commands to auto-generate test files from traces or models)

## Compile `wasmd`

```sh
git clone https://github.com/CosmWasm/wasmd
(cd wasmd; make build)
ls wasmd/build/wasmd
```

## Update chain config

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

## Finally run the tests

```sh
atomkraft test trace --trace traces/example0.itf.json --reactor reactors/reactor.py --keypath last_msg.name
```
