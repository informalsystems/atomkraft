# Cosmwasm Counter: Atomkraft example project

## Install/update `atomkraft` cli

```
pip install -U atomkraft
```

## Initialize atomkraft project

```
atomkraft init counter
cd counter
```

## Add CosmWasm project as Git submodule

```
git submodule add --force git@github.com:Ethernal-Tech/counter-example-contract
```

## Compile CosmWasm binary

```
rustup target add wasm32-unknown-unknown
RUSTFLAGS='-C link-arg=-s' cargo build --release --target wasm32-unknown-unknown --manifest-path counter-example-contract/Cargo.toml
ls counter-example-contract/target/wasm32-unknown-unknown/release/counter.wasm # wasm binary
```

## Generate and update reactors

```
atomkraft reactor --actions store_cw_contract,instantiate,reset,increment,get_count --variables count,last_msg
# update the `reactors/reactor.py`
```

## Create tests

- Add ITF traces in `traces/`
- Add TLA+ models in `models/`
- Add tests in `tests/`
  - Soon we will provide CLI commands to auto-generate test files from traces or models)

## Update chain config

```
atomkraft chain config chain_id test-cw
atomkraft chain config binary junod
atomkraft chain config prefix juno
atomkraft chain config coin_type 118

atomkraft chain config n_account 3
atomkraft chain config n_validator 2

atomkraft chain config denom stake
atomkraft chain config config.node.app.minimum-gas-prices 0.10stake
```

## Finally run the tests

```
python -m pytest -s tests/test_wasm.py -p reactors.reactor
```
