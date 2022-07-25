# Cosmwasm Counter: Atomkraft example project

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
RUSTFLAGS='-C link-arg=-s' cargo build --release --target wasm32-unknown-unknown --manifest-path counter-example-contract/Cargo.toml
ls counter-example-contract/target/wasm32-unknown-unknown/release/counter.wasm # wasm binary
```

## Create tests

- Add TLA+ models in `models/`
- Add ITF traces in `traces/`
- Add tests in `tests/`

## Generate and update reactors

```
atomkraft reactor --actions "store_cw_contract,instantiate,reset,increment,get_count" --variables "count,last_msg"
# update the `reactors/reactor.py`
```

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
