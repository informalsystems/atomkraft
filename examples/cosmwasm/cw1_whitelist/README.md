# Cosmwasm Counter: Atomkraft example project

This example showcases Atomkraft on CosmWasm. The example is already instantiated as an Atomkraft project and contains an example `cw1_whitelist`. Cw1_whitelist contract is the smart contract taken from [cwplus repo](https://github.com/CosmWasm/cw-plus). More information on contract itself: [cw1_whitelist](https://github.com/CosmWasm/cw-plus/tree/main/contracts/cw1-whitelist).
Here, atomkraft contain precompiled smart contract, which is later used for testing. Cwplus repo contains instructions how to build the smart contract.

## Instructions for running tests

### Compile `wasmd`

```sh
git clone --depth 1 https://github.com/CosmWasm/wasmd
(cd wasmd; make build)
ls wasmd/build/wasmd # wasmd binary
```

If you have wasmd already compiled inside your computer, you can just put path to the `wasmd` executable inside `chain.toml` file.

### Add test data

- Add ITF traces in `traces/`
- Add TLA+ models in `models/`
Trace can be generated from TLA+ model, using `atomkraft model` command.

### Install/update `atomkraft` cli

```sh
pip install -U atomkraft
```

### Initialize atomkraft project

```sh
atomkraft init cw1_whitelist
cd cw1_whitelist
```

### Update chain config

```sh
atomkraft chain config chain_id test-cosmos
atomkraft chain config binary wasmd # or put path to your wasmd binary
atomkraft chain config hrp_prefix wasm
atomkraft chain config coin_type 118

atomkraft chain config accounts 21
atomkraft chain config validators 2

atomkraft chain config denom stake
atomkraft chain config config_node.app.minimum-gas-prices 0.10stake
```

### Generate and update reactors

```sh
 atomkraft reactor --actions "idle, store_cw_contract, instantiate, execute, freeze, update_admins, get_admin_list, get_can_execute" --variables "last_msg"
```

This command generated reactor stub. After that, reactor source code is written, by extending the generated stub.

### Finally run the tests

```sh
atomkraft test trace --path traces/violation1.itf.json --reactor reactors/reactor.py --keypath last_msg.name
```

