# ADR-02: Atomkraft init subcommand

| authors         | revision | revision date |
| --------------- | -------: | ------------: |
| Ranadeep Biswas |        2 | July 18, 2022 |

## Status

Proposed

## Context

We are figuring out how a user will use Atomkraft - produce tests, interact with test setup, and execute them.

The idea is to provide an `atomkraft` cli, which initializes a [poetry](https://python-poetry.org) project with [pytest](https://docs.pytest.org) dependency and other necessary configurations.

## Summary

- Set up a poetry project at the current directory.
- Perform lightweight smoke tests right out of the box.
- Configure chain parameters via CLI.

### `atomkraft init BINARY [TEST]...`

This command is used to initialize an Atomkraft project in the current directory.
It uses [copier](https://pypi.org/project/copier) to copy a template and dynamically update project variables.

#### Arguments

- `BINARY` is path to Cosmos-SDK chain binary.
  - "gaiad"
  - "/opt/cosmos-chains/junod"
- `[TEST]...` is a list of provided lightweight tests that can be included in the project.
  - "authz"
  - "cosmwasm"
  - "feegrant"

#### Template directory structure

```
.
├── .atomkraft
│   └─── config.toml
├── atomkraft.toml
├── chain.toml
├── modelator.toml
├── models
├── reactors
│   ├─── authz.py
│   └─── cosmwasm.py
├── reports
├── tests
│   ├─── conftest.py
│   ├─── test_authz.py
│   └─── test_cosmwasm.py
└── traces
```

#### `.atomkraft/config.toml`

Used to for any configuration local to current user. Example, last used reactor.

#### `atomkraft.toml`

This file is used for any top-level project configuration.

- The lightweight tests are marked in `atomkraft.toml` file.

##### Sample

```
[chain]
binary = "gaia"

[modelator.apalache]
jar = "/path/to/apalache/jar"

[tests]
lightweight = ["authz", "cosmwasm"]
```

#### `chain.toml`

The chain config values are stored in `chain.toml` file.

##### Sample

```
name = "cosmoshub"
prefix = "cosmos"
denom = "uatom"
coin = 118

[app]
"api.enable" = True
"api.swagger" = True
"api.enabled-unsafe-cors" = True
"minimum-gas-prices" = "0.10uatom"
"rosetta.enable" = False

[config]
"instrumentation.prometheus" = False
"p2p.addr_book_strict" = False
"p2p.allow_duplicate_ip" = True

[genesis]
"app_state.gov.voting_params.voting_period" = "600s"
"app_state.mint.minter.inflation" = "0.300000000000000000"
```

#### `modelator.toml`

Configs for Modelator.

##### Sample

```
[[models]]
model = "path/to/module.tla"
config = "path/to/module.cfg"
constants = {"N": 3, "FOO": "bar" }
invariants = ["Inv1", "Inv2"]
samples = ["Ex1", "Ex2"]
md_monitor = "path/to/monitor.md"
html_monitor = "path/to/monitor.html"
```

### `atomkraft chain config FILE KEY [VALUE]`

This command can be used to query or update chain parameters.

#### Arguments

- `KEY` is a nested key.
  - `coin`
  - `"app.api.enable"`
  - `"config.p2p.allow_duplicate_ip"`
  - `"genesis.app_state.gov.voting_params.voting_period"`

Note, `app`, `config` and `genesis` prefixes. They correspond to the usual `app.toml`, `config.toml`, and `genesis.json` files in a Cosmos-SDK chain node data directory.

- `VALUE` is used to overwrite the current value. If it is skipped, the current value is printed.

### `atomkraft chain test-drive`

After running `atomkraft init` (with included tests) and `atomkraft chain config`, the project should be ready to perform some lightweight tests.

`atomkraft chain test-drive` will run the light-weight tests using `reactors/*py` and `tests/test_*py`.

## Future work

- Spawn independent testnet via `atomkraft chain [up|down]`.
- Spawn blockchain explorer via `atomkraft chain explorer [up|down] [PORT]`.
- Spawn testnet with an explorer via `atomkraft chain --explorer [up|down]`.
