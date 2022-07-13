# ADR-03: Atomkraft init subcommand

| authors         | revision | revision date |
| --------------- | -------: | ------------: |
| Ranadeep Biswas |        1 | July 13, 2022 |

## Status

Proposed

## Context

We are figuring out how a user will use Atomkraft - produce tests, interact with test setup, and execute them.

The idea is to provide an `atomkraft` cli, which initializes a [poetry](https://python-poetry.org) project with [pytest](https://docs.pytest.org) dependency and other necessary configurations.

## Decision

To set up an `atomkraft` project,

- `atomkraft init BINARY DIR` is executed which sets up a poetry project at `DIR`.
- After changing the directory to `DIR`, a user should be able to execute some kick-the-tire tests (included in Atomkraft) for standard Cosmos-SDK modules right out of the box.
- The chain parameters can be queried/modified using `atomkraft chain config CONFIGFILE KEYPATH [VALUE]`
- A testnet can be started via `atomkraft chain up [-d]`.
- A testnet can be shut down via `atomkraft chain down`.

## Summary

- `atomkraft init` to initialize atomkraft project as a poetry project with python 3.10 and pytest dependency
- `atomkraft test-drive` to execute a set of standard Cosmos-SDK tests using provided chain binary.
- `atomkraft chain config CONFIGFILE KEYPATH [VALUE]` to update chain configuration.
- `atomkraft chain [up|down]` to control a testnet.
