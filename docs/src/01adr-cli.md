# ADR-01: Atomkraft CLI

| authors           | revision | revision date  |
| ----------------- | --------:| --------------:|
| Andrey Kuprianov  |        1 | July 11, 2022  |

This ADR describes the command-line interface of Atomkraft, and how it is supposed to be used by the users as a standalone tool. It *does not* describe other possible usage scenarios, e.g. integration with testing frameworks (such as Pytest). We structure the description around the tool use cases.

Below we specify only the outcomes for successful command execution. Upon unsuccessful command execution, the error should be reported to the user, and no remnants (e.g. zombie processes, or additional files beyond requested) should remain.

## Launch a testnet

A user wants to set up a Cosmos-SDK testnet, using a specific binary of their choice, so that the testnet can later be used either for exploration or testing.  Upon successful command execution, the testnet should be in operational step, and keep running; the testnet mnemonic is returned to the user. The proposed command format:

```
atomkraft launch <binary> <genesis-config> <node-config>
```
where: 
    
- `<binary>` is the name or path to a Cosmos-SDK based blockchain binary (e.g. `gaiad`);
- `<genesis-config>` is the (path to) TOML file with the genesis configuration;
- `<node-config>` is the (path to) TOML file with the node configuration.

It should be possible to terminate one or all of the previously launched testnets:
- `atomkraft terminate <mnemonic>` should terminate the testnet launched previously under `<mnemonic>`;
- `atomkraft terminate <binary>` should terminate all testnets launched previously using `<binary>`;
- `atomkraft terminate` should terminate all previously launched testnets.

## Explore a testnet

A user wants to explore the running testnet visually (e.g. validators or transactions), so that they see the transactions live as they are executed. Upon successful command execution, a browser window is opened with the blockchain explorer for the specified testnet. The proposed command format:

```
atomkraft explore [<address>]
```

where `<address>` is the optional address for the blockchain explorer to connect to. If omitted, the explorer should connect to the testnet launched last.


## Generate test trace

A user has written a TLA+ model, and wants to generate some traces for test assertions from the model, so that they can understand the model behavior, and use some of the generated test traces later for executing on a testnet. Upon successful command execution, the generated test trace should be saved to disk. The proposed command format:

```
atomkraft generate <model> <model-config> <test-assertion>
```
where: 
- `<model>` is the (path to) TLA+ model;
- `<model-config>` is the (path to) TOML file with the model and model checker configuration;
- `<test-assertion>` is the name of the model operator describing the desired test trace.


## Generate test stub





## Execute a trace on the blockchain


