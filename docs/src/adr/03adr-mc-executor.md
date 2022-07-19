# ADR-02: Model-Checker Executor

| authors         | revision | revision date |
| --------------- | -------: | ------------: |
| Hernán Vanzetto |        1 | July 18, 2022 |

## Status

Proposed first architecture for a prototype

## Summary

This document describes the architecture of the Model-Checker (MC) Executor,
consisting of a module for loading models and generating traces. Modelator
provides most of its underlying functionality.

## Description

The MC Executor module deals with loading, parsing, and setting of models, and
also with the generation of traces.

### CLI commands

The CLI command `atomkraft model` is essentially a wrapper around Modelator's
`Model` class, where each of its sub-commands would map almost one-to-one to the
methods of `Model`:
```
atomkraft model load <model-path> # in Model it's the parse_file method
atomkraft model typecheck
atomkraft model instantiate <constant-name> <constant-value>
atomkraft model check [<invariant-list>] [--constants=<name>:<value>,...] # for now, checker is Apalache, and checker params are the default values
atomkraft model sample [<sample-list>] [--constants=<name>:<value>,...] 
atomkraft model last-sample
atomkraft model all-samples
atomkraft model monitor add markdown <monitor-file.md>
atomkraft model monitor add html <monitor-file.html>
```

Additionally, `model` has the following sub-commands that require some extra
logic not directly provided by Modelator:
```
atomkraft trace [--model=<model>] <config-path> <test-assertion>
atomkraft model info # will display filename(s), init, next, constants, invariants, ... 
atomkraft model monitor remove-all # will remove all initialized monitors
```

The `atomkraft model trace` command generates ITF traces. If no model is given
as parameter, it will use an already loaded model. Its parameters are:
- `<config-path>`, the path to a TOML file with the model and model checker
  configuration (see below)
- `<test-assertion>`, the name of the TLA+ operator describing the desired test
  trace

Upon successful command execution, the generated test trace should be persisted
to disk in ITF format. The files will be located in the `traces` directory.

Under the hood, `atomkraft model trace` calls the following Modelator Shell
commands:
```
model = ModelShell.parse_file(<model-path>)
model.typecheck()
config = ModelConfig.parse_file(<config-path>)
model.check(config, <test-assertion>, <traces-path>)
```
where `ModelConfig` will be a new class in Modelator, used as a common data
structure for Apalache and TLC configurations.

### Model config file

A model config is a TOML file located in the same directory as the model, with
the following format:
```
[Model]
name = "ModuleName"
init = "Init"
next = "Next"
spec = "Spec"
invariants = ["Inv1", "Inv2", ...]
samples = ["Ex1", "Ex2", ...]
tlc_config_file = "path/to/ModuleName.cfg"

[Constants]
constant_name_1 = "tla_constant_value_1"
...
constant_name_n = "tla_constant_value_n"

[Config]
check_deadlock = FALSE
length = 10 # called 'depth' in TLC

[Monitors]
md = "path/to/monitor.md"
html = "path/to/monitor.html"
```

### Artifacts and programmatic interface

The MC Executor module can load a file with a TLA+ model that can be used by other modules.
The `trace` sub-command generates ITF trace files.

#### Relation to other modules

MC Executor provides the following functions that can be called by other modules.
- `get_all_traces()` will return a list with all the trace files in the default directory for traces.
- `get_trace(trace_file_path)` will return the content of the file `trace_file_path`.

## Decision

- Initially, we will support only Apalache; support for TLC will be postponed to
  a later version
