# ADR-02: Model-Checker Executor

| authors         | revision | revision date |
| --------------- | -------: | ------------: |
| Hernán Vanzetto |        1 | July 18, 2022 |

## Status

Proposed

## Summary

This document describes the architecture of the Model-Checker (MC) Executor,
consisting of two modules, one for models and one for traces. See a high-level
overview in Atomkraft's architecture diagram: ![Atomkraft architecture
diagram](images/architecture-diagram.png).

The underlying functionality of both modules is mostly provided by Modelator.

## Model module

This module deals with loading, parsing, and setting of models, as an interface
to the Modelator's `Model` class.

### CLI commands

The command `atomkraft model` is essentially a wrapper around Modelator's
`Model`, where each of its sub-commands would map almost one-to-one to the
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
atomkraft model info # will display filename(s), init, next, constants, invariants, ... 
atomkraft model monitor remove-all # will remove all initialized monitors
```

Apalache does not require a `cfg` file with the model, so we do not included in
the first prototype:
```
atomkraft model config load <model-config-file> # will call the `ModelConfig` class in Modelator
```

### Artifacts and programmatic interface

This module can load a model in memory that can be used by other modules.

This module does not expect any connection to other components.

## Trace module

This module deals with generation of execution traces from a model.

### CLI commands

The `atomkraft trace` command generates ITF traces. If no model is given as
parameter, it will use a model already loaded in memory with the `atomkraft
model` command. Its format is:
```
atomkraft trace [--model=<model>] <config-path> <test-assertion> [<traces-path>]
```
where:
- `<config-path>` is the (path to) TOML file with the model and model checker
  configuration (see below)
- `<test-assertion>` is the name of the model operator describing the desired
  test trace
- `<traces-path>` is a custom location for the trace files

Upon successful command execution, the generated test trace should be persisted
to disk in ITF format. The files will be located in a directory defined by the
Setup/Config module.

Under the hood, the `atomkraft trace` command will call the following Modelator
Shell commands:
```
model = ModelShell.parse_file(<model-path>)
model.typecheck()
config = ModelConfig.parse_file(<config-path>)
model.check(config, <test-assertion>, <traces-path>)
```
where `ModelConfig` would be a new class in Modelator, used as a common data
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
tlc_config_file = "path/to/ModuleName.cfg"

[Constants]
constant_name_1 = "tla_constant_value_1"
...
constant_name_n = "tla_constant_value_n"

[Config]
check_deadlock = FALSE
length=10 # called depth in TLC
```

#### Related commands:
```
atomkraft config traces-dir <traces-path> # sets the location for the generated trace files
atomkraft config traces-dir # displays the current directory for the trace files
```
#### Artifacts

This command generates ITF traces in the directory `default_traces_dir` provided
by the Setup module.

#### Relation to other modules

- Read the value of `default_traces_dir` provided by the Setup module.

## Decision

- Initially, we will support only Apalache; support for TLC will be postponed to
  a later version
