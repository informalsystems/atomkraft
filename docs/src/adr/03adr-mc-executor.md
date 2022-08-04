# ADR-02: Model-Checker Executor

| authors         | revision | revision date  |
| --------------- | -------: | -------------: |
| Hernán Vanzetto |        1 | August 4, 2022 |

## Status

Proposed first architecture for a prototype

## Summary

This document describes the architecture of the Model-Checker (MC) Executor,
which is a module for handling models and generating traces. Modelator provides
most of its underlying functionality.

## Description

The MC Executor module deals with loading, parsing, instantiating, and running the
models to produce execution trace files.

### CLI commands

The CLI command `atomkraft model` is essentially a wrapper around Modelator's
`Model` class, where each of its sub-commands would map almost one-to-one to the
methods of `Model`:

| Command     | Description |
|-------------|-------------|
| `load`      | Load a TLA+ model file and parses it. |
| `reload`    | Reload current model, if any. |
| `info`      | Display information on the loaded model, if available. |
| `reset`     | Removes any loaded model. |
| `typecheck` | Type check the loaded model, if available. |
| `check`     | Check that the invariants hold in the model, or generate a trace for a counterexample. |
| `sample`    | Generate execution traces that reach the state described by the `examples` properties. |

### Load, reload, reset, info

The `load` command parses the file in `model-path` and creates a `Model` object,
which will be serialized with the standard `pickle` library and saved as
`.model.pickle`.
```
atomkraft model load <model-path>
```

Any other command that requires a model will try to load the `pickle` file if no
other model is provided.

The `reload` command will simply take the path to the model file from the
`pickle` file (if it exists), parse it again, serialize the object model, and
save it.
```
atomkraft model reload
```

The `info` command removes displays information about the model found in the object model file, such as model path, init and next predicates, constant definitions, files in the model, etc.
```
atomkraft model info
```

The `reset` command removes the object model file `.model.pickle` if it exists.
```
atomkraft model reset
```
#### Typecheck

```
atomkraft model typecheck
```
runs Apalache's type-checker on the loaded model.

#### Check and sample

The following two commands run the model checker and generate traces. The only
difference is in how they check model properties, that is, the invariants and
examples.

An invariant must hold in each state and, if is violated, the model checker will
produce an execution trace as a counter-example of the violated property. 

An example predicate is a state property that must be satisfied at some point in
the state space exploration. When the example predicate holds, the model checker
stops and provides the execution trace leading to the state satisfying the
desired property. The example predicate may be a property of one state, two
consecutive states, if it includes primed variables, or many states if it
involves temporal logic operators.

```
atomkraft model check [--config-path=<config-path>] 
    [--model-path=<model-path>] 
    [--constants=<name>:<value>,...] 
    [--invariants=<invariants-list>]
    [--traces-dir=<traces-dir>]
atomkraft model sample [--config-path=<config-path>] 
    [--model-path=<model-path>] 
    [--constants=<name>:<value>,...] 
    [--examples=<examples-list>] 
    [--traces-dir=<traces-dir>]
```

If a path to a configuration file is provided, the command will load all
available settings from that file. Subsequent options provided to the command
will override those settings.

For now, checker is Apalache, and checker params are the default values

If no model is given as parameter, it will use an already loaded model. Its
parameters are:
- `<config-path>`, the path to a TOML file with the model and model checker
  configuration (see below)

Upon successful command execution, the generated test trace should be persisted
to disk in ITF format. The files will be located in the `traces` directory.

#### Commands not implemented yet

```
atomkraft model instantiate <constant-name> <constant-value>
atomkraft model last-sample
atomkraft model all-samples
atomkraft model monitor add markdown <monitor-file.md>
atomkraft model monitor add html <monitor-file.html>
atomkraft model monitor remove-all # will remove all initialized monitors
```

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
