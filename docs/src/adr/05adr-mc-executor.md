# ADR-02: Model-Checker Executor

| authors         | revision | revision date |
| --------------- | -------: | ------------: |
| Hernán Vanzetto |        1 | July 11, 2022 |

## Status

Proposed

## Summary

This ADR describes the architecture of the model-checker (MC) executor module.

Given as input:
- an [MC task file](04adr-mc-task-file.md), containing information about which
  model checker to run and on which TLA+ specs and properties, and
- (optionally) a json file with specific parameters to the model-checker, 

the MC executor produces as output: 
- a list of ITF trace files in case of success, and 
- a json file with information about the MC execution, such as success or
failure of the execution, error messages, if any, etc.

The MC executor can be seen in the Atomkraft's architecture diagram: ![Atomkraft
architecture diagram](images/architecture-diagram.png).

## Context

An [MC task file](04adr-mc-task-file.md) contains all the information about the
model required to run an instance of a model checker, including TLA+ files and
(model) configuration files.

The functionality is mostly implemented by Modelator. The MC executor module
will just parse the input, call Modelator, and produce the output files.

## Decision

- Initially, support only Apalache 
- Support for TLC will be postponed to a later version
