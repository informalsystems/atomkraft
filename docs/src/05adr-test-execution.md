# ADR-05: Test execution

| authors          | revision | revision date  |
| ---------------- | --------:| --------------:|
| Andrey Kuprianov |        1 | July 18, 2022  |

The present ADR describes the external interfaces of the `Execute` component that deals with test execution, either from a given abstract trace, or from (a set of) traces generated from a TLA+ model.


## Command line interface

Test execution CLI provides two main entry points:

- `test trace [--trace <trace-file>] [--reactor <reactor-file>]` allows to execute an abstract test trace against the chain. All additional parameters are optional; when omitted, the defaults will be used.
  - `--trace <trace-file>` allows to specify which test trace file to execute. 
  - `--reactor <reactor-file>` allows to provide explicitly the reactor to employ; when omitted, the reactor previously generated via `reactor` command will be used.
- `test model [--model <model-file>] [--config <config-file>] [--sample <sample-operator>]` allows to execute test traces generated from a TLA+ model. All additional parameters are optional; when omitted, the defaults will be used.
  - `--model <model-file>` allows to specify which TLA+ model to use.
  - `--config <config-file>` specifies the model configuration file.
  - `--sample <sample-operator>` gives the name of the sample operator describing the test traces.

