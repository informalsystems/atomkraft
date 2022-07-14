# ADR-02: Model-Checker task file

| authors                      | revision | revision date |
| ---------------------------- | -------: | ------------: |
| Ivan Gavran, Hernán Vanzetto |        1 | July 14, 2022 |

## Status

Proposed

## Summary

A model-checker (MC) task is a JSON file produced by the pre-processor module and consumed by the MC executor.
```json
{
    "checker": "<apalache|tlc>",
    "model": "<model_name>_MC.tla",
    "files": [
        { "<file_name_1>": "<file_content_1>" },
        { "...": "..." },
        { "<file_name_k>": "<file_content_k>" }
    ],
    "checks": {
        "<predicateName_constantsElementNum>":"<config_file_name>.cfg"
    },
    "timestamp": "<datetime>"
}
```

- The field `checker` contains either `apalache` or `tlc`.
- The field `model` contains the name of the TLA+ file with the model to check.
  The file name must have `_MC` as suffix.
- The field `files` contains an array of file names and their corresponding
  content. The array must contains all the files that are relevant for running
  the model checker, including the generated `.cfg` files.
- The field `checks` corresponds to individual runs of model checkers. Each run
  of a model checker corresponds to an element of the cross-product of
  predicates that the user wants to check and constants.