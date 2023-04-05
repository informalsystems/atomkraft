# Contributing to Atomkraft

## Installation

### Using `pip` (inside a system or virtual env)

```
pip install atomkraft
atomkraft --help
# or
python -m atomkraft --help
```

### Using `poetry` (inside a project)

```
poetry add atomkraft
poetry run atomkraft --help
# or
poetry run python -m atomkraft --help
```

For experimenting with local changes, run `pip install -U <path to the Atomkraft repo>`.
For instance, if at the root of the repo, you can run `pip install -U .`.

## Code Quality

To run unit-tests, execute `pytest` (to run all existing tests) or `pytest <path>` (to execute only some tests), for instance `pytest tests/test_util.py`.

To run CLI tests locally, make sure to have [mdx](https://github.com/realworldocaml/mdx/blob/main/README.md) installed.
Afterwards, run `ocaml-mdx-test -v tests/cli/test_transfer.md`.

The tests are also run for every commit to the repository.

For basic linting and formatting, run

```
pip install black pylama
black . --check
pylama -l pyflakes,pycodestyle,isort
```

You can also use [pre-commit](https://pre-commit.com/) to run those as hooks (as defined in the `.pre-commit-config.yaml` file).
