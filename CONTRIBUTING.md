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

## Code Quality

```
pip install black pylama[all]
black . --check
pylama -l pyflakes,pycodestyle,isort
```
