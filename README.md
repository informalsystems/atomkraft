# atomkraft

Testing for Cosmos Blockchains

### Using `pip` (inside a system or virtual env)

```
git clone https://github.com/informalsystems/atomkraft.git
cd atomkraft
pip install atomkraft
atomkraft --help
# or
python -m atomkraft --help
```

### Using `poetry` (inside a project)

```
git clone https://github.com/informalsystems/atomkraft.git
cd atomkraft
poetry install --no-interaction --no-root
poetry add atomkraft
poerty run atomkraft --help
# or
poetry run python -m atomkraft --help
```

### Code Quality

```
pip install black pylama[all]
black . --check
pylama -l pyflakes,pycodestyle,isort
```
