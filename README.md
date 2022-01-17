# atomkraft

*Testing should be easy!*

End-to-end testing for Cosmos blockchains.

## Install

To build the package, we require python3 and pip. Make sure that your version
is up to date by running:

```sh
python3 -m pip install --upgrade pip
```

We do not publish the package globally yet. Hence, to build atomkraft, run the
following commands:

```sh
git clone git@github.com:informalsystems/atomkraft.git
cd atomkraft
python3 -m pip install --upgrade build
python3 -m build
```

To install the built package of version `X.Y.Z`, run the command:

```sh
python3 -m pip install dist/atomkraft-informal-X.Y.Z.tar.gz
```

## Use

