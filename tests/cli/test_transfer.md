# Tests Transfer tutorial

## Init

```sh
$ [ ! -d transfer ] || rm -rdf transfer
$ atomkraft init transfer
...
Atomkraft project is ready: transfer
...
$ cd transfer
```

## Model and traces

<!-- $MDX dir=transfer -->
```sh
$ curl -sLo models/transfer.tla https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/transfer.tla
```

```sh
$ atomkraft model apalache info
...
Apalache JAR file exists and its version is 0.25.10
...
```

Clean `traces` directory:

<!-- $MDX dir=transfer -->
```sh
$ rm -rf traces/*
```

<!-- $MDX dir=transfer -->
```sh
$ atomkraft model simulate --model-path models/transfer.tla --max-trace 4 --length 3 --traces-dir simulation_traces
...
Simulation completed✅
...
```

<!-- $MDX dir=transfer -->
```sh
$ atomkraft model sample --model-path models/transfer.tla --traces-dir traces --tests TestAliceZero
...
- TestAliceZero OK ✅
...
```

Check that the previous command generated a trace file:

<!-- $MDX dir=transfer -->
```sh
$ [ -f "traces/TestAliceZero/violation1.itf.json" ] && echo "Found trace file"
Found trace file
```

## Reactor

Clean `reactors` directory before running `atomkraft test`:

<!-- $MDX dir=transfer -->
```sh
$ rm -rf reactors/*
```

<!-- $MDX dir=transfer -->
```sh
$ atomkraft reactor --actions "Init,Transfer" --variables "action"
```

Check that the reactor file was created:

<!-- $MDX dir=transfer -->
```sh
$ find "reactors" -type f -iname "reactor.py" -exec echo File found! \;
File found!
```

Clean `tests` directory before running `atomkraft test`:

<!-- $MDX dir=transfer -->
```sh
$ rm -rf tests/*
```

<!-- $MDX dir=transfer -->
```sh
$ atomkraft test trace --path traces/TestAliceZero/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag --verbose
...
PASSED                                                                   [100%]
...
```

Check that a test file was created:

<!-- $MDX dir=transfer -->
```sh
$ find "tests" -type f -iname "test_test_alice_zero_violation*.py" -exec echo File found! \;
File found!
```

## Count

<!-- $MDX dir=transfer -->
```sh
$ rm -rf tests/*
$ atomkraft test trace --path traces/TestAliceZero/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag --verbose | grep PASSED | wc -l | xargs
1
$ rm -rf traces/*
$ atomkraft test model --model models/transfer.tla --test TestAliceZero --max-trace 7 --view View --reactor reactors/reactor.py --keypath action.tag | grep PASSED | wc -l | xargs
7
$ atomkraft test trace --reactor reactors/reactor.py --keypath action.tag --all --verbose | grep PASSED | wc -l | xargs
7
$ atomkraft test trace --path traces/TestAliceZero --reactor reactors/reactor.py --keypath action.tag --verbose | grep PASSED | wc -l | xargs
7
```

<!-- $MDX dir=transfer -->
```sh
$ curl -sLo reactors/reactor.py https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/reactor.py
```

## Test

### Trace

<!-- $MDX dir=transfer -->
```sh
$ atomkraft test trace --path traces/TestAliceZero/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag --verbose
...
PASSED                                                                   [100%]
...
```

### Model

<!-- $MDX dir=transfer -->
```sh
$ rm -rf traces/*
$ atomkraft test model --model models/transfer.tla --test TestAliceZero --max-trace 3 --view View --reactor reactors/reactor.py --keypath action.tag --verbose
...
PASSED                                                                   [ 33%]
...
PASSED                                                                   [ 66%]
...
PASSED                                                                   [100%]
...
```

## Lints

The generated Python test files are correctly formatted:

<!-- $MDX dir=transfer -->
```sh
$ black --line-length 1000 . --check
...
All done! ✨ 🍰 ✨
...
$ pylama -l pyflakes,pycodestyle,isort
```

## Clean up

```
rm -rdf transfer
```
