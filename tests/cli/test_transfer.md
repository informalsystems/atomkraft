# Tests Transfer tutorial

## Init

```sh
$ [ -d transfer ] || atomkraft init transfer
...
$ cd transfer
```

## Model and traces

<!-- $MDX dir=transfer -->
```sh
$ curl -Lo models/transfer.tla https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/transfer.tla
...
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
$ atomkraft model sample --model-path models/transfer.tla --traces-dir traces --examples Ex
...
- Ex OK ✅
...
```

Check that the previous command generated a trace file:

<!-- $MDX dir=transfer -->
```sh
$ [ -f "traces/Ex/violation1.itf.json" ] && echo "Found trace file"
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
$ atomkraft test trace --trace traces/Ex/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag --verbose
...
```

Check that a test file was created:

<!-- $MDX dir=transfer -->
```sh
$ find "tests" -type f -iname "test_traces_Ex_violation1_itf_json_*.py" -exec echo File found! \;
File found!
```

## Count

<!-- $MDX dir=transfer -->
```sh
$ rm -rf tests/*
$ atomkraft test trace --trace traces/Ex/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag --verbose | grep PASSED | wc -l | xargs
1
$ rm -rf traces/*
$ atomkraft test model --model models/transfer.tla --test Ex --max-trace 25 --view View --reactor reactors/reactor.py --keypath action.tag | grep PASSED | wc -l | xargs
25
$ atomkraft test trace --reactor reactors/reactor.py --keypath action.tag --all --verbose | grep PASSED | wc -l | xargs
25
$ atomkraft test trace --reactor reactors/reactor.py --keypath action.tag --trace traces/Ex --verbose | grep PASSED | wc -l | xargs
25
```

<!-- $MDX dir=transfer -->
```sh
$ curl -Lo reactors/reactor.py https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/reactor.py
...
```

## Test

### Trace

<!-- $MDX dir=transfer -->
```sh
$ atomkraft test trace --trace traces/Ex/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
...
```

### Model

<!-- $MDX dir=transfer -->
```sh
$ rm -rf traces/*
$ atomkraft test model --model models/transfer.tla --test Ex --max-trace 3 --view View --reactor reactors/reactor.py --keypath action.tag
...
```

## Lints

<!-- $MDX dir=transfer -->
```sh
$ black . --check
...
$ pylama -l pyflakes,pycodestyle,isort
...
```

## Clean up

```
rm -rdf transfer
```
