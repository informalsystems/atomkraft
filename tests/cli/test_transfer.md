# Tests Transfer tutorial

## Init

```sh
$ [ -d transfer ] || atomkraft init transfer
...
$ [ -d transfer ] && echo Project directory created successfully
Project directory created successfully
```

## Model and traces

```sh
$ curl -Lo transfer/models/transfer.tla https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/transfer.tla
...
```

```sh
$ atomkraft model apalache info
...
Apalache JAR file exists and its version is 0.25.10
...
```

Clean `traces` directory:

```sh
$ rm -rf transfer/traces/*
```

<!-- $MDX dir=transfer -->

```sh
$ atomkraft model sample --model-path models/transfer.tla --traces-dir traces --examples Ex
...
- Ex OK ✅
...
```

Check that the previous command generated a trace file:

```sh
$ [ -f "transfer/traces/violation1.itf.json" ] && echo "Found trace file"
Found trace file
```

## Reactor

Clean `reactors` directory before running `atomkraft test`:

```sh
$ rm -rf transfer/reactors/*
```

<!-- $MDX dir=transfer -->

```sh
$ atomkraft reactor --actions "Init,Transfer" --variables "action"
```

Check that the reactor file was created:

```sh
$ find "transfer/reactors" -type f -iname "reactor.py" -exec echo File found! \;
File found!
```

Clean `tests` directory before running `atomkraft test`:

```sh
$ rm -rf transfer/tests/*
```

<!-- $MDX dir=transfer -->

```sh
$ atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
...
```

Check that a test file was created:

```sh
$ find "transfer/tests" -type f -iname "test_traces_violation1_itf_json_*.py" -exec echo File found! \;
File found!
```

```sh
$ curl -Lo transfer/reactors/reactor.py https://raw.githubusercontent.com/informalsystems/atomkraft/dev/examples/cosmos-sdk/transfer/reactor.py
...
```

## Tests

<!-- $MDX dir=transfer -->

```sh
$ poetry run atomkraft test trace --trace traces/violation1.itf.json --reactor reactors/reactor.py --keypath action.tag
...
Successfully executed trace traces/violation1.itf.json
...
```

## Clean up

```
rm -rdf transfer
```
