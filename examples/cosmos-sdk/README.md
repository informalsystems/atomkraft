# End-to-end testing of staking in Cosmos-SDK

This example provides us with a reproducible environment for executing Informal
traces against a single-node instance of Cosmos SDK with atomkraft.

## Run a single trace:

 1. Build a docker image and set up the chain by issung:

    ```sh
    $ make
    ```

 1. Run the chain in docker by issuing (in a separate terminal):

    ```sh
    $ ./start-node.sh
    ```

 1. Execute a trace against the dockerized blockchain:

    ```sh
    $ ./exec-trace.sh --script test.sh traces/trace2.itf.json
    ```

## What happened?

The script `exec-trace.sh` reads the trace from the file `trace2.itf.json` in
the [Informal Trace
Format](https://apalache.informal.systems/docs/adr/015adr-trace.html) and posts
transactions to the blockchain via `./client.sh`. You can observe that the
transactions produced unexpected results:

```
Input: traces/trace2.itf.json
Output: test.sh
cosmos balance:   999999363335802543203126000
expected balance: 999998999999999998999800000
validator has 363335802544203326000 more coins as expected (due to rewards?)
Expected transaction 0 to OK, got OK
Expected transaction 1 to FAIL, got OK
Executed 2 transactions
```

The script reported that the transactions were executed differently from what
has been encoded in the trace [`trace2.itf.json`](./traces/trace2.itf.json).
You can see the CLI commands that were executed in the generated file
`test.sh`:

```sh
./client.sh tx staking delegate \
  cosmosvaloper1uquty6wqc03pqpmz0t5fzh4fd5npfpd256ukjv 1000000000stake \
  --from cosmos1uquty6wqc03pqpmz0t5fzh4fd5npfpd23wgr7l
./client.sh tx bank send cosmos1uquty6wqc03pqpmz0t5fzh4fd5npfpd23wgr7l \
  cosmos1evyv7neax9qtxxzuexnhylxyz4guvsyjmwauct \
  999998999999999999000800000stake \
  --from cosmos1uquty6wqc03pqpmz0t5fzh4fd5npfpd23wgr7l  
```

From what we can see here, it is unexpected for the `bank transfer` to go
through, as the delegator's balance was expected to have fewer coins than is
required in the transfer. However, the command `staking delegate` has
transferred delegation rewards on the delegator's account, and the transfer
succeeded.

The above trace does not expose any bug in Cosmos SDK. Interestingly, it shows
that our expectations in the test deviate from the implementation.  In fact,
this trace reproduces the behavior that once was reported as a bug.

Check more traces in [traces](./traces).

## How to write my own traces?

Start with the exiting example, e.g.,
[`trace2.itf.json`](./traces/trace2.itf.json), change the transactions and
their payloads. The JSON format is documented in
[ADR0015](https://apalache.informal.systems/docs/adr/015adr-trace.html). The
structure of the state machine and its transactions is fixed in this example.
But you can change it by modifying the handlers in
[`exec-trace.py`](./exec-trace.py).

Writing longer traces is a laborious process. That is why
we are [generating them](./generator/README.md).

## How to add other types of transactions?

Extend the function `tx_to_fun` in the script
[`exec-trace.py`](./exec-trace.py) with your handlers. For instance, here is
how bank transfer is implemented:

```py
def tx_to_fun(scriptf, state):
    """Translate a transaction to a list of callables"""
    ...
    # tx bank send
    elif tx["tag"] == "transfer-cosmos":
        def fun():
            coin = "{d}stake".format(d=int(tx["value"]))
            sender = COSMOS_ACCOUNTS[tx["sender"]]["addr"]
            receiver = COSMOS_ACCOUNTS[tx["toAddr"]]["addr"]
            args = ["tx", "bank", "send",
                    sender, receiver, coin, "--from", sender]
            result = CosmosCmd(scriptf, COSMOS_BIN, args, []).call()
            # did the transaction succeed?
            return result != None and result

        return fun
   ...     
```

