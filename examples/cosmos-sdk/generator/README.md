# Generating Informal traces

One way to generate Informal traces is by running the model checker
[Apalache](https://github.com/informalsystems/apalache). This allows us
to easily produce hundreds of traces that satisfy user-defined properties.

In this directory, we introduce a very simple TLA+ specification of staking.
This specification is embarrassingly incomplete and even imprecise,
but it still allows us to generate interesting traces.

The state machine is specified in [Staking.tla](./Staking.tla). It implements
three actions that produce Cosmos SDK commands:

 - Action `Delegate` produces a transaction for the `staking delegate` command.
 - Action `Unbond` produces a transaction for the `staking unbond` command.
 - Action `Transfer` produces a transaction for the `bank transfer` command.

The particular instance of `Staking` is specified in
[`MC_Staking.tla`](./MC_Staking.tla). We should pay extra care to the constants
in this module, so they match the predefined constants in the trace executor
[exec-trace.py](../exec-trace.py).

Importantly, [`MC_Staking.tla`](./MC_Staking.tla) contains false invariant,
e.g., `NoUnbond` and `NoDelegate`. By running Apalache against
`MC_Staking.tla` and a false invariant, we are generating traces. For instance,
the trace [`trace2.itf.json`](../traces/trace2.itf.json) is one of the ten
traces that are generated as follows:

```sh
apalache check --inv=NoDelegateAndTransfer \
  --run-dir=exp22 --max-error=10 --view=TxView MC_Staking.tla
```

The above command generates up to 10 traces that violate the predicate
`NoDelegateAndTransfer`. These traces should differ in their state views
that are specified with `TxView`. The view gives us a simple way to partition
traces in different classes:

```tla
TxView ==
    <<lastTx.tag, lastTx.sender, lastTx.toAddr,
      lastTx.value > 0, lastTx.value > 1000,
      lastTx.value > PRECISION, lastTx.value >= (MAX_COSMOS_NUM - 1)>>
```
