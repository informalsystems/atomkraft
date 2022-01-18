------------------------- MODULE Staking ---------------------------------
(*
 * Modeling delegate and unbond in the staking module.
 * This is a very minimal spec to reproduce a reported issue.
 *
 * Simplifications:
 *   - We keep track of the gas token only (e.g., stake in cosmos-sdk).
 *   - We assume only one validator to be delegated to.
 *   - Rewards are not specified.
 * 
 * Igor Konnov, 2021
 *)
EXTENDS Integers, Apalache, Staking_typedefs

CONSTANTS
    \* Set of all addresses on Cosmos.
    \* @type: Set(ADDR);
    UserAddrs

VARIABLES
    \* Coin balance for every Cosmos account.
    \*
    \* @type: BALANCE;
    balanceOf,
    \* Balance of unbonded coins that cannot be used during the bonding period.
    \*
    \* @type: BALANCE;
    unbonded,
    \* Coins that are delegated to Validator.
    \*
    \* @type: BALANCE;
    delegated

\* Variables that model transactions, not the state machine.
VARIABLES    
    \* The last executed transaction.
    \*
    \* @type: TX;
    lastTx,
    \* A serial number to assign unique ids to transactions
    \* @type: Int;
    nextTxId,
    \* Whether at least one transaction has failed
    \* @type: Bool;
    failed

\* the maximum value in Cosmos
MAX_UINT == 2^(256 - 60) - 1

\* 1 billion coins in the initial supply
INITIAL_SUPPLY == 10^(9+18)

\* the number of coins the validator has staked
INIT_VALIDATOR_STAKE == 1000000000000000000000

\* gas burned by every tx (we hard-code it)
GAS_PER_TX == 200000

\* the validator account
Validator == "validator"

\* Initialize the balances
Init ==
    \* user{1,2,3} have 1M Cosmos coins, the validator has 1M - stake
    /\ balanceOf = [ a \in UserAddrs |->
        IF a /= "validator"
        THEN INITIAL_SUPPLY
        ELSE INITIAL_SUPPLY - INIT_VALIDATOR_STAKE
       ]
    /\ unbonded = [ a \in UserAddrs |-> 0 ]
    /\ delegated = [
        a \in UserAddrs |-> IF a /= "validator"
        THEN 0
        ELSE INIT_VALIDATOR_STAKE
       ]
    /\ nextTxId = 0
    /\ lastTx = [ id |-> 0, tag |-> "None", fail |-> FALSE ]
    /\ failed = FALSE


\* delegate `amount` coins to Validator
Delegate(sender, amount) ==
    LET fail ==
        \/ amount < 0
        \/ amount + GAS_PER_TX > balanceOf[sender]
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "delegate", fail |-> fail,
                   sender |-> sender, toAddr |-> Validator, value |-> amount ]
    /\ nextTxId' = nextTxId + 1
    /\ failed' = (fail \/ failed)
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, unbonded, delegated>>
        ELSE
          \* transaction succeeds
          \* update the balance of 'sender'
          /\ balanceOf' =
                [ balanceOf EXCEPT ![sender] = @ - amount - GAS_PER_TX]
          /\ delegated' = [ delegated EXCEPT ![sender] = @ + amount ]
          /\ UNCHANGED unbonded


\* unbond `amount` coins from Validator
Unbond(sender, amount) ==
    LET fail ==
        \/ amount < 0
        \/ sender = Validator
        \/ amount > delegated[sender]
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "unbond", fail |-> fail,
                   sender |-> sender, toAddr |-> Validator, value |-> amount ]
    /\ nextTxId' = nextTxId + 1
    /\ failed' = (fail \/ failed)
    /\  IF fail
        THEN
          UNCHANGED <<balanceOf, unbonded, delegated>>
        ELSE
          \* transaction succeeds
          \* the balance of 'sender' should decrease as we are burning gas
          /\ balanceOf' = [ balanceOf EXCEPT ![sender] = @ - GAS_PER_TX]
          /\ unbonded' = [ unbonded EXCEPT ![sender] = @ + amount ]
          /\ delegated' = [ delegated EXCEPT ![sender] = @ - amount ]

\* Transfer `amount` coins. We use it to test other transactions.
Transfer(sender, receiver, amount) ==
    LET fail ==
        \/ amount < 0
        \/ sender = receiver
        \/ amount > balanceOf[sender] - GAS_PER_TX
    IN
    /\ lastTx' = [ id |-> nextTxId, tag |-> "transfer-cosmos", fail |-> fail,
                   sender |-> sender, toAddr |-> receiver, value |-> amount ]
    /\ nextTxId' = nextTxId + 1
    /\ failed' = (fail \/ failed)
    /\  IF fail
        THEN UNCHANGED <<balanceOf, unbonded, delegated>>
        ELSE
          \* transaction succeeds
          \* the balance of 'sender' should decrease as we are burning gas
          /\ balanceOf' = [ balanceOf EXCEPT
              ![sender] = @ - amount - GAS_PER_TX,
              ![receiver] = @ + amount
             ]
          /\ UNCHANGED <<unbonded, delegated>>

\* The transition relation, which chooses one of the actions
Next ==
    \/ \E sender \in UserAddrs:
       \E amount \in Int:
        /\ amount <= MAX_UINT
        /\ \/ Delegate(sender, amount)
           \/ Unbond(sender, amount)
           \/ \E receiver \in UserAddrs:
                Transfer(sender, receiver, amount)

\* The transition relation assuming that no failure occurs
NextNoFail ==
    Next /\ ~failed /\ ~failed'

(* False invariants to debug the spec *)


===============================================================================
