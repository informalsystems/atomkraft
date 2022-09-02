---- MODULE transfer ----
EXTENDS Apalache, Integers, FiniteSets

VARIABLES
    \* @type: Str -> Int;
    balances,
    \* @type: [tag: Str, value: [wallets: Set(Str), sender: Str, receiver: Str, amount: Int]];
    action,
    \* @type: Int;
    step

WALLETS == {"Alice", "Bob"}

Init ==
    /\ balances = [wallet \in WALLETS |-> 100]
    /\ action = [tag |-> "Init", value |-> [wallets |-> WALLETS]]
    /\ step = 0

Next ==
    \E sender \in WALLETS:
    \E receiver \in WALLETS:
    \E amount \in 1..balances[sender]:
        /\ sender /= receiver
        /\ balances' = [
            balances EXCEPT
            ![sender] = @ - amount,
            ![receiver] = @ + amount
            ]
        /\ action' = [tag |-> "Transfer", value |-> [sender |-> sender, receiver |-> receiver, amount |-> amount]]
    /\ step' = step + 1

View ==
    IF action.tag = "Transfer"
    THEN action.value
    ELSE [sender |-> "", receiver |-> "", amount |-> 0]

Ex == step > 3

====
