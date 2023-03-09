---- MODULE transfer ----
EXTENDS Variants, Integers

VARIABLES
    \* @type: Str -> Int;
    balances,
    \* @type: Init({wallets: Set(Str)}) | Transfer({sender: Str, receiver: Str, amount: Int});
    action,
    \* @type: Int;
    step

WALLETS == {"Alice", "Bob"}

Init ==
    /\ balances = [wallet \in WALLETS |-> 100]
    /\ action = Variant("Init", [wallets |-> WALLETS])
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
        /\ action' = Variant("Transfer", [sender |-> sender, receiver |-> receiver, amount |-> amount])
    /\ step' = step + 1

View ==
    VariantGetOrElse(
        "Transfer",
        action,
        [sender |-> "", receiver |-> "", amount |-> 0]
    )

TestAliceZero == balances["Alice"] = 0

====
