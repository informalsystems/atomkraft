--------------------------- MODULE cw20_vesting---------------------------------

EXTENDS Folds, curves

VARIABLES
    \* @type: Bool;
    instantiated,
    \* @type: Bool;
    stored,
    \* @type: $message;
    lastMsg,
    \* @type: $tokenInfo;
    tokenInfo,
    \* @type: Seq(Int);
    allowList,
    \* @type: Seq($balanceInfo);
    balances
(*
@typeAlias: tokenInfo = {name: Str, symbol: Str, decimals: Int};
*)

(*
@typeAlias: balanceInfo = {address: Int, amount: Int, vesting: $curve};
*)

(*
@typeAlias: message = Idle(NIL)
                    | StoreCW({sender:Int})
                    | Instantiate({sender: Int, name: Str, symbol: Str, decimals: Int, init_balances: Seq($balanceInfo)})
                    | Transfer({sender: Int, recepient: Int, amount: Int})
                    ;
*)

\* @type: () => Seq($balanceInfo);
DefaultBalances == <<[address |-> 0, amount |-> 0, vesting |-> Constant(0)]>>

Name == "TokenName"
Symbol == "TokenSymbol"
MAX_DECIMALS == 18
\* to be specified later
Amount == 10

\* @type: () => Seq($balanceInfo);
Balances == <<[address |-> 1, amount |-> 50, vesting |-> Constant(10)], [address |-> 2, amount |-> 500, vesting |-> Constant(20)]>>

\* @type: (Int, Str, Str, Int, Seq($balanceInfo)) => $message;
Instaniate(_sender, _name, _symbol, _decimals, _init_balances) ==
    Variant("Instantiate",[sender |-> _sender, name |-> _name, symbol |-> _symbol, decimals |-> _decimals,
    init_balances |-> _init_balances])
\* @type: () => $message;
Idle == Variant("Idle", "0_OF_NIL")
\* @type: (Int) => $message;
StoreCW(_sender) == Variant("StoreCW",[sender |-> _sender])
\* @type: (Int, Int, Int) => $message;
Transfer(_sender, _recepient, _amount) == Variant("Transfer", [sender |-> _sender, recepient |-> _recepient, amount |-> _amount])


\* @type: () => Bool;
Init ==
    /\ instantiated = FALSE
    /\ stored = FALSE
    /\ lastMsg = Idle

\* @type: ($message) => Bool;
ProcessInstantiate(msg) ==
    LET _var==VariantGetOrElse("Instantiate", msg, 
    [sender |-> 0, name |-> "", symbol |-> "", decimals |-> 0,
    init_balances |-> DefaultBalances])
    IN
        /\ ~instantiated
        /\ stored
        /\ instantiated' = TRUE
        /\ balances' = _var.init_balances
        /\ tokenInfo' = [name |-> _var.name, symbol |-> _var.symbol, decimals |-> _var.decimals]
        /\ allowList' = <<_var.sender>>
        /\ UNCHANGED stored

\* @type: (Int, Str, Str, Int, Seq($balanceInfo)) => Bool;
InstaniateNext(_sender, _name, _symbol, _decimals, _init_balances) ==
        LET msg == Instaniate(_sender, _name, _symbol, _decimals, _init_balances) IN
            /\ ProcessInstantiate(msg)
            /\ lastMsg' = msg

\* @type: ($message) => Bool;
ProcessStore(msg) ==
    /\ ~instantiated
    /\ ~stored
    /\ stored' = TRUE
    /\ UNCHANGED <<instantiated>>

\* @type: (Int) => Bool;
StoreNext(_sender) ==
    LET msg == StoreCW(_sender) IN
        /\ ProcessStore(msg)
        /\ lastMsg' = msg

\* @type: (Int, Int, Int) => Seq($balanceInfo);
UpdateBalance(_sender, _recepient, _amount) ==
    LET
    \* @type: (Seq($balanceInfo), $balanceInfo) => Seq($balanceInfo);
    FoldOp(a,b) == 
        IF b.address = _sender THEN Append(a, [address |-> b.address, amount |-> b.amount - _amount, vesting |-> b.vesting])
        ELSE IF b.address = _recepient THEN Append(a, [address |-> b.address, amount |-> b.amount + _amount, vesting |-> b.vesting])
        ELSE a
    IN
        ApaFoldSeqLeft(FoldOp, <<>>, balances)

\* @type: ($message) => Bool;
ProcessTransfer(_msg) ==
    LET _var==VariantGetOrElse("Transfer", _msg, [sender |-> 0, recepient |-> 0, amount |-> 0])
    IN
        /\ instantiated
        /\ stored
        /\ balances' = UpdateBalance(_var.sender, _var.recepient, _var.amount)
        /\ UNCHANGED <<instantiated, stored>>

\* @type: (Int, Int, Int) => Bool;
TransferNext(_sender, _recepient, _amount) ==
    LET msg == Transfer(_sender, _recepient, _amount) IN
        /\ ProcessTransfer(msg)
        /\ lastMsg' = msg


Next ==
    \E _sender \in 1..20, _decimals \in (1..MAX_DECIMALS), _recepient \in (1..20):
        \/ StoreNext(_sender)
        \/ InstaniateNext(_sender, Name, Symbol, _decimals, Balances)
        \/ TransferNext(_sender, _recepient, Amount)



\* (*
\* @typeAlias: trace = {
\*     instantiated:Bool,
\*     stored:Bool,
\*     admins:Set(Int),
\*     mutable:Bool,
\*     lastMsg: $message
\* };
\* *)

\* \* @type: (Seq($trace)) => Bool;
\* TraceInvBasic(trace) == ~(
\*     Len(trace) = 20
\* )

\* \* @type: (Seq($trace)) => Bool;
\* TraceInvFreeze(trace) == ~(
\*     /\ ~(Len(trace) < 20)
\*     /\ (\E i \in  DOMAIN trace: VariantTag(trace[i].lastMsg) = "Freeze")
\* )

\* \* @type: (Seq($trace)) => Bool;
\* TraceAllDifferent(trace) == ~(
\*     /\ Len(trace) = 8
\*     /\ (\A i, j \in DOMAIN trace: i < j => VariantTag(trace[i].lastMsg) /= VariantTag(trace[j].lastMsg))
\* )

===============================================================================
