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
    balances,
    \* @type: Seq($vestingInfo);
    vestingSchedules
(*
@typeAlias: tokenInfo = {name: Str, symbol: Str, decimals: Int};
*)

(*
@typeAlias: balanceInfo = {address: Int, amount: Int};
*)

(*
@typeAlias: vestingInfo = {address: Int, vesting: $curve};
*)

(*
@typeAlias: message = Idle(NIL)
                    | StoreCW({sender:Int})
                    | Instantiate({sender: Int, name: Str, symbol: Str, decimals: Int, init_balances: Seq($balanceInfo)})
                    | Transfer({sender: Int, recepient: Int, amount: Int})
                    | TransferVesting({sender: Int, recepient: Int, amount: Int, schedule: $curve})
                    ;
*)

\* @type: () => Seq($balanceInfo);
DefaultBalances == <<[address |-> 0, amount |-> 0]>>

Name == "TokenName"
Symbol == "TokenSymbol"
MAX_DECIMALS == 18
\* to be specified later
Amount == 10

\* @type: () => Seq($balanceInfo);
Balances == <<[address |-> 1, amount |-> 50], [address |-> 2, amount |-> 500]>>

\* @type: (Int) => Bool;
isAllowed(_sender) == 
    LET test(x) == x = _sender IN
        Len(SelectSeq(allowList, test)) = 1


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
\* @type: (Int, Int, Int, $curve) => $message;
TransferVesting(_sender, _recepient, _amount, _schedule) ==
    Variant("TransferVesting", [sender |-> _sender, recepient |-> _recepient, amount |-> _amount, schedule |-> _schedule])

\* @type: () => Bool;
Init ==
    /\ instantiated = FALSE
    /\ stored = FALSE
    /\ lastMsg = Idle
    /\ vestingSchedules = <<>>
    /\ tokenInfo = [name |-> "", symbol |-> "", decimals |-> 0]
    /\ allowList = <<>>
    /\ balances = <<>>

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
        /\ UNCHANGED <<stored, vestingSchedules>>

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
    /\ UNCHANGED <<instantiated, allowList, balances, tokenInfo, vestingSchedules>>

\* @type: (Int) => Bool;
StoreNext(_sender) ==
    LET msg == StoreCW(_sender) IN
        /\ ProcessStore(msg)
        /\ lastMsg' = msg

\* @type: (Int) => $curve;
VestingSchedule(_address) ==
    LET 
    \* @type: ($vestingInfo) => Bool;
    test(_elem) == _elem.address = _address 
    IN 
    SelectSeq(vestingSchedules, test)[0].vesting

\* @type: (Int, Int, Seq($balanceInfo)) => Seq($balanceInfo);
DeductCoins(_sender, _amount, _balances) ==
    LET
    \* @type: (Seq($balanceInfo), $balanceInfo) => Seq($balanceInfo);
    FoldOp(a,b) == 
        IF (b.address = _sender) /\ (b.amount - _amount > Value(VestingSchedule(_sender))) THEN 
            Append(a, [address |-> b.address, amount |-> b.amount - _amount])
        ELSE a
    IN
        ApaFoldSeqLeft(FoldOp, <<>>, _balances)

\* @type: (Int, Int, Seq($balanceInfo)) => Seq($balanceInfo);
AddBalance(_addr, _amount, _balances) ==
    LET
    \* @type: (Seq($balanceInfo), $balanceInfo) => Seq($balanceInfo);
    FoldOp(a,b) == 
        IF (b.address = _addr) THEN 
            Append(a, [address |-> b.address, amount |-> b.amount + _amount])
        ELSE a
    IN
        ApaFoldSeqLeft(FoldOp, <<>>, _balances)

\* @type: (Int, $curve) => Seq($vestingInfo);
UpdateVestingInfo(_recepient, _schedule) ==
    LET
    \* @type: (Seq($vestingInfo), $vestingInfo) => Seq($vestingInfo);
    FoldOp(a,b) == 
        IF (b.address = _recepient) THEN 
            Append(a, [address |-> b.address, vesting |-> Combine(b.vesting, _schedule)])
        ELSE a
    IN
        ApaFoldSeqLeft(FoldOp, <<>>, vestingSchedules)

\* @type: ($message) => Bool;
ProcessTransfer(_msg) ==
    LET 
        _var==VariantGetOrElse("Transfer", _msg, [sender |-> 0, recepient |-> 0, amount |-> 0])
        new_balance == DeductCoins(_var.sender, _var.amount, balances)
        new_balance1 == AddBalance(_var.recepient, _var.amount, new_balance)
    IN
        /\ instantiated
        /\ stored
        /\ balances' = new_balance1
        /\ UNCHANGED <<instantiated, stored, tokenInfo>>

\* @type: (Int, Int, Int) => Bool;
TransferNext(_sender, _recepient, _amount) ==
    LET msg == Transfer(_sender, _recepient, _amount) IN
        /\ ProcessTransfer(msg)
        /\ lastMsg' = msg
        /\ UNCHANGED <<vestingSchedules, allowList>>

\* @type: ($message) => Bool;
ProcessTransferVesting(_msg) ==
    LET _var==VariantGetOrElse("TransferVesting", _msg, [sender |-> 0, recepient |-> 0, amount |-> 0, schedule |-> Constant(0)])
    IN
        /\ instantiated
        /\ stored
        /\ _var.amount > 0
        /\ isAllowed(_var.sender)
        /\ vestingSchedules' = UpdateVestingInfo(_var.recepient, _var.schedule)
        /\ LET msg == Transfer(_var.sender, _var.recepient, _var.amount) IN  ProcessTransfer(msg)
        /\ UNCHANGED <<allowList>>

\* @type: (Int, Int, Int, $curve) => Bool;
TransferVestingNext(_sender, _recepient, _amount, _schedule) ==
    LET msg == TransferVesting(_sender, _recepient, _amount, _schedule) IN
        /\ ProcessTransferVesting(msg)
        /\ lastMsg' = msg


Next ==
    \E _sender \in 1..20, _decimals \in (1..MAX_DECIMALS), _recepient \in (1..20):
        \/ StoreNext(_sender)
        \/ InstaniateNext(_sender, Name, Symbol, _decimals, balances)
        \/ TransferNext(_sender, _recepient, Amount)
        \/ TransferVestingNext(_sender, _recepient, Amount, Constant(4))



(*
@typeAlias: trace = {
    instantiated: Bool,
    stored: Bool,
    lastMsg :$message,
    tokenInfo: $tokenInfo,
    allowList: Seq(Int),
    balances: Seq($balanceInfo),
    vestingSchedules: Seq($vestingInfo)
};
*)

\* @type: (Seq($trace)) => Bool;
TraceInvBasic(trace) == ~(
    Len(trace) = 10
)

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
