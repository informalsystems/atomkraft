--------------------------- MODULE cw1_whitelist---------------------------------

EXTENDS Integers, Apalache, Sequences, FiniteSets, Variants

VARIABLES
    \* @type: $state;
    state,
    \* @type: $message;
    lastMsg,
    \* @type: Bool;
    success


(*
@typeAlias: message = Instantiate({admins: Set(Int), mutable: Bool})
                    | Idle(UNIT)
                    | GetCanExecute({sender:Int})
                    | GetAdminList(UNIT)
                    | StoreCW({sender:Int})
                    | Execute({sender:Int})
                    | Freeze({sender:Int})
                    | UpdateAdmins({sender:Int, admins: Set(Int)})
                    ;
*)

\* @type: (Set(Int), Bool) => $message;
Instantiate(_admins, _mutable) == Variant("Instantiate",[admins |-> _admins, mutable |-> _mutable])
\* @type: () => $message;
Idle == Variant("Idle", UNIT)
\* @type: (Int) => $message;
GetCanExecute(_sender) == Variant("GetCanExecute",[sender |-> _sender])
\* @type: () => $message;
GetAdminList == Variant("GetAdminList",UNIT)
\* @type: (Int) => $message;
StoreCW(_sender) == Variant("StoreCW",[sender |-> _sender])
\* @type: (Int) => $message;
Execute(_sender) == Variant("Execute",[sender |-> _sender])
\* @type: (Int) => $message;
Freeze(_sender) == Variant("Freeze",[sender |-> _sender])
\* @type: (Int, Set(Int)) => $message;
UpdateAdmins(_sender, _admins) == Variant("UpdateAdmins",[sender |-> _sender, admins |-> _admins])

(*
@typeAlias: state = Empty(UNIT)
                  | Stored(UNIT)
                  | Instantiated({admins: Set(Int), mutable: Bool})
                  ;
*)

\* @type: () => $state;
EmptyState == Variant("Empty",UNIT)
\* @type: () => $state;
StoredState == Variant("Stored",UNIT)
\* @type: ({admins: Set(Int), mutable: Bool}) => $state;
InstantiatedState(_cw_state) == Variant("Instantiated", _cw_state)

\* @type: () => Set(Bool);
MutableSet == {TRUE,FALSE}


(******************)
(*   Constants    *)
(******************)

\* @type: () => Int;
ADMIN_SET_SIZE == 10


(******************)
(* UTIL operators *)
(******************)

\* @type: (Int) => Bool;
CanExecute(_account) ==
    IF VariantTag(state) /= "Instantiated" THEN FALSE ELSE
    LET _state==VariantGetUnsafe("Instantiated", state) IN
        _account \in _state.admins


\* @type: (Int) => Bool;
CanModify(_account) ==
    IF VariantTag(state) /= "Instantiated" THEN FALSE ELSE
    LET _state==VariantGetUnsafe("Instantiated", state) IN
        /\ _account \in _state.admins
        /\ _state.mutable


(******************)
(* PROC operators *)
(******************)

\* @type: ($message) => Bool;
StoreProcess(msg) ==
    IF VariantTag(state) = "Empty" THEN
        /\ state' = StoredState
        /\ success' = TRUE
    ELSE
        /\ UNCHANGED state
        /\ success' = FALSE


\* @type: ($message) => Bool;
InstantiateProcess(msg) ==
    IF VariantTag(state) = "Stored" THEN
        \* IF VariantTag(msg) /= "Instantiate" THEN FALSE ELSE
        LET _var==VariantGetUnsafe("Instantiate", msg) IN
            /\ state' = InstantiatedState(_var)
            /\ success' = TRUE
    ELSE
        /\ UNCHANGED state
        /\ success' = FALSE


\* @type: ($message) => Bool;
ExecuteProcess(msg) ==
    IF VariantTag(state) = "Instantiated" THEN
        \* IF VariantTag(msg) /= "Execute" THEN FALSE ELSE
        LET _var==VariantGetUnsafe("Execute", msg) IN
            /\ CanExecute(_var.sender)
            /\ UNCHANGED state
            /\ success' = TRUE
    ELSE
        /\ UNCHANGED state
        /\ success' = FALSE


\* @type: ($message) => Bool;
FreezeProcess(msg) ==
    IF VariantTag(state) = "Instantiated" THEN
        \* IF VariantTag(msg) /= "Freeze" THEN FALSE ELSE
        LET _var==VariantGetUnsafe("Freeze", msg) IN
        LET _state==VariantGetUnsafe("Instantiated", state) IN
            /\ CanModify(_var.sender)
            /\ state' = InstantiatedState([_state EXCEPT !.mutable = FALSE])
            /\ success' = TRUE
    ELSE
        /\ UNCHANGED state
        /\ success' = FALSE


\* @type: ($message) => Bool;
UpdateAdminsProcess(msg) ==
    IF VariantTag(state) = "Instantiated" THEN
        \* IF VariantTag(msg) /= "UpdateAdmins" THEN FALSE ELSE
        LET _var==VariantGetUnsafe("UpdateAdmins", msg) IN
        LET _state==VariantGetUnsafe("Instantiated", state) IN
            /\ CanModify(_var.sender)
            /\ state' = InstantiatedState([_state EXCEPT !.admins = _var.admins])
            /\ success' = TRUE
    ELSE
        /\ UNCHANGED state
        /\ success' = FALSE


\* @type: () => Bool;
GetAdminListProcess ==
    /\ UNCHANGED state
    /\ success' = (VariantTag(state) = "Instantiated")


\* @type: ($message) => Bool;
GetCanExecuteProcess(msg) ==
    IF VariantTag(state) = "Instantiated" THEN
        \* IF VariantTag(msg) /= "GetCanExecute" THEN FALSE ELSE
        LET _var==VariantGetUnsafe("GetCanExecute", msg) IN
            /\ UNCHANGED state
            /\ success' = TRUE
    ELSE
        /\ UNCHANGED state
        /\ success' = FALSE


(******************)
(* NEXT operators *)
(******************)

\* @type: (Int) => Bool;
StoreNext(_sender) ==
    LET msg == StoreCW(_sender) IN
        /\ StoreProcess(msg)
        /\ lastMsg' = msg


\* @type: (Int) => Bool;
InstantiateNext(_sender) ==
    \E _m \in MutableSet, _admins \in SUBSET (1..ADMIN_SET_SIZE):
        LET msg == Instantiate(_admins, _m) IN
            /\ InstantiateProcess(msg)
            /\ lastMsg' = msg


\* @type: (Int) => Bool;
ExecuteNext(_sender) ==
    LET msg == Execute(_sender) IN
        /\ ExecuteProcess(msg)
        /\ lastMsg' = msg


\* @type: (Int) => Bool;
FreezeNext(_sender) ==
    LET msg == Freeze(_sender) IN
        /\ FreezeProcess(msg)
        /\ lastMsg' = msg


\* @type: (Int) => Bool;
UpdateAdminsNext(_sender) ==
    \E _admins \in SUBSET (1..ADMIN_SET_SIZE):
        LET msg == UpdateAdmins(_sender, _admins) IN
            /\ UpdateAdminsProcess(msg)
            /\ lastMsg' = msg


\* @type: (Int) => Bool;
GetAdminListNext(_sender) ==
    LET msg == GetAdminList IN
        /\ GetAdminListProcess
        /\ lastMsg' = msg


\* @type: (Int) => Bool;
GetCanExecuteNext(_sender) ==
    LET msg == GetCanExecute(_sender) IN
        /\ GetCanExecuteProcess(msg)
        /\ lastMsg' = msg


(******************)
(*   INIT & NEXT  *)
(******************)

Init ==
    /\ state = EmptyState
    /\ lastMsg = Idle
    /\ success = TRUE


Next ==
    \E _sender \in 1..ADMIN_SET_SIZE:
        \/ StoreNext(_sender)
        \/ InstantiateNext(_sender)
        \/ ExecuteNext(_sender)
        \/ FreezeNext(_sender)
        \/ UpdateAdminsNext(_sender)
        \/ GetAdminListNext(_sender)
        \/ GetCanExecuteNext(_sender)


(******************)
(*   Invariants   *)
(******************)

(*
@typeAlias: trace = {
    state: $state,
    lastMsg: $message,
    success: Bool
};
*)

\* @type: (Seq($trace)) => Bool;
TraceInvBasic(trace) == ~(
    Len(trace) = 20
)

\* @type: (Seq($trace)) => Bool;
TraceInvFreeze(trace) == ~(
    /\ ~(Len(trace) < 20)
    /\ (\E i \in  DOMAIN trace: VariantTag(trace[i].lastMsg) = "Freeze")
)

\* @type: (Seq($trace)) => Bool;
TraceAllDifferent(trace) == ~(
    /\ Len(trace) = 8
    /\ (\A i, j \in DOMAIN trace: i < j => VariantTag(trace[i].lastMsg) /= VariantTag(trace[j].lastMsg))
)

\* @type: (Seq($trace)) => Bool;
AllSuccess(trace) == ~(
    /\ Len(trace) > 9
    /\ (\A i \in  DOMAIN trace: trace[i].success)
)

\* @type: (Seq($trace)) => Bool;
InterestingFailures(trace) == ~(
    /\ Len(trace) > 9
    /\ trace[3].success
    /\ VariantTag(trace[3].lastMsg) = "Instantiate"
    /\ (\E i \in  DOMAIN trace: ~trace[i].success)
)


(******************)
(*     Views      *)
(******************)

\* @type: () => $message;
View ==
    lastMsg


===============================================================================
