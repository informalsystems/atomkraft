--------------------------- MODULE cw1_whitelist---------------------------------

EXTENDS Integers, Apalache, Sequences, FiniteSets, Variants

VARIABLES
    \* @type: Bool;
    instantiated,
    \* @type: Bool;
    stored,
     \* @type: Set(Int);
    admins,
    \* @type: Bool;
    mutable,
    \* @type: $message;
    lastMsg

\* @type: () => Int;
ADMIN_LEN == 10
\* @type: () => Int;
ADMIN_SET_SIZE == 100

AdminLen(_admins) == Cardinality(_admins) <= ADMIN_LEN


(*
@typeAlias: message = Instantiate({admins: Set(Int), mutable: Bool})
                    | Idle(NIL)
                    | GetCanExecute({sender:Int})
                    | GetAdminList(NIL)
                    | StoreCW({sender:Int})
                    | Execute({sender:Int})
                    | Freeze({sender:Int})
                    | UpdateAdmins({sender:Int})
                    ;
*)

\* @type: (Set(Int), Bool) => $message;
Instaniate(_admins, _mutable) == Variant("Instantiate",[admins |-> _admins, mutable |-> _mutable])
\* @type: () => $message;
Idle == Variant("Idle", "0_OF_NIL")
\* @type: (Int) => $message;
GetCanExecute(_sender) == Variant("GetCanExecute",[sender |-> _sender])
\* @type: () => $message;
GetAdminList == Variant("GetAdminList","0_OF_NIL")
\* @type: (Int) => $message;
StoreCW(_sender) == Variant("StoreCW",[sender |-> _sender])
\* @type: (Int) => $message;
Execute(_sender) == Variant("Execute",[sender |-> _sender])
\* @type: (Int) => $message;
Freeze(_sender) == Variant("Freeze",[sender |-> _sender])
\* @type: (Int) => $message;
UpdateAdmins(_sender) == Variant("UpdateAdmins",[sender |-> _sender])

Init ==
    /\ mutable = FALSE
    /\ admins \in SUBSET (1..ADMIN_SET_SIZE)
    /\ instantiated = FALSE
    /\ stored = FALSE
    /\ lastMsg = Idle

\* @type: () => Set(Bool);
MutableSet == {TRUE,FALSE}

ProcessInstantiate(msg) ==
    LET _var==VariantGetOrElse("Instantiate", msg, [admins |-> {0}, mutable |-> FALSE]) IN
        /\ ~instantiated
        /\ stored
        /\ mutable' = _var.mutable
        /\ admins' = _var.admins
        /\ instantiated' = TRUE
        /\ UNCHANGED stored

InstaniateNext(_sender) ==
    /\ \E _m \in MutableSet:
        LET msg == Instaniate(admins, _m) IN
            /\ ProcessInstantiate(msg)
            /\ lastMsg' = msg

CanExecute(_sender) == _sender \in admins

ProcessGetCanExecute(msg) ==
    LET _var==VariantGetOrElse("GetCanExecute", msg, [sender |-> 0]) IN
    /\ instantiated
    /\ stored
    /\ CanExecute(_var.sender)
    /\ UNCHANGED<<admins, mutable, instantiated, stored>>

GetCanExecuteNext(_sender) ==
    LET msg == GetCanExecute(_sender) IN
        /\ ProcessGetCanExecute(msg)
        /\ lastMsg' = msg

ProcessGetAdminList ==
    /\ instantiated
    /\ stored
    /\ UNCHANGED<<admins, mutable, instantiated, stored>>

GetAdminListNext(_sender) ==
    LET msg == GetAdminList IN
        /\ ProcessGetAdminList
        /\ lastMsg' = msg
    

CanModify(_sender) ==
    /\ _sender \in admins
    /\ mutable

ProcessExecute(msg) ==
    LET _var==VariantGetOrElse("Execute", msg, [sender |-> 0]) IN
        /\ instantiated
        /\ stored
        /\ CanExecute(_var.sender)
        /\ UNCHANGED<<admins, mutable, instantiated, stored>>

ExecuteNext(_sender) ==
    LET msg == Execute(_sender) IN
        /\ ProcessExecute(msg)
        /\ lastMsg' = msg

ProcessFreeze(msg) ==
    LET _var==VariantGetOrElse("Freeze", msg, [sender |-> 0]) IN
        /\ instantiated
        /\ stored
        /\ CanModify(_var.sender)
        /\ mutable' = FALSE
        /\ UNCHANGED<<admins, instantiated, stored>>

FreezeNext(_sender) ==
    LET msg == Freeze(_sender) IN
        /\ ProcessFreeze(msg)
        /\ lastMsg' = msg

ProcessUpdateAdmins(msg) ==
    LET _var==VariantGetOrElse("UpdateAdmins", msg, [sender |-> 0]) IN
        /\ instantiated
        /\ stored
        /\ mutable
        /\ CanModify(_var.sender)
        /\ admins' \in SUBSET (1..ADMIN_SET_SIZE)
        /\ UNCHANGED<<mutable, instantiated, stored>>

UpdateAdminsNext(_sender) ==
    LET msg == UpdateAdmins(_sender) IN
        /\ ProcessUpdateAdmins(msg)
        /\ lastMsg' = msg

ProcessStore(msg) ==
    /\ ~instantiated
    /\ ~stored
    /\ stored' = TRUE
    /\ UNCHANGED <<instantiated, mutable, admins>>

StoreNext(_sender) ==
    LET msg == StoreCW(_sender) IN
        /\ ProcessStore(msg)
        /\ lastMsg' = msg

Next ==
    \E _sender \in 1..20:
        \/ StoreNext(_sender)
        \/ InstaniateNext(_sender)
        \/ ExecuteNext(_sender)
        \/ FreezeNext(_sender)
        \/ UpdateAdminsNext(_sender)
        \/ GetAdminListNext(_sender)
        \/ GetCanExecuteNext(_sender)



(*
@typeAlias: trace = {
    instantiated:Bool,
    stored:Bool,
    admins:Set(Int),
    mutable:Bool,
    lastMsg: $message
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

===============================================================================
