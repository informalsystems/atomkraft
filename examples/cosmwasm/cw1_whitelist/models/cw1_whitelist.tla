--------------------------- MODULE cw1_whitelist---------------------------------

EXTENDS Integers, Apalache, Sequences

VARIABLES
    \* @type: Bool;
    instantiated,
    \* @type: Bool;
    stored,
    \* @type: Bool;
    updating_admins,
     \* @type: Set(Int);
    admins,
    \* @type: Bool;
    mutable,
    \* @type: [name:Str, cnt: Int];
    last_msg,
    \* @type: Seq([name:Str, cnt: Int]);
    messages,
    \* @type: Int;
    stepCount,
    \* @type: Int;
    adminLen

\* @type: () => Str;
INSTANTIATE == "instantiate"
\* @type: () => Str;
EXECUTE == "execute"
\* @type: () => Str;
FREEZE == "freeze"
\* @type: () => Str;
UPDATE_ADMINS == "update_admins"
\* @type: () => Str;
GET_ADMIN_LIST == "get_admin_list"
\* @type: () => Str;
GET_CAN_EXECUTE == "get_can_execute"
\* @type: () => Str;
IDLE == "idle"
\* @type: () => Str;
STORE_CW == "store_cw_contract"

\* @type: (Set(Int), Bool) => [name: Str, admins: Set(Int), mutable: Bool];
Instaniate(_admins, _mutable) == [name |-> INSTANTIATE, admins |-> _admins, mutable |-> _mutable]
\* @type: () => [name: Str];
Idle == [name |-> IDLE]

GetCanExecute(_sender) == [name |->GET_CAN_EXECUTE, sender |-> _sender]

\* @type: () => [name: Str];
GetAdminList == [name |->GET_ADMIN_LIST]

StoreCW(_sender) == [name |-> STORE_CW, sender |-> _sender]
Execute(_sender) == [name |-> EXECUTE, sender |-> _sender]
Freeze(_sender) == [name |-> FREEZE, sender |-> _sender]
UpdateAdmins(_sender) == [name |-> UPDATE_ADMINS, sender |-> _sender]

Init ==
    /\ mutable = FALSE
    /\ admins = {}
    /\ instantiated = FALSE
    /\ stored = FALSE
    /\ updating_admins = FALSE
    /\ messages = <<>>
    /\ stepCount = 1
    /\ adminLen = 0
    /\ last_msg = Idle

\* @type: () => Set(Bool);
MutableSet == {TRUE,FALSE}

ProcessInstantiate(_admins, _mutable) ==
    /\ ~instantiated
    /\ stored
    /\ mutable' = _mutable
    /\ admins' = _admins
    /\ instantiated' = TRUE
    /\ UNCHANGED stored

InstaniateNext(_sender) ==
    /\ \E _m \in MutableSet:
        LET msg == Instaniate(admins, _m) IN
        /\ ProcessInstantiate(msg.admins, msg.mutable)
        /\ last_msg' = msg
        /\ UNCHANGED <<adminLen, updating_admins>>

CanExecute(_sender) == _sender \in admins

ProcessGetCanExecute(_sender) ==
    /\ instantiated
    /\ stored
    /\ CanExecute(_sender)
    /\ UNCHANGED<<admins, mutable, instantiated, stored>>

GetCanExecuteNext(_sender) ==
    LET msg == GetCanExecute(_sender) IN
        /\ ProcessGetCanExecute(_sender)
        /\ last_msg' = msg
     /\ UNCHANGED <<adminLen, updating_admins>>

ProcessGetAdminList ==
    /\ instantiated
    /\ stored
    /\ UNCHANGED<<admins, mutable, instantiated, stored>>

GetAdminListNext(_sender) ==
    LET msg == GetAdminList IN
        /\ ProcessGetAdminList
        /\ last_msg' = msg
        /\ UNCHANGED <<adminLen, updating_admins>>
    


CanModify(_sender) ==
    /\ _sender \in admins
    /\ mutable

ProcessExecute(_sender) ==
    /\ instantiated
    /\ stored
    /\ CanExecute(_sender)
    /\ UNCHANGED<<admins, mutable, instantiated, stored>>

ExecuteNext(_sender) ==
    LET msg == Execute(_sender) IN
        /\ ProcessExecute(msg.sender)
        /\ last_msg' = msg
        /\ UNCHANGED <<adminLen, updating_admins>>

ProcessFreeze(_sender) ==
    /\ instantiated
    /\ stored
    /\ CanModify(_sender)
    /\ mutable' = FALSE
    /\ UNCHANGED<<admins, instantiated, stored>>

FreezeNext(_sender) ==
    LET msg == Freeze(_sender) IN
        /\ ProcessFreeze(msg.sender)
        /\ last_msg' = msg
        /\ UNCHANGED <<adminLen, updating_admins>>

ProcessUpdateAdmins(_sender) ==
    /\ instantiated
    /\ stored
    /\ mutable
    /\ CanModify(_sender)
    /\ admins' = {}
    /\ adminLen' = 0
    /\ updating_admins' = TRUE
    /\ UNCHANGED<<mutable, instantiated, stored>>

UpdateAdminsNext(_sender) ==
    LET msg == UpdateAdmins(_sender) IN
        /\ ProcessUpdateAdmins(msg.sender)
        /\ last_msg' = msg

ProcessStore(_sender) ==
    /\ ~instantiated
    /\ ~stored
    /\ stored' = TRUE
    /\ UNCHANGED <<instantiated, mutable, adminLen, admins, updating_admins>>

StoreNext(_sender) ==
    LET msg == StoreCW(_sender) IN
        /\ ProcessStore(msg.sender)
        /\ last_msg' = msg

StartNewMessage ==
    /\ adminLen = 10
    /\ ~updating_admins
    /\ \E _sender \in 1..20:
        \/ StoreNext(_sender)
        \/ InstaniateNext(_sender)
        \/ ExecuteNext(_sender)
        \/ FreezeNext(_sender)
        \/ UpdateAdminsNext(_sender)
        \/ GetAdminListNext(_sender)
        \/ GetCanExecuteNext(_sender)
    /\ messages' = Append(messages, last_msg)
    /\ stepCount' = stepCount + 1

FinishUpdateAdmins ==
    /\ adminLen = 10
    /\ updating_admins
    /\ updating_admins' = FALSE
    /\ UNCHANGED <<messages, last_msg, stepCount, mutable, adminLen, admins, instantiated, stored>>

NextMessage ==
    FinishUpdateAdmins \/ StartNewMessage

CreateAdminSet ==
    /\ adminLen < 10
    /\ ~updating_admins
    /\ adminLen' = adminLen + 1
    /\ last_msg' = Idle
    /\ \E _id \in 1..100:
        /\ _id \notin admins
        /\ admins' = admins \union {_id}
    /\ UNCHANGED <<messages, mutable, stepCount, instantiated, stored, updating_admins>>

UpdateAdminSet ==
    /\ adminLen < 10
    /\ updating_admins
    /\ adminLen' = adminLen + 1
    /\ last_msg' = Idle
    /\ \E _id \in 1..100:
        /\ _id \notin admins
        /\ admins' = admins \union {_id}
    /\ UNCHANGED <<messages, mutable, stepCount, instantiated, stored, updating_admins>>


Next== NextMessage \/ CreateAdminSet \/ UpdateAdminSet
    

Inv == stepCount < 20
===============================================================================
