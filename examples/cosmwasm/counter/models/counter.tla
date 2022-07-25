--------------------------- MODULE counter ---------------------------------

EXTENDS Integers, Apalache, Sequences


\* CONSTANTS
\*     \* @type: Int;
\*     MAX_STEP,
\*     \* @type: Int;
\*     MAX_ACCOUNTS

\* @type: () => Int;
MAX_STEP == 20
\* @type: () => Int;
MAX_ACCOUNTS == 3

VARIABLES
    \* @type: Int;
    count,
    \* @type: Int;
    owner,
    \* @type: Bool;
    instantiated,
    \* @type: [name:Str, cnt: Int];
    last_msg,
    \* @type: Seq([name:Str, cnt: Int]);
    messages,
    \* @type: Int;
    stepCount

\* @type: () => Str;
INSTANTIATE == "instantiate"
\* @type: () => Str;
RESET == "reset"
\* @type: () => Str;
INCREMENT == "increment"
\* @type: () => Str;
GET_COUNT == "get_count"
\* @type: () => Str;
STORE_CW == "store_cw_contract"

\* @type: (Int, Int) => [name: Str, sender: Int, cnt: Int];
Instaniate(_sender, val) == [name |-> INSTANTIATE, sender |-> _sender, cnt |-> val]
\* @type: (Int, Int) => [name: Str, sender: Int, cnt: Int];
Reset(_sender, val) == [name |-> RESET, sender |-> _sender, cnt |-> val]
\* @type: (Int) => [name: Str, sender: Int];
Increment(_sender) == [name |-> INCREMENT, sender |-> _sender]
\* @type: (Int) => [name: Str, sender: Int];
GetCount(_sender) == [name |-> GET_COUNT, sender |-> _sender]
\* @type: (Int) => [name: Str, sender: Int];
StoreCW(_sender) == [name |-> STORE_CW, sender |-> _sender]


\* @type: () => Set(Int);
ACCOUNTS == 0..(MAX_ACCOUNTS-1)

Init ==
    /\ count = 0
    /\ owner = 0
    /\ instantiated = FALSE
    /\ \E _sender \in ACCOUNTS: last_msg = StoreCW(_sender)
    /\ messages = <<>>
    /\ stepCount = 1

ProcessInstantiate(_sender, _count) ==
    /\ ~instantiated
    /\ count' = _count
    /\ owner' = _sender
    /\ instantiated' = TRUE

InstaniateNext(_sender) ==
    \E instantiate_cnt \in 0..100:
        LET msg == Instaniate(_sender, instantiate_cnt) IN
        /\ ProcessInstantiate(msg.sender, msg.cnt)
        /\ last_msg' = msg

ProcessReset(_owner, _sender, _count) ==
    /\ instantiated
    /\ owner = _sender
    /\ count' = _count
    /\ UNCHANGED<<owner, instantiated>>

ResetNext(_sender) ==
    \E reset_cnt \in 0..100:
        LET msg == Reset(_sender, reset_cnt) IN
        /\ ProcessReset(owner, msg.sender, msg.cnt)
        /\ last_msg' = msg

ProcessIncrement ==
    /\ instantiated
    /\ count' = count + 1
    /\ UNCHANGED<<owner, instantiated>>

IncrementNext(_sender) ==
    LET msg == Increment(_sender) IN
        /\ ProcessIncrement
        /\ last_msg' = msg

ProcessGetCount ==
    /\ instantiated
    /\ UNCHANGED<<count, owner, instantiated>>

GetCountNext(_sender) ==
    LET msg == GetCount(_sender) IN
        /\ ProcessGetCount
        /\ last_msg' = msg

Next==
    /\ \E _sender \in ACCOUNTS:
        \/ InstaniateNext(_sender)
        \/ ResetNext(_sender)
        \/ IncrementNext(_sender)
        \/ GetCountNext(_sender)
    /\ messages' = Append(messages, last_msg)
    /\ stepCount' = stepCount + 1

Inv == stepCount < MAX_STEP

View == <<count,owner,last_msg>>
View2 == last_msg.name
===============================================================================
