--------------------------- MODULE counter ---------------------------------

EXTENDS Integers, Variants, Sequences

\* @type: () => Int;
MAX_STEP == 20
\* @type: () => Int;
MAX_ACCOUNTS == 3

(*
@typeAlias: message = Instantiate({sender: Int, count: Int})
                    | Reset({sender: Int, count: Int})
                    | Increment({sender: Int})
                    | GetCount({sender: Int})
                    | StoreCwContract({sender: Int})
                    ;
*)
typedef == TRUE


VARIABLES
    \* @type: Int;
    count,
    \* @type: Int;
    owner,
    \* @type: Bool;
    instantiated,
    \* @type: $message;
    last_msg,
    \* @type: Seq($message);
    messages,
    \* @type: Int;
    stepCount


\* @type: (Int, Int) => $message;
Instaniate(_sender, _count) == Variant("Instantiate", [sender |-> _sender, count |-> _count])
\* @type: (Int, Int) => $message;
Reset(_sender, _count) == Variant("Reset", [sender |-> _sender, count |-> _count])
\* @type: (Int) => $message;
Increment(_sender) == Variant("Increment", [sender |-> _sender])
\* @type: (Int) => $message;
GetCount(_sender) == Variant("GetCount", [sender |-> _sender])
\* @type: (Int) => $message;
StoreCW(_sender) == Variant("StoreCwContract", [sender |-> _sender])


\* @type: () => Set(Int);
ACCOUNTS == 1..MAX_ACCOUNTS

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
    \E instantiate_count \in 0..100:
        LET msg == Instaniate(_sender, instantiate_count) IN
        LET _msg == VariantGetUnsafe("Instantiate", msg) IN
        /\ ProcessInstantiate(_msg.sender, _msg.count)
        /\ last_msg' = msg

ProcessReset(_owner, _sender, _count) ==
    /\ instantiated
    /\ owner = _sender
    /\ count' = _count
    /\ UNCHANGED<<owner, instantiated>>

ResetNext(_sender) ==
    \E reset_count \in 0..100:
        LET msg == Reset(_sender, reset_count) IN
        LET _msg == VariantGetUnsafe("Reset", msg) IN
        /\ ProcessReset(owner, _msg.sender, _msg.count)
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

MaxLength == stepCount < MAX_STEP

View == <<owner,VariantTag(last_msg)>>
===============================================================================
