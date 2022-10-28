--------------------------- MODULE curves ---------------------------------
EXTENDS Integers, Apalache, Sequences, Variants

VARIABLES
    \* @type: Seq($point);   
    points,
    \* @type: Int;   
    y

\* @typeAlias: point = {x:Int, y:Int};

\* @typeAlias: curve = Constant({y: Int});

\* @type: (Int) => $curve;
Constant(_y) == Variant("Constant",[y |-> _y])


===============================================================================