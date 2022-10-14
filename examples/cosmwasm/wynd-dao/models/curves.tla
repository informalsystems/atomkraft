--------------------------- MODULE curves ---------------------------------
EXTENDS Integers, Apalache, Sequences

\* @typeAlias: Point = [x:Int, y:Int];

\* @type: () => Int;
MAX_NUM_POINTS == 100

VARIABLES
    \* @type: Int;   
    numPoints
    \* @type: Int;   
    i

\* @type: () => Point;    
Point(_x, _y) == [x |-> _x, y |->_y]
\* @type: () => [y:Int];
Constant(_y) == [y |-> _y]

\* @type: () => [points:Seq(Point)];
PieceWiseLinear(_points) == [points |-> _points]

SaturatingLinear(_points) == Len(_points)=2 /\ PieceWiseLinear(_points)

Init == 
    /\ \E _num \in 1..MAX_NUM_POINTS:
        numPoints = _num
    /\ i=0
Next ==


===============================================================================