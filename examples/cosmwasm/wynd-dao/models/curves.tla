--------------------------- MODULE curves ---------------------------------
EXTENDS Integers, Apalache, Sequences, Variants


\* @typeAlias: curve = Constant({y: Int});

\* @type: (Int) => $curve;
Constant(_y) == Variant("Constant",[y |-> _y])

\* @type: ($curve) => Int;
Value(_curve) == VariantGetUnsafe("Constant", _curve).y
\* @type: ($curve, $curve) => $curve;
Combine(_curve1, _curve2) ==
    Variant("Constant",
    [y |-> VariantGetUnsafe("Constant", _curve1).y + VariantGetUnsafe("Constant", _curve2).y])
    
  
===============================================================================