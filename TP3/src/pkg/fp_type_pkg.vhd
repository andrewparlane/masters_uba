library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package fp_type_pkg is

    type RoundingMode is
    (
        RoundingMode_NEG_INF,
        RoundingMode_POS_INF,
        RoundingMode_0,
        RoundingMode_NEAREST
    );

    type fpNumType is
    (
        fpNumType_NORMAL,
        fpNumType_ZERO,
        fpNumType_DENORMAL,
        fpNumType_NaN,
        fpNumType_INFINITY
    );

end package fp_type_pkg;
