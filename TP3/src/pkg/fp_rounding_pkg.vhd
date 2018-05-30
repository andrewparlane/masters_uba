library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package fp_rounding_pkg is

    type RoundingMode is
    (
        RoundingMode_NEG_INF,
        RoundingMode_POS_INF,
        RoundingMode_0,
        RoundingMode_NEAREST
    );

end package fp_rounding_pkg;
