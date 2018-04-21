library ieee;
use ieee.std_logic_1164.all;
use ieee.math_real.all;

package utils is
    function min_width(max_value: natural) return natural;
end package utils;

package body utils is
    function min_width(max_value: natural) return natural is
    begin
        return integer(ceil(log2(real(max_value))));
    end function min_width;
end package body utils;
