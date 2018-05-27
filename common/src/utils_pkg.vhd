library ieee;
use ieee.std_logic_1164.all;
use ieee.math_real.all;

package utils_pkg is
    function min_width(max_value: natural) return natural;
    function vector_to_string(vect: std_ulogic_vector) return string;
end package utils_pkg;

package body utils_pkg is
    function min_width(max_value: natural) return natural is
    begin
        return integer(ceil(log2(real(max_value))));
    end function min_width;

    function vector_to_string(vect: std_ulogic_vector) return string is
        variable str: string(1 to vect'length);
    begin
        for i in vect'range loop
            str(i+1) := '1' when vect(vect'length - i - 1) else '0';
        end loop;
        return str;
    end function vector_to_string;
end package body utils_pkg;
