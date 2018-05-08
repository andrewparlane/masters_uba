library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package type_pkg is
    type slvArray       is array (natural range <>) of std_logic_vector;
    type signedArray    is array (natural range <>) of signed;
    type unsignedArray  is array (natural range <>) of unsigned;
end package type_pkg;
