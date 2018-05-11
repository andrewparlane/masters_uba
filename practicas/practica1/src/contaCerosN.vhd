-- La resulta es el numero de 0s antes de un 1
-- comenzando desde el MSb
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;

entity contaCerosN is
    generic (WIDTH: integer := 8);
    port (a: in  std_ulogic_vector((WIDTH - 1) downto 0);
          o: out unsigned(integer(ceil(log2(real(WIDTH)))) downto 0));
end entity contaCerosN;

architecture synth of contaCerosN is
    signal todoCeroHasta: std_ulogic_vector((WIDTH - 1) downto 0);

    function conta(input: std_ulogic_vector) return integer is
        variable bits: integer := 0;
    begin
        for i in input'range loop
            if (input(i) = '0') then
                bits := bits + 1;
            else
                return bits;
            end if;
        end loop;
        return input'length;
    end function conta;

begin

    o <= to_unsigned(conta(a), o'length);

end architecture synth;