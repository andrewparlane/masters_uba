library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.type_pkg.all;

entity delay is
    generic (DELAY: natural;
             WIDTH: natural);

    port (clk:      in  std_ulogic;
          rst:      in  std_ulogic;
          input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
          output:   out std_ulogic_vector((WIDTH - 1) downto 0));
end entity delay;

architecture synth of delay is
    signal aux: slvArray(0 to (DELAY - 1))((WIDTH - 1) downto 0);
begin
    output <= aux(DELAY - 1);

    process (clk, rst)
    begin
        if (rst = '1') then
            for i in 0 to (DELAY - 1) loop
                aux(i) <= std_ulogic_vector(to_unsigned(0, WIDTH));
            end loop;
        elsif (rising_edge(clk)) then
            aux(0) <= input;
            for i in 1 to (DELAY - 1) loop
                aux(i) <= aux(i - 1);
            end loop;
        end if;
    end process;

end architecture synth;
