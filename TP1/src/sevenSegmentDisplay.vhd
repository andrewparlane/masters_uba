library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity sevenSegmentDisplay is
    port (n:        in  unsigned(3 downto 0);
          o:        out std_logic_vector(6 downto 0));
end entity sevenSegmentDisplay;

architecture synth of sevenSegmentDisplay is
    signal auxOut: std_logic_vector(6 downto 0);
begin

    -- los señales están activa baja.
    --
    --         0
    --      -------
    --      |     |
    --    5 |     | 1
    --      |  6  |
    --      -------
    --      |     |
    --    4 |     | 2
    --      |     |
    --      -------
    --         3

    with to_integer(n) select o <=  (not "0111111") when 0,
                                    (not "0000110") when 1,
                                    (not "1011011") when 2,
                                    (not "1001111") when 3,
                                    (not "1100110") when 4,
                                    (not "1101101") when 5,
                                    (not "1111101") when 6,
                                    (not "0000111") when 7,
                                    (not "1111111") when 8,
                                    (not "1101111") when 9,
                                    (not "0000000") when others;

end architecture synth;
