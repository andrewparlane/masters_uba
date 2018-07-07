library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity counter is
    generic (WIDTH: natural;
             MAX: natural);
    port (clk:      in  std_ulogic;
          en:       in  std_ulogic;
          rst:      in  std_ulogic;
          load:     in  std_ulogic;
          loadData: in  unsigned((WIDTH - 1) downto 0);
          count:    out unsigned((WIDTH - 1) downto 0);
          atZero:   out std_ulogic;
          atMax:    out std_ulogic);
end entity counter;

architecture synth of counter is
    signal countAux: unsigned((WIDTH - 1) downto 0) := (others => '0');
begin

    process (clk, rst)
    begin
        -- asíncrono reset
        if (rst = '1') then
            countAux <= (others => '0');
        elsif (rising_edge(clk)) then
            if (en = '1') then
                if (load = '1') then
                    countAux <= loadData;
                else
                    if (countAux = to_unsigned(MAX, WIDTH)) then
                        countAux <= (others => '0');
                    else
                        countAux <= countAux + to_unsigned(1, WIDTH);
                    end if;
                end if;
            end if;
        end if;
    end process;

    count <= countAux;
    atMax <= '1' when (countAux = MAX) else '0';
    atZero <= '1' when (countAux = 0) else '0';

end architecture synth;
