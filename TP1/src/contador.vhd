library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity contador is
    generic (WIDTH: natural;
             MAX: natural);
    port (clk:      in  std_logic;
          en:       in  std_logic;
          rst:      in  std_logic;
          load:     in  std_logic;
          loadData: in  unsigned((WIDTH - 1) downto 0);
          o:        out unsigned((WIDTH - 1) downto 0);
          overflow: out std_logic);
end entity contador;

architecture synth of contador is
    signal tmp: unsigned((WIDTH - 1) downto 0);
begin

    process (clk, rst)
    begin
        -- asíncrono reset
        if (rst = '1') then
            tmp <= (others => '0');
            overflow <= '0';
        elsif (rising_edge(clk)) then
            if (en = '1') then
                if (load = '1') then
                    tmp <= loadData;
                    overflow <= '0';
                else
                    if (tmp = to_unsigned(MAX, WIDTH)) then
                        tmp <= (others => '0');
                        overflow <= '1';
                    else
                        tmp <= tmp + to_unsigned(1, WIDTH);
                        overflow <= '0';
                    end if;
                end if;
            else
                overflow <= '0';
            end if;
        end if;
    end process;

    o <= tmp;

end architecture synth;
