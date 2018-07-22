library ieee;
use ieee.std_logic_1164.all;

entity flipFlopN_srst is
    generic (WIDTH: integer := 8);
    port (clk:  in  std_ulogic;
          d:    in  std_ulogic_vector((width - 1) downto 0);
          en:   in  std_ulogic;
          srst: in  std_ulogic;
          q:    out std_ulogic_vector((width - 1) downto 0));
end entity flipFlopN_srst;

architecture synth of flipFlopN_srst is
begin
    process (clk)
    begin
        if rising_edge(clk) then
            if (srst = '1') then
                q <= (others => '0');
            elsif (en = '1') then
                q <= d;
            end if;
        end if;
    end process;
end architecture synth;