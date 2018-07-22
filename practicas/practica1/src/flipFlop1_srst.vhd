library ieee;
use ieee.std_logic_1164.all;

entity flipFlop1_srst is
    port (clk:  in  std_ulogic;
          d:    in  std_ulogic;
          en:   in  std_ulogic;
          srst: in  std_ulogic;
          q:    out std_ulogic);
end entity flipFlop1_srst;

architecture synth of flipFlop1_srst is
begin
    process (clk)
    begin
        if rising_edge(clk) then
            if (srst = '1') then
                q <= '0';
            elsif (en = '1') then
                q <= d;
            end if;
        end if;
    end process;
end architecture synth;