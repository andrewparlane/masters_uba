library ieee;
use ieee.std_logic_1164.all;

entity flipFlop1_srst is
    port (clk:  in  std_logic;
          d:    in  std_logic;
          en:   in  std_logic;
          srst: in  std_logic;
          q:    out std_logic);
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