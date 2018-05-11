library ieee;
use ieee.std_logic_1164.all;

entity contador2 is
    port (clk:  in  std_ulogic;
          rst:  in  std_ulogic;
          q:    out std_ulogic_vector(1 downto 0));
end entity contador2;

architecture synth of contador2 is
    signal ff: std_ulogic_vector(1 downto 0);
begin
    process (clk, rst)
    begin
        if (rst = '1') then
            ff <= "00";
        elsif rising_edge(clk) then
            ff(0) <= not ff(0);
            ff(1) <= ff(0) xor ff(1);
        end if;
    end process;

    Q <= ff;

end architecture synth;
