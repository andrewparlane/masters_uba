library ieee;
use ieee.std_logic_1164.all;

entity contador4 is
    port (clk:  in  std_logic;
          rst:  in  std_logic;
          q:    out std_logic_vector(3 downto 0));
end entity contador4;

architecture synth of contador4 is
    signal ff: std_logic_vector(3 downto 0);
begin
    process (clk, rst)
    begin
        if (rst = '1') then
            ff <= "0000";
        elsif rising_edge(clk) then
            ff(0) <= not ff(0);
            ff(1) <= ff(0) xor ff(1);
            ff(2) <= (ff(0) and ff(1)) xor ff(2) ;
            ff(3) <= (ff(0) and ff(1) and ff(2)) xor ff(3) ;
        end if;
    end process;

    Q <= ff;

end architecture synth;
