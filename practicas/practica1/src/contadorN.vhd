library ieee;
use ieee.std_logic_1164.all;

entity contadorN is
    generic (WIDTH: natural);
    port (clk:  in  std_ulogic;
          rst:  in  std_ulogic;
          q:    out std_ulogic_vector((WIDTH - 1) downto 0));
end entity contadorN;

architecture synth of contadorN is
    signal ff: std_ulogic_vector((WIDTH - 1) downto 0);
    signal andBits0ToN: std_ulogic_vector((WIDTH - 2) downto 0);
begin

    -- andBits0ToN(i) = '1' si ff(i) and ff(i-1) and ... and ff(0)
    andBits0ToN(0) <= ff(0);
    genLoop: for i in 1 to (WIDTH - 2) generate
        andBits0ToN(i) <= ff(i) and andBits0ToN(i - 1);
    end generate genLoop;

    process (clk, rst)
    begin
        if (rst = '1') then
            ff <= (others => '0');
        elsif rising_edge(clk) then
            ff(0) <= not ff(0);
            processLoop: for i in 1 to (WIDTH - 1) loop
                ff(i) <= andBits0ToN(i - 1) xor ff(i);
            end loop processLoop;
        end if;
    end process;

    Q <= ff;

end architecture synth;
