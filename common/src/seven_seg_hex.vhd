library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity seven_seg_hex is
    port (clk:      in  std_ulogic;
          rst:      in  std_ulogic;
          en:       in  std_ulogic;
          hex:      in  unsigned(3 downto 0);
          display:  out std_ulogic_vector(6 downto 0));
end entity seven_seg_hex;

architecture synth of seven_seg_hex is
    signal displayAux: std_ulogic_vector(6 downto 0);
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

    with hex select displayAux <=
            (not "0111111") when 4ux"0",
            (not "0000110") when 4ux"1",
            (not "1011011") when 4ux"2",
            (not "1001111") when 4ux"3",
            (not "1100110") when 4ux"4",
            (not "1101101") when 4ux"5",
            (not "1111101") when 4ux"6",
            (not "0000111") when 4ux"7",
            (not "1111111") when 4ux"8",
            (not "1101111") when 4ux"9",
            (not "1110111") when 4ux"A",
            (not "1111100") when 4ux"B",
            (not "1011000") when 4ux"C",
            (not "1011110") when 4ux"D",
            (not "1111001") when 4ux"E",
            (not "1110001") when 4ux"F",
            (not "0000000") when others;

    process (clk, rst)
    begin
        if (rst = '1') then
            display <= (others => '1'); -- apagado
        elsif (rising_edge(clk)) then
            if (en = '1') then
                display <= displayAux;
            else
                display <= (others => '1');
            end if;
        end if;
    end process;

end architecture synth;
