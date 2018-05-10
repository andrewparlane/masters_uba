library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.char_rom_pkg.all;

entity char_rom is
    port (clk:  in  std_logic;
          rst:  in  std_logic;
          char: in  charRomCharacter;
          offX: in  unsigned(3 downto 0);
          offY: in  unsigned(4 downto 0);
          px:   out std_logic);
end entity char_rom;

architecture synth of char_rom is

    component altera_mf_rom is
        port(address:   in  std_logic_vector (11 downto 0);
             clock:     in  std_logic;
             q:         out std_logic_vector (15 downto 0));
    end component altera_mf_rom;

    constant NUM_CHARS:         natural := 95;
    constant PX_CADA_FILA:      natural := 16;

    -- max 2849 = 0xB21 -> 12 bits
    signal y:       unsigned(11 downto 0);
    signal fila:    std_logic_vector(15 downto 0);

    signal uChar:   unsigned(6 downto 0);

begin

    rom_inst : altera_mf_rom port map (address => std_logic_vector(y),
                                       clock => clk,
                                       q => fila);

    px <= fila(to_integer(offX));


    uChar <= to_unsigned(charRomCharacter'pos(char), uChar'length);

    -- char * 30
    -- = (char * 32) - (char * 2)
    -- = (char & "00000") - (char & "0")
    y <= ((uChar & "00000") -
          ("0000" & uChar & "0")) +
         resize(offY, y'length);

    -- max permitdo char es NUM_CHARS - 1
    charMenorDe95:
        assert (to_integer(uChar) < NUM_CHARS)
        report "Char = " & integer'image(charRomCharacter'pos(char)) &
               "max permitido es " & integer'image(NUM_CHARS-1)
        severity error;

end architecture synth;
