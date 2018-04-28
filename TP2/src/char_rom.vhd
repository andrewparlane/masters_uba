library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity char_rom is
    port (clk:  in  std_logic;
          rst:  in  std_logic;
          char: in  std_logic_vector(6 downto 0);
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

begin

    rom_inst : altera_mf_rom port map (address => std_logic_vector(y),
                                       clock => clk,
                                       q => fila);

    px <= fila(to_integer(offX));

    -- char * 30
    -- = (char * 32) - (char * 2)
    -- = (char & "00000") - (char & "0")
    y <= (unsigned(char & "00000") -
          unsigned("0000" & char & "0")) +
         resize(offY, y'length);

    -- max permitdo char es NUM_CHARS - 1
    charMenorDe95:
        assert (to_integer(unsigned(char)) < NUM_CHARS)
        report "Char = " & integer'image(to_integer(unsigned(char))) &
               "max permitido es " & integer'image(NUM_CHARS-1)
        severity error;

end architecture synth;
