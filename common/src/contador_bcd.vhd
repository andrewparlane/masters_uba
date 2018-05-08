library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.all;

entity contador_bcd is
    generic (CIFRAS: natural);
    port (clk:      in  std_logic;
          en:       in  std_logic;
          rst:      in  std_logic;
          dout:     out type_pkg.unsignedArray((CIFRAS-1) downto 0)(3 downto 0));
end entity contador_bcd;

architecture synth of contador_bcd is

    component contador is
        generic (WIDTH: natural;
                 MAX: natural);
        port (clk:      in  std_logic;
              en:       in  std_logic;
              rst:      in  std_logic;
              load:     in  std_logic;
              loadData: in  unsigned((WIDTH - 1) downto 0);
              count:    out unsigned((WIDTH - 1) downto 0);
              atMax:    out std_logic);
    end component contador;

    type stdLogicArray is array ((CIFRAS - 1) downto 0) of std_logic;
    signal dEn: stdLogicArray;
    signal atMax: stdLogicArray;

begin

    dEn(0) <= en;

    cifraGenLoop:
    for c in 0 to (CIFRAS - 1) generate
    begin
        siNoCifra0:
        if (c /= 0) generate
            -- un dígito cuenta si el dígito anterior hace el transición 9 -> 0
            -- (en and atMax)
            dEn(c) <= dEn(c-1) and atMax(c-1);
        end generate;
        inst:   contador    generic map    (WIDTH => 4,
                                            MAX => 9)
                            port map       (clk => clk,
                                            en => dEn(c),
                                            rst => rst,
                                            load => '0',
                                            loadData => to_unsigned(0, 4),
                                            count => dout(c),
                                            atMax => atMax(c));
    end generate;

end architecture synth;
