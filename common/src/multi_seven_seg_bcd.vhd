library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.type_pkg.all;

entity multi_seven_seg_bcd is
    generic (CIFRAS: natural);
    port (clk:      in  std_ulogic;
          rst:      in  std_ulogic;
          en:       in  std_ulogic_vector((CIFRAS - 1) downto 0);
          bcd:      in  unsignedArray((CIFRAS - 1) downto 0)(3 downto 0);
          display:  out slvArray((CIFRAS - 1) downto 0)(6 downto 0));
end entity multi_seven_seg_bcd;

architecture synth of multi_seven_seg_bcd is

    component seven_seg_bcd is
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              en:       in  std_ulogic;
              bcd:      in  unsigned(3 downto 0);
              display:  out std_ulogic_vector(6 downto 0));
    end component seven_seg_bcd;

begin

    genLoop:
    for i in 0 to (CIFRAS - 1) generate
        inst: seven_seg_bcd port map (clk => clk,
                                      rst => rst,
                                      en => en(i),
                                      bcd => bcd(i),
                                      display => display(i));
    end generate genLoop;

end architecture synth;
