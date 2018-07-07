library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.type_pkg.all;

entity multi_seven_seg_hex is
    generic (CIFRAS: natural);
    port (clk:      in  std_ulogic;
          rst:      in  std_ulogic;
          en:       in  std_ulogic_vector((CIFRAS - 1) downto 0);
          hex:      in  unsignedArray((CIFRAS - 1) downto 0)(3 downto 0);
          display:  out slvArray((CIFRAS - 1) downto 0)(6 downto 0));
end entity multi_seven_seg_hex;

architecture synth of multi_seven_seg_hex is

    component seven_seg_hex is
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              en:       in  std_ulogic;
              hex:      in  unsigned(3 downto 0);
              display:  out std_ulogic_vector(6 downto 0));
    end component seven_seg_hex;

begin

    genLoop:
    for i in 0 to (CIFRAS - 1) generate
        inst: seven_seg_hex port map (clk => clk,
                                      rst => rst,
                                      en => en(i),
                                      hex => hex(i),
                                      display => display(i));
    end generate genLoop;

end architecture synth;
