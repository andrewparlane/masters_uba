library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

use work.fp_helper_pkg.all;

entity fp_add_32b_denormals is
        port (CLOCK_50: in  std_ulogic;
              i_a:      in  std_ulogic_vector(31 downto 0);
              i_b:      in  std_ulogic_vector(31 downto 0);
              i_rm:     in  std_ulogic_vector(1 downto 0);
              o_res:    out std_ulogic_vector(31 downto 0));
end entity fp_add_32b_denormals;

architecture synth of fp_add_32b_denormals is
    component fp_add is
        generic (TBITS:     natural;
                 EBITS:     natural;
                 DENORMALS: boolean);
        port (i_clk:    in  std_ulogic;
              i_a:      in  std_ulogic_vector((TBITS - 1) downto 0);
              i_b:      in  std_ulogic_vector((TBITS - 1) downto 0);
              i_rm:     in  RoundingMode;
              o_res:    out std_ulogic_vector((TBITS - 1) downto 0));
    end component fp_add;

    signal rm: RoundingMode;
begin

    rm <= RoundingMode_NEG_INF when (i_rm = "00") else
          RoundingMode_POS_INF when (i_rm = "01") else
          RoundingMode_0       when (i_rm = "10") else
          RoundingMode_NEAREST;

    dut: fp_add     generic map (TBITS      => 32,
                                 EBITS      => 8,
                                 DENORMALS  => true)
                    port map (i_clk => CLOCK_50,
                              i_a   => i_a,
                              i_b   => i_b,
                              i_rm  => rm,
                              o_res => o_res);

end architecture synth;
