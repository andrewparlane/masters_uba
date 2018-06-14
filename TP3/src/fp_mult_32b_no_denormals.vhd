library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

use work.fp_type_pkg.all;
use work.fp_helper_pkg.all;

entity fp_mult_32b_no_denormals is
        port (CLOCK_50: in  std_ulogic;
              i_a:      in  std_ulogic_vector(31 downto 0);
              i_b:      in  std_ulogic_vector(31 downto 0);
              i_rm:     in  std_ulogic_vector(1 downto 0);
              o_res:    out std_ulogic_vector(31 downto 0));
end entity fp_mult_32b_no_denormals;

architecture synth of fp_mult_32b_no_denormals is
    component fp_mult is
        generic (TBITS:     natural;
                 EBITS:     natural;
                 DENORMALS: boolean);
        port (i_clk:    in  std_ulogic;
              i_a:      in  std_ulogic_vector((TBITS - 1) downto 0);
              i_b:      in  std_ulogic_vector((TBITS - 1) downto 0);
              i_rm:     in  RoundingMode;
              o_res:    out std_ulogic_vector((TBITS - 1) downto 0));
    end component fp_mult;

    signal a:  std_ulogic_vector(31 downto 0);
    signal b:  std_ulogic_vector(31 downto 0);
    signal rm: RoundingMode;
begin

    process (CLOCK_50)
    begin
        if (rising_edge(CLOCK_50)) then
            case (i_rm) is
                when "00"    => rm <= RoundingMode_NEG_INF;
                when "01"    => rm <= RoundingMode_POS_INF;
                when "10"    => rm <= RoundingMode_0;
                when others  => rm <= RoundingMode_NEAREST;
            end case;
            a <= i_a;
            b <= i_b;
        end if;
    end process;

    dut: fp_mult    generic map (TBITS      => 32,
                                 EBITS      => 8,
                                 DENORMALS  => false)
                    port map (i_clk => CLOCK_50,
                              i_a   => a,
                              i_b   => b,
                              i_rm  => rm,
                              o_res => o_res);
end architecture synth;
