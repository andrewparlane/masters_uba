library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

library common;
use common.all;
use common.type_pkg.all;

use work.fp_rounding_pkg.all;

entity fp_mult_tb is
    generic(TOTAL_BITS:                 natural := 32;
            EXPONENT_BITS:              natural := 8;
            TEST_FILE:                  string  := "test_files/multiplicacion/test_mul_float_32_8.txt";
            ROUNDING_MODE:              RoundingMode;
            NO_ASSERT_ON_ZERO_NEG_ZERO: boolean := false);
end entity fp_mult_tb;

architecture sim of fp_mult_tb is
    component fp_mult is
        generic (TOTAL_BITS:    natural;
                 EXPONENT_BITS: natural);
        port (inA:          in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
              inB:          in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
              roundingMode: in RoundingMode;
              outC:         out std_ulogic_vector((TOTAL_BITS - 1) downto 0));
    end component fp_mult;

    package fpPkg
            is new work.fp_helper_pkg
            generic map (TOTAL_BITS => TOTAL_BITS,
                         EXPONENT_BITS => EXPONENT_BITS);

    signal A:           std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal B:           std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal C:           std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal expectedC:   std_ulogic_vector((TOTAL_BITS - 1) downto 0);

    -- convert the args and result to fpUnpackeds
    -- for debugging
    signal fpA:         fpPkg.fpUnpacked;
    signal fpB:         fpPkg.fpUnpacked;
    signal fpC:         fpPkg.fpUnpacked;
    signal fpExpectedC: fpPkg.fpUnpacked;


begin

    dut: fp_mult    generic map (TOTAL_BITS => TOTAL_BITS,
                                 EXPONENT_BITS => EXPONENT_BITS)
                    port map (inA => A,
                              inB => B,
                              roundingMode => ROUNDING_MODE,
                              outC => C);

    fpA         <= fpPkg.unpack(A);
    fpB         <= fpPkg.unpack(B);
    fpC         <= fpPkg.unpack(C);
    fpExpectedC <= fpPkg.unpack(expectedC);

    process
        file     f:     text;
        variable l:     line;
        variable u:     unsigned((TOTAL_BITS - 1) downto 0);
      begin

        report "Starting test with parameters:" &
               " TOTAL_BITS = " & integer'image(TOTAL_BITS) &
               " EXPONENT_BITS = " & integer'image(EXPONENT_BITS) &
               " TEST_FILE = " & TEST_FILE &
               " ROUNDING_MODE = " & RoundingMode'image(ROUNDING_MODE);

        file_open(f, TEST_FILE,  read_mode);

        while not endfile(f) loop
            readline(f, l);

            utils_pkg.read_unsigned_decimal_from_line(l, u);
            A <= std_ulogic_vector(u);

            utils_pkg.read_unsigned_decimal_from_line(l, u);
            B <= std_ulogic_vector(u);

            utils_pkg.read_unsigned_decimal_from_line(l, u);
            expectedC <= std_ulogic_vector(u);

            wait for 100 ns;

            assert (C = expectedC) or
                    (fpPkg.is_NaN(fpC) and
                     fpPkg.is_NaN(fpExpectedC)) or
                   (NO_ASSERT_ON_ZERO_NEG_ZERO and
                    (fpPkg.is_zero(fpC)) and
                    (fpPkg.is_zero(fpExpectedC)))
                report fpPkg.to_string(fpA) & " * " &
                       fpPkg.to_string(fpB) & " = " &
                       fpPkg.to_string(fpC) & " expecting " &
                       fpPkg.to_string(fpExpectedC)
                severity failure;
        end loop;

        file_close(f);

        std.env.stop;
    end process;
end architecture sim;
