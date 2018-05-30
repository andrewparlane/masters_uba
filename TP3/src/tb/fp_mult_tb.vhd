library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

library common;
use common.all;
use common.type_pkg.all;

use work.fp_rounding_pkg.all;

entity fp_mult_tb is
    generic(TOTAL_BITS:     natural := 32;
            EXPONENT_BITS:  natural := 8;
            TEST_FILE:      string  := "test_files/multiplicacion/test_mul_float_32_8.txt";
            ROUNDING_MODE:  RoundingMode);
end entity fp_mult_tb;

architecture sim of fp_mult_tb is
    component fp_mult is
        generic (TOTAL_BITS:    natural;
                 EXPONENT_BITS: natural);
        port (inA:  in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
              inB:  in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
              roundingMode: RoundingMode;
              outC: out std_ulogic_vector((TOTAL_BITS - 1) downto 0));
    end component fp_mult;

    package fpPkg
            is new work.fp_helper_pkg
            generic map (TOTAL_BITS => TOTAL_BITS,
                         EXPONENT_BITS => EXPONENT_BITS);

    signal A:           std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal B:           std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal C:           std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal expectedC:   std_ulogic_vector((TOTAL_BITS - 1) downto 0);

begin

    dut: fp_mult    generic map (TOTAL_BITS => TOTAL_BITS,
                                 EXPONENT_BITS => EXPONENT_BITS)
                    port map (inA => A,
                              inB => B,
                              roundingMode => ROUNDING_MODE,
                              outC => C);

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

            assert C = expectedC
                report fpPkg.to_string(fpPkg.vect_to_fpType(A)) & " * " &
                       fpPkg.to_string(fpPkg.vect_to_fpType(B)) & " = " &
                       fpPkg.to_string(fpPkg.vect_to_fpType(C)) & " expecting " &
                       fpPkg.to_string(fpPkg.vect_to_fpType(expectedC))
                severity failure;
        end loop;

        file_close(f);

        std.env.stop;
    end process;
end architecture sim;
