library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

library common;
use common.all;
use common.type_pkg.all;

use work.fp_helper_pkg.all;

entity fp_add_tb is
    generic(TOTAL_BITS:                 natural := 32;
            EXPONENT_BITS:              natural := 8;
            TEST_FILE:                  string  := "test_files/suma/test_sum_float_32_8.txt";
            ROUNDING_MODE:              RoundingMode;
            DENORMALS:                  boolean;
            SUBTRACT:                   boolean := false;
            NO_ASSERT_ON_ZERO_NEG_ZERO: boolean := false);
end entity fp_add_tb;

architecture sim of fp_add_tb is
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

    component delay is
        generic (DELAY: natural;
                 WIDTH: natural);

        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              output:   out std_ulogic_vector((WIDTH - 1) downto 0));
    end component delay;

    component fp_add_wrapper is
    end component fp_add_wrapper;

    constant PIPELINE_STAGES:   natural := 6;

    signal A:                   std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal B:                   std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal ADelayed:            std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal BDelayed:            std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal C:                   std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal expectedC:           std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal expectedCDelayed:    std_ulogic_vector((TOTAL_BITS - 1) downto 0);

    -- convert the args and result to fpUnpackeds
    -- for debugging
    signal fpADelayed:          fpUnpacked;
    signal fpBDelayed:          fpUnpacked;
    signal fpC:                 fpUnpacked;
    signal fpExpectedCDelayed:  fpUnpacked;

    signal clk: std_ulogic := '0';
    signal rst: std_ulogic := '0';

    signal done: std_ulogic := '0';

    -- 50 MHz
    constant CLK_HZ:        natural := 50 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;
begin

    clk <= not clk after (CLK_PERIOD/2);

    add_coverage:   fp_add_wrapper;

    dut: fp_add     generic map (TBITS      => TOTAL_BITS,
                                 EBITS      => EXPONENT_BITS,
                                 DENORMALS  => DENORMALS)
                    port map (i_clk => clk,
                              i_a   => A,
                              i_b   => B,
                              i_rm  => ROUNDING_MODE,
                              o_res => C);

    dlyA: delay generic map (WIDTH => TOTAL_BITS,
                             DELAY => PIPELINE_STAGES)
                port map (clk    => clk,
                          rst    => rst,
                          input  => A,
                          output => ADelayed);

    dlyB: delay generic map (WIDTH => TOTAL_BITS,
                             DELAY => PIPELINE_STAGES)
                port map (clk    => clk,
                          rst    => rst,
                          input  => B,
                          output => BDelayed);

    dlyExpectedC: delay generic map (WIDTH => TOTAL_BITS,
                                     DELAY => PIPELINE_STAGES)
                        port map (clk    => clk,
                                  rst    => rst,
                                  input  => expectedC,
                                  output => expectedCDelayed);

    fpADelayed          <= unpack(ADelayed, TOTAL_BITS, EXPONENT_BITS);
    fpBDelayed          <= unpack(BDelayed, TOTAL_BITS, EXPONENT_BITS);
    fpC                 <= unpack(C, TOTAL_BITS, EXPONENT_BITS);
    fpExpectedCDelayed  <= unpack(expectedCDelayed, TOTAL_BITS, EXPONENT_BITS);

    process
        file     f:         text;
        variable l:         line;
        variable u:         unsigned((TOTAL_BITS - 1) downto 0);
      begin

        report "Starting test with parameters:" &
               " TOTAL_BITS = " & integer'image(TOTAL_BITS) &
               " EXPONENT_BITS = " & integer'image(EXPONENT_BITS) &
               " TEST_FILE = " & TEST_FILE &
               " ROUNDING_MODE = " & RoundingMode'image(ROUNDING_MODE);

        rst <= '1';
        wait for CLK_PERIOD * 5;
        rst <= '0';

        file_open(f, TEST_FILE,  read_mode);

        while not endfile(f) loop
            readline(f, l);

            utils_pkg.read_unsigned_decimal_from_line(l, u);
            A <= std_ulogic_vector(u);

            utils_pkg.read_unsigned_decimal_from_line(l, u);
            if (SUBTRACT) then
                B <= std_ulogic_vector((not u(TOTAL_BITS-1)) &
                                       u((TOTAL_BITS-2) downto 0));
            else
                B <= std_ulogic_vector(u);
            end if;

            utils_pkg.read_unsigned_decimal_from_line(l, u);
            expectedC <= std_ulogic_vector(u);

            wait for CLK_PERIOD;
        end loop;

        file_close(f);

        wait for (CLK_PERIOD * PIPELINE_STAGES);
        done <= '1';
        std.env.stop;
    end process;

    process
        variable OP: string(1 to 3);
    begin
        if (SUBTRACT) then
            OP := " - ";
        else
            OP := " + ";
        end if;

        wait until falling_edge(rst);
        wait until rising_edge(clk);
        wait for (CLK_PERIOD * PIPELINE_STAGES);
        while (done = '0') loop
            assert (C = expectedCDelayed) or
                        (is_NaN(fpC) and
                         is_NaN(fpExpectedCDelayed)) or
                       (NO_ASSERT_ON_ZERO_NEG_ZERO and
                        (is_zero(fpC)) and
                        (is_zero(fpExpectedCDelayed)))
                    report to_string(fpADelayed, TOTAL_BITS, EXPONENT_BITS) & OP &
                           to_string(fpBDelayed, TOTAL_BITS, EXPONENT_BITS) & " = " &
                           to_string(fpC, TOTAL_BITS, EXPONENT_BITS) & " expecting " &
                           to_string(fpExpectedCDelayed, TOTAL_BITS, EXPONENT_BITS)
                    severity failure;

            wait for CLK_PERIOD;
        end loop;
        std.env.stop;
    end process;
end architecture sim;
