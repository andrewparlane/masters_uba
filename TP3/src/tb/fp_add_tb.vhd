library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

library common;
use common.all;
use common.type_pkg.all;

use work.fp_type_pkg.all;

entity fp_add_tb is
    generic(TOTAL_BITS:                 natural := 32;
            EXPONENT_BITS:              natural := 8;
            TEST_FILE:                  string  := "test_files/suma/test_sum_float_32_8.txt";
            ROUNDING_MODE:              RoundingMode;
            SUBTRACT:                   boolean := false;
            NO_ASSERT_ON_ZERO_NEG_ZERO: boolean := false);
end entity fp_add_tb;

architecture sim of fp_add_tb is
    component fp_add is
        generic (TOTAL_BITS:    natural;
                 EXPONENT_BITS: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              inA:      in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
              inB:      in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
              rm:       in RoundingMode;
              outC:     out std_ulogic_vector((TOTAL_BITS - 1) downto 0));
    end component fp_add;

    component delay is
        generic (DELAY: natural;
                 WIDTH: natural);

        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              output:   out std_ulogic_vector((WIDTH - 1) downto 0));
    end component delay;

    constant PIPELINE_STAGES:   natural := 7;

    package fpPkg
            is new work.fp_helper_pkg
            generic map (TOTAL_BITS => TOTAL_BITS,
                         EXPONENT_BITS => EXPONENT_BITS);

    signal A:                   std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal B:                   std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal ADelayed:            std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal BDelayed:            std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal C:                   std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal expectedC:           std_ulogic_vector((TOTAL_BITS - 1) downto 0);
    signal expectedCDelayed:    std_ulogic_vector((TOTAL_BITS - 1) downto 0);

    -- convert the args and result to fpUnpackeds
    -- for debugging
    signal fpADelayed:          fpPkg.fpUnpacked;
    signal fpBDelayed:          fpPkg.fpUnpacked;
    signal fpC:                 fpPkg.fpUnpacked;
    signal fpExpectedCDelayed:  fpPkg.fpUnpacked;

    signal clk: std_ulogic := '0';
    signal rst: std_ulogic := '0';

    signal done: std_ulogic := '0';

    -- 50 MHz
    constant CLK_HZ:        natural := 50 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;
begin

    clk <= not clk after (CLK_PERIOD/2);

    dut: fp_add     generic map (TOTAL_BITS => TOTAL_BITS,
                                 EXPONENT_BITS => EXPONENT_BITS)
                    port map (clk => clk,
                              rst => rst,
                              inA => A,
                              inB => B,
                              rm => ROUNDING_MODE,
                              outC => C);

    dlyA: delay generic map (WIDTH => TOTAL_BITS,
                             DELAY => PIPELINE_STAGES)
                port map (clk => clk,
                          rst => rst,
                          input => A,
                          output => ADelayed);

    dlyB: delay generic map (WIDTH => TOTAL_BITS,
                             DELAY => PIPELINE_STAGES)
                port map (clk => clk,
                          rst => rst,
                          input => B,
                          output => BDelayed);

    dlyExpectedC: delay generic map (WIDTH => TOTAL_BITS,
                                     DELAY => PIPELINE_STAGES)
                        port map (clk => clk,
                                  rst => rst,
                                  input => expectedC,
                                  output => expectedCDelayed);

    fpADelayed          <= fpPkg.unpack(ADelayed);
    fpBDelayed          <= fpPkg.unpack(BDelayed);
    fpC                 <= fpPkg.unpack(C);
    fpExpectedCDelayed  <= fpPkg.unpack(expectedCDelayed);

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
                        (fpPkg.is_NaN(fpC) and
                         fpPkg.is_NaN(fpExpectedCDelayed)) or
                       (NO_ASSERT_ON_ZERO_NEG_ZERO and
                        (fpPkg.is_zero(fpC)) and
                        (fpPkg.is_zero(fpExpectedCDelayed)))
                    report fpPkg.to_string(fpADelayed) & OP &
                           fpPkg.to_string(fpBDelayed) & " = " &
                           fpPkg.to_string(fpC) & " expecting " &
                           fpPkg.to_string(fpExpectedCDelayed)
                    severity failure;

            wait for CLK_PERIOD;
        end loop;
        std.env.stop;
    end process;
end architecture sim;
