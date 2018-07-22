library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

library common;
use common.all;
use common.utils_pkg.all;

entity cordic_rotation_3d_tb is
    generic(TEST_FILE:                  string;
            DELAY_BETWEEN_ENTRIES:      natural := 0);
end entity cordic_rotation_3d_tb;

architecture sim of cordic_rotation_3d_tb is
    component cordic_rotation_3d is
        generic (N: natural;
                 M: natural;
                 STEPS: natural);
        port (i_clk:    in  std_ulogic;
              i_reset:  in  std_ulogic;
              i_en:     in  std_ulogic;
              i_x:      in  signed((N + M - 1) downto 0);
              i_y:      in  signed((N + M - 1) downto 0);
              i_z:      in  signed((N + M - 1) downto 0);
              i_alpha:  in  unsigned((N + M - 1) downto 0);
              i_beta:   in  unsigned((N + M - 1) downto 0);
              i_gamma:  in  unsigned((N + M - 1) downto 0);
              o_x:      out signed((N + M - 1) downto 0);
              o_y:      out signed((N + M - 1) downto 0);
              o_z:      out signed((N + M - 1) downto 0);
              o_valid:  out std_ulogic);
    end component cordic_rotation_3d;

    component delay is
        generic (DELAY: natural;
                 WIDTH: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              output:   out std_ulogic_vector((WIDTH - 1) downto 0));
    end component delay;

    constant CORDIC_STAGES:     natural := 10;
    constant DELAY_TICKS:       natural := CORDIC_STAGES * 3;
    constant QN:                natural := 9;
    constant QM:                natural := 23;
    constant QNM:               natural := QN + QM;

    signal x:                   signed((QNM - 1) downto 0);
    signal y:                   signed((QNM - 1) downto 0);
    signal z:                   signed((QNM - 1) downto 0);
    signal alpha:               unsigned((QNM - 1) downto 0);
    signal beta:                unsigned((QNM - 1) downto 0);
    signal gamma:               unsigned((QNM - 1) downto 0);

    signal calculatedX:         signed((QNM - 1) downto 0);
    signal calculatedY:         signed((QNM - 1) downto 0);
    signal calculatedZ:         signed((QNM - 1) downto 0);

    signal expectedX:           signed((QNM - 1) downto 0);
    signal expectedY:           signed((QNM - 1) downto 0);
    signal expectedZ:           signed((QNM - 1) downto 0);
    signal expectedXDelayed:    signed((QNM - 1) downto 0);
    signal expectedYDelayed:    signed((QNM - 1) downto 0);
    signal expectedZDelayed:    signed((QNM - 1) downto 0);

    signal en:                  std_ulogic;
    signal resValid:            std_ulogic;

    signal clk:                 std_ulogic := '0';
    signal reset:               std_ulogic;

    signal done:                std_ulogic := '0';

    -- 100 MHz
    constant CLK_HZ:        natural := 100 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;
begin

    clk <= not clk after (CLK_PERIOD/2);

    cordic: cordic_rotation_3d
            generic map (N => QN,
                         M => QM,
                         STEPS => CORDIC_STAGES)
            port map (i_clk => clk,
                      i_reset => reset,
                      i_en => en,
                      i_x => x,
                      i_y => y,
                      i_z => z,
                      i_alpha => alpha,
                      i_beta  => beta,
                      i_gamma => gamma,
                      o_x => calculatedX,
                      o_y => calculatedY,
                      o_z => calculatedZ,
                      o_valid => resValid);

    dlyX: delay generic map (WIDTH => QNM,
                             DELAY => DELAY_TICKS)
                port map (clk    => clk,
                          rst    => reset,
                          input  => std_ulogic_vector(expectedX),
                          signed(output) => expectedXDelayed);

    dlyY: delay generic map (WIDTH => QNM,
                             DELAY => DELAY_TICKS)
                port map (clk    => clk,
                          rst    => reset,
                          input  => std_ulogic_vector(expectedY),
                          signed(output) => expectedYDelayed);

    dlyZ: delay generic map (WIDTH => QNM,
                             DELAY => DELAY_TICKS)
                port map (clk    => clk,
                          rst    => reset,
                          input  => std_ulogic_vector(expectedZ),
                          signed(output) => expectedZDelayed);

    process
        file     f:         text;
        variable l:         line;
        variable aux:       unsigned((QNM - 1) downto 0);
        variable ch:        character;
      begin

        reset <= '1';
        en <= '0';
        wait for CLK_PERIOD * 5;
        wait until (rising_edge(clk));
        reset <= '0';

        file_open(f, TEST_FILE,  read_mode);

        while not endfile(f) loop
            wait until rising_edge(clk);

            readline(f, l);

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            x <= signed(aux);

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            y <= signed(aux);

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            z <= signed(aux);

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            alpha <= aux;

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            beta <= aux;

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            gamma <= aux;

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            expectedX <= signed(aux);

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            expectedY <= signed(aux);

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            expectedZ <= signed(aux);

            en <= '1';

            if (DELAY_BETWEEN_ENTRIES /= 0) then
                wait until rising_edge(clk);
                en <= '0';
                for i in 0 to (DELAY_BETWEEN_ENTRIES - 1) loop
                    wait until rising_edge(clk);
                end loop;
            end if;
        end loop;

        wait until rising_edge(clk);
        en <= '0';

        file_close(f);

        wait for (CLK_PERIOD * DELAY_TICKS * 2);
        done <= '1';
        std.env.stop;
    end process;

    process
    begin
        while (done = '0') loop
            wait until rising_edge(clk);
            if (resValid = '1') then
                assert ((calculatedX = expectedXDelayed) and
                        (calculatedY = expectedYDelayed) and
                        (calculatedZ = expectedZDelayed))
                        severity failure;
            end if;
        end loop;
        std.env.stop;
    end process;
end architecture sim;
