library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use std.textio.all;

library common;
use common.all;
use common.utils_pkg.all;

entity transform_tb is
    generic(TEST_FILE:                  string);
end entity transform_tb;

architecture sim of transform_tb is
    component transform is
        port (i_clk:                in  std_ulogic;
              i_reset:              in  std_ulogic;
              i_start:              in  std_ulogic;
              i_value:              in  signed(15 downto 0);
              i_valid:              in  std_ulogic;
              i_alpha:              in  unsigned(31 downto 0);
              i_beta:               in  unsigned(31 downto 0);
              i_gamma:              in  unsigned(31 downto 0);
              o_setPixelAddr:       out unsigned(15 downto 0);
              o_setPixelBitMask:    out unsigned(7 downto 0);
              o_setPixel:           out std_ulogic);
    end component transform;

    component delay is
        generic (DELAY: natural;
                 WIDTH: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              output:   out std_ulogic_vector((WIDTH - 1) downto 0));
    end component delay;

    -- 3 ticks to get all three inputs to the cordic
    -- then 30 ticks for the cordic
    -- then 1 tick for the pixel address calculation
    constant DELAY_TICKS:       natural := 35;

    signal v:                   signed(15 downto 0);
    signal alpha:               unsigned(31 downto 0);
    signal beta:                unsigned(31 downto 0);
    signal gamma:               unsigned(31 downto 0);

    signal calculatedAddr:      unsigned(15 downto 0);
    signal calculatedBitMask:   unsigned(7 downto 0);
    signal expectedAddr:        unsigned(15 downto 0);
    signal expectedBitMask:     unsigned(7 downto 0);
    signal delayedAddr:         unsigned(15 downto 0);
    signal delayedBitMask:      unsigned(7 downto 0);

    signal start:               std_ulogic;
    signal valid:               std_ulogic;
    signal setPixel:            std_ulogic;

    signal clk:                 std_ulogic := '0';
    signal reset:               std_ulogic;

    signal done:                std_ulogic := '0';

    -- 100 MHz
    constant CLK_HZ:        natural := 100 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;
begin

    clk <= not clk after (CLK_PERIOD/2);

    dut: transform
        port map (i_clk              => clk,
                  i_reset            => reset,
                  i_start            => start,
                  i_value            => v,
                  i_valid            => valid,
                  i_alpha            => alpha,
                  i_beta             => beta,
                  i_gamma            => gamma,
                  o_setPixelAddr     => calculatedAddr,
                  o_setPixelBitMask  => calculatedBitMask,
                  o_setPixel         => setPixel);

    dlyAddr: delay
        generic map (WIDTH => 16,
                     DELAY => DELAY_TICKS)
        port map (clk    => clk,
                  rst    => reset,
                  input  => std_ulogic_vector(expectedAddr),
                  unsigned(output) => delayedAddr);

    dlyBitMask: delay
        generic map (WIDTH => 8,
                     DELAY => DELAY_TICKS)
        port map (clk    => clk,
                  rst    => reset,
                  input  => std_ulogic_vector(expectedBitMask),
                  unsigned(output) => delayedBitMask);

    process
        file     f:         text;
        variable l:         line;
        variable aux:       unsigned(31 downto 0);
        variable ch:        character;
        variable x:         signed(15 downto 0);
        variable y:         signed(15 downto 0);
        variable z:         signed(15 downto 0);
      begin
        valid <= '0';
        reset <= '1';
        start <= '0';
        wait for CLK_PERIOD * 5;
        wait until (rising_edge(clk));
        reset <= '0';

        wait until (rising_edge(clk));
        start <= '1';
        wait until (rising_edge(clk));
        start <= '0';
        wait until (rising_edge(clk));

        file_open(f, TEST_FILE,  read_mode);

        while not endfile(f) loop
            readline(f, l);

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            x := signed(aux(28 downto 13));

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            y := signed(aux(28 downto 13));

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            z := signed(aux(28 downto 13));

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            alpha <= aux;

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            beta <= aux;

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            gamma <= aux;

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            utils_pkg.read_unsigned_decimal_from_line(l, aux);

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            expectedAddr <= aux(15 downto 0);

            utils_pkg.read_unsigned_decimal_from_line(l, aux);
            expectedBitMask <= aux(7 downto 0);

            valid <= '1';
            v <= x;
            wait until rising_edge(clk);
            v <= y;
            wait until rising_edge(clk);
            v <= z;
            wait until rising_edge(clk);
        end loop;

        valid <= '0';

        file_close(f);

        wait for (CLK_PERIOD * DELAY_TICKS * 2);
        done <= '1';
        std.env.stop;
    end process;

    process
    begin
        while (done = '0') loop
            wait until rising_edge(clk);
            if (setPixel = '1') then
                assert ((calculatedAddr = delayedAddr) and
                        (calculatedBitMask = delayedBitMask))
                        severity failure;
            end if;
        end loop;
        std.env.stop;
    end process;
end architecture sim;
