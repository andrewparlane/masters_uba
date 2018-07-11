library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.all;
use work.vga_timings_10_10_pkg.all;

entity vga_tb is
end entity vga_tb;

architecture sim of vga_tb is
    component vga is
        generic (H_ACTIVE:      natural;    -- ticks
                 H_FRONT_PORCH: natural;    -- ticks
                 H_SYNC:        natural;    -- ticks
                 H_BACK_PORCH:  natural;    -- ticks

                 V_ACTIVE:      natural;    -- líneas
                 V_FRONT_PORCH: natural;    -- líneas
                 V_SYNC:        natural;    -- líneas
                 V_BACK_PORCH:  natural);   -- líneas

        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              pixelX:   out unsigned((utils_pkg.min_width(H_ACTIVE) - 1) downto 0);
              pixelY:   out unsigned((utils_pkg.min_width(V_ACTIVE) - 1) downto 0);
              inActive: out std_ulogic;
              nHSync:   out std_ulogic;
              nVSync:   out std_ulogic);

    end component vga;

    component vga_sva_wrapper is
    end component vga_sva_wrapper;

    signal clk:         std_ulogic := '0';
    signal rst:         std_ulogic := '1';

    signal pixelX:      unsigned((PIXEL_X_WIDTH - 1) downto 0);
    signal pixelY:      unsigned((PIXEL_Y_WIDTH - 1) downto 0);

    signal inActive:    std_ulogic;
    signal nHSync:      std_ulogic;
    signal nVSync:      std_ulogic;

    -- 50 MHz
    constant CLK_HZ:        natural := 50 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;

    constant LINE_TIME:     time := getLineTime(CLK_PERIOD);
    constant FRAME_TIME:    time := getFrameTime(CLK_PERIOD);
begin

    clk <= not clk after (CLK_PERIOD/2);

    dut: vga    generic map(H_ACTIVE        => H_ACTIVE,
                            H_FRONT_PORCH   => H_FRONT_PORCH,
                            H_SYNC          => H_SYNC,
                            H_BACK_PORCH    => H_BACK_PORCH,
                            V_ACTIVE        => V_ACTIVE,
                            V_FRONT_PORCH   => V_FRONT_PORCH,
                            V_SYNC          => V_SYNC,
                            V_BACK_PORCH    => V_BACK_PORCH)
                    port map(clk => clk,
                             rst => rst,
                             pixelX => pixelX,
                             pixelY => pixelY,
                             inActive => inActive,
                             nHSync => nHSync,
                             nVSync => nVSync);

    sva:    vga_sva_wrapper;

    process
    begin
        report ("CLK_HZ " & integer'image(CLK_HZ) & "Hz" &
                " -> periodo " & time'image(CLK_PERIOD) &
                " -> " & integer'image(1000000000 / (getFrameTime(CLK_PERIOD) / 1 ns)) &
                " cuadras cada segundo");
        rst <= '1';
        wait for CLK_PERIOD * 5;
        rst <= '0';
        wait for (5 * FRAME_TIME);
        rst <= '1';
        wait for 100 ns;
        std.env.stop;
    end process;

end architecture sim;