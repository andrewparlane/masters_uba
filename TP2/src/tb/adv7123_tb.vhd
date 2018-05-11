library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;

use work.vga_timings_10_10_pkg.all;

entity adv7123_tb is
end entity adv7123_tb;

architecture sim of adv7123_tb is
    component adv7123 is
        generic (H_ACTIVE:      natural;    -- ticks
                 H_FRONT_PORCH: natural;    -- ticks
                 H_SYNC:        natural;    -- ticks
                 H_BACK_PORCH:  natural;    -- ticks

                 V_ACTIVE:      natural;    -- líneas
                 V_FRONT_PORCH: natural;    -- líneas
                 V_SYNC:        natural;    -- líneas
                 V_BACK_PORCH:  natural);   -- líneas

        port (clk:      in  std_logic;
              rst:      in  std_logic;
              rIn:      in  std_logic_vector(9 downto 0);
              gIn:      in  std_logic_vector(9 downto 0);
              bIn:      in  std_logic_vector(9 downto 0);
              pixelX:   out unsigned((utils.min_width(H_ACTIVE) - 1) downto 0);
              pixelY:   out unsigned((utils.min_width(V_ACTIVE) - 1) downto 0);
              clkOut:   out std_logic;
              rOut:     out std_logic_vector(9 downto 0);
              gOut:     out std_logic_vector(9 downto 0);
              bOut:     out std_logic_vector(9 downto 0);
              nBlank:   out std_logic;
              nSync:    out std_logic;
              nHSync:   out std_logic;
              nVSync:   out std_logic);

    end component adv7123;

    component adv7123_sva_wrapper is
    end component adv7123_sva_wrapper;

    signal clk:         std_logic := '0';
    signal rst:         std_logic := '1';

    signal pixelX:      unsigned((PIXEL_X_WIDTH - 1) downto 0);
    signal pixelY:      unsigned((PIXEL_Y_WIDTH - 1) downto 0);

    signal nBlank:      std_logic;
    signal nSync:       std_logic;
    signal nHSync:      std_logic;
    signal nVSync:      std_logic;

    signal rIn:         std_logic_vector(9 downto 0);
    signal gIn:         std_logic_vector(9 downto 0);
    signal bIn:         std_logic_vector(9 downto 0);

    signal rOut:        std_logic_vector(9 downto 0);
    signal gOut:        std_logic_vector(9 downto 0);
    signal bOut:        std_logic_vector(9 downto 0);

    signal clkOut:      std_logic;

    -- 50 MHz
    constant CLK_HZ:        natural := 50 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;

    constant LINE_TIME:     time := getLineTime(CLK_PERIOD);
    constant FRAME_TIME:    time := getFrameTime(CLK_PERIOD);
begin

    clk <= not clk after (CLK_PERIOD/2);

    dut: adv7123    generic map(H_ACTIVE        => H_ACTIVE,
                                H_FRONT_PORCH   => H_FRONT_PORCH,
                                H_SYNC          => H_SYNC,
                                H_BACK_PORCH    => H_BACK_PORCH,
                                V_ACTIVE        => V_ACTIVE,
                                V_FRONT_PORCH   => V_FRONT_PORCH,
                                V_SYNC          => V_SYNC,
                                V_BACK_PORCH    => V_BACK_PORCH)
                    port map(clk => clk,
                             rst => rst,
                             rIn => rIn,
                             gIn => gIn,
                             bIn => bIn,
                             pixelX => pixelX,
                             pixelY => pixelY,
                             clkOut => clkOut,
                             rOut => rOut,
                             gOut => gOut,
                             bOut => bOut,
                             nBlank => nBlank,
                             nSync  => nSync,
                             nHSync => nHSync,
                             nVSync => nVSync);

    sva:    adv7123_sva_wrapper;

    process (all)
    begin
        if (rst = '1') then
            rIn <= "1111111111";
            gIn <= "1111111111";
            bIn <= "1111111111";
        else
            gIn <= "0000000000";
            bIn <= "0000000000";
            if (pixelY(0) = '0') then
                if (pixelX(0) = '0') then
                    rIn <= "1111111111";
                else
                    rIn <= "0000000000";
                end if;
            else
                if (pixelX(0) = '0') then
                    rIn <= "0000000000";
                else
                    rIn <= "1111111111";
                end if;
            end if;
        end if;
    end process;

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