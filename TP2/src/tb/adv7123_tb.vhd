library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;

use work.adv7123_10_10_valores.all;

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

        port (eClk:      in  std_logic;
              eRst:      in  std_logic;
              eR:        in  std_logic_vector(9 downto 0);
              eG:        in  std_logic_vector(9 downto 0);
              eB:        in  std_logic_vector(9 downto 0);
              -- salidas del componente
              pixel_x:   out unsigned(utils.min_width(H_ACTIVE) - 1 downto 0);
              pixel_y:   out unsigned(utils.min_width(V_ACTIVE) - 1 downto 0);
              -- salidas del FPGA
              sClk:      out std_logic;
              sR:        out std_logic_vector(9 downto 0);
              sG:        out std_logic_vector(9 downto 0);
              sB:        out std_logic_vector(9 downto 0);
              sBlank:    out std_logic;
              sSync:     out std_logic;
              sHSync:    out std_logic;
              sVSync:    out std_logic);
    end component adv7123;

    component adv7123_sva_wrapper is
    end component adv7123_sva_wrapper;

    signal clk:         std_logic := '0';
    signal rst:         std_logic := '1';
    signal r:           std_logic_vector(9 downto 0) := (others => '0');
    signal g:           std_logic_vector(9 downto 0) := (others => '0');
    signal b:           std_logic_vector(9 downto 0) := (others => '0');

    signal pixel_x:     unsigned((PIXEL_X_WIDTH - 1) downto 0);
    signal pixel_y:     unsigned((PIXEL_Y_WIDTH - 1) downto 0);

    signal vga_clk:     std_logic;
    signal vga_r:       std_logic_vector(9 downto 0);
    signal vga_g:       std_logic_vector(9 downto 0);
    signal vga_b:       std_logic_vector(9 downto 0);
    signal vga_blank:   std_logic;
    signal vga_sync:    std_logic;
    signal vga_hsync:   std_logic;
    signal vga_vsync:   std_logic;

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
                    port map(eClk => clk,
                             eRst => rst,
                             eR => r,
                             eG => g,
                             eB => b,

                             pixel_x => pixel_x,
                             pixel_y => pixel_y,

                             sClk => vga_clk,
                             sR => vga_r,
                             sG => vga_g,
                             sB => vga_b,
                             sBlank => vga_blank,
                             sSync => vga_sync,
                             sHSync => vga_hsync,
                             sVSync => vga_vsync);

    sva:    adv7123_sva_wrapper;

    process (all)
    begin
        if (rst = '1') then
            r <= "1111111111";
            g <= "1111111111";
            b <= "1111111111";
        else
            g <= "0000000000";
            b <= "0000000000";
            if (pixel_y(0) = '0') then
                if (pixel_x(0) = '0') then
                    r <= "1111111111";
                else
                    r <= "0000000000";
                end if;
            else
                if (pixel_x(0) = '0') then
                    r <= "0000000000";
                else
                    r <= "1111111111";
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
        wait for 100 ns;
        rst <= '0';
        wait for (2 * FRAME_TIME);
        rst <= '1';
        wait for 100 ns;
        std.env.stop;
    end process;

end architecture sim;