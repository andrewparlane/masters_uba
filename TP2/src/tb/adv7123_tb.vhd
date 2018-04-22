library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;

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

    constant H_ACTIVE:      natural := 800; -- ticks
    constant H_FRONT_PORCH: natural := 15;  -- ticks
    constant H_SYNC:        natural := 80;  -- ticks
    constant H_BACK_PORCH:  natural := 160; -- ticks

    constant V_ACTIVE:      natural := 600; -- líneas
    constant V_FRONT_PORCH: natural := 1;   -- líneas
    constant V_SYNC:        natural := 3;   -- líneas
    constant V_BACK_PORCH:  natural := 21;  -- líneas

    constant PIXEL_X_WIDTH: natural := utils.min_width(H_ACTIVE);
    constant PIXEL_Y_WIDTH: natural := utils.min_width(V_ACTIVE);

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

    constant H_ACTIVE_TIME: time := H_ACTIVE        * CLK_PERIOD;
    constant H_FP_TIME:     time := H_FRONT_PORCH   * CLK_PERIOD;
    constant H_SYNC_TIME:   time := H_SYNC          * CLK_PERIOD;
    constant H_BP_TIME:     time := H_BACK_PORCH    * CLK_PERIOD;
    constant LINE_TIME:     time := H_ACTIVE_TIME   + H_FP_TIME +
                                    H_SYNC_TIME     + H_BP_TIME;

    constant V_ACTIVE_TIME: time := V_ACTIVE        * LINE_TIME;
    constant V_FP_TIME:     time := V_FRONT_PORCH   * LINE_TIME;
    constant V_SYNC_TIME:   time := V_SYNC          * LINE_TIME;
    constant V_BP_TIME:     time := V_BACK_PORCH    * LINE_TIME;
    constant FRAME_TIME:    time := V_ACTIVE_TIME   + V_FP_TIME +
                                    V_SYNC_TIME     + V_BP_TIME;
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

    process
    begin
        report ("CLK_HZ " & integer'image(CLK_HZ) & "Hz" &
                " -> periodo " & time'image(CLK_PERIOD) &
                " -> " & integer'image(1000000000 / (FRAME_TIME / 1 ns)) &
                " cuadras cada segundo");
        r <= "1111111111";
        g <= "0000000000";
        b <= "1010101010";
        rst <= '1';
        wait for 100 ns;
        rst <= '0';
        wait for (2 * FRAME_TIME);
        rst <= '1';
        wait for 100 ns;
        std.env.stop;
    end process;

end architecture sim;