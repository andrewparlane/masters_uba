library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.vga_timings_800_600_pkg.all;

entity tp2_tb is
end entity tp2_tb;

architecture sim of tp2_tb is

    component tp2 is
        port (CLOCK_50:             in  std_ulogic;
              KEY:                  in  std_ulogic_vector(0 downto 0);
              VGA_R:                out std_ulogic_vector(9 downto 0);
              VGA_G:                out std_ulogic_vector(9 downto 0);
              VGA_B:                out std_ulogic_vector(9 downto 0);
              DATA_VOLT_IN_DIFF:    in  std_ulogic;
              DATA_VOLT_OUT:        out std_ulogic;
              VGA_CLK:              out std_ulogic;
              VGA_BLANK:            out std_ulogic;
              VGA_HS:               out std_ulogic;
              VGA_VS:               out std_ulogic;
              VGA_SYNC:             out std_ulogic);
    end component tp2;

    component adv7123_sva_wrapper is
    end component adv7123_sva_wrapper;

    signal clk:         std_ulogic := '0';
    signal rst:         std_ulogic := '1';

    -- key(0) <= not rst;
    signal key:         std_ulogic_vector(0 downto 0) := "0";

    -- la entrada diferencial
    signal vIn:         std_ulogic := '0';

    -- señales VGA
    signal vga_clk:     std_ulogic;
    signal vga_r:       std_ulogic_vector(9 downto 0);
    signal vga_g:       std_ulogic_vector(9 downto 0);
    signal vga_b:       std_ulogic_vector(9 downto 0);
    signal vga_blank:   std_ulogic;
    signal vga_sync:    std_ulogic;
    signal vga_hs:     std_ulogic;
    signal vga_vs:     std_ulogic;

    -- 50 MHz
    constant CLK_HZ:        natural := 50 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;
    constant FRAME_TIME:    time := getFrameTime(CLK_PERIOD);
begin

    clk <= not clk after (CLK_PERIOD/2);

    -- Cambiamos vIn a CLK_HZ/2, así 50% 1, 50% 0 => 1.25V
    vIn <= not vIn after CLK_PERIOD;

    key(0) <= not rst;

    dut:    tp2 port map (CLOCK_50 => clk,
                          KEY => key,
                          VGA_R => vga_r,
                          VGA_G => vga_g,
                          VGA_B => vga_b,
                          DATA_VOLT_IN_DIFF => vIn,
                          DATA_VOLT_OUT => open,
                          VGA_CLK => vga_clk,
                          VGA_BLANK => vga_blank,
                          VGA_HS => vga_hs,
                          VGA_VS => vga_vs,
                          VGA_SYNC => vga_sync);

    -- Para capturar la salida VGA por uso con
    -- https://ericeastwood.com/lab/vga-simulator/
    sva:    adv7123_sva_wrapper;

    process
    begin
        rst <= '1';
        wait for CLK_PERIOD*5;
        rst <= '0';
        wait for (1 * FRAME_TIME);
        std.env.stop;
    end process;

end architecture sim;
