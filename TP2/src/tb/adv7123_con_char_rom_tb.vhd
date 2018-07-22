library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_textio.all;
use std.textio.all;

library common;
use common.all;

use work.vga_timings_800_600_pkg.all;
use work.char_rom_pkg.all;

entity adv7123_con_char_rom_tb is
end entity adv7123_con_char_rom_tb;

architecture sim of adv7123_con_char_rom_tb is

    component adv7123 is
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
              rIn:      in  std_ulogic_vector(9 downto 0);
              gIn:      in  std_ulogic_vector(9 downto 0);
              bIn:      in  std_ulogic_vector(9 downto 0);
              pixelX:   out unsigned((utils_pkg.min_width(H_ACTIVE) - 1) downto 0);
              pixelY:   out unsigned((utils_pkg.min_width(V_ACTIVE) - 1) downto 0);
              clkOut:   out std_ulogic;
              rOut:     out std_ulogic_vector(9 downto 0);
              gOut:     out std_ulogic_vector(9 downto 0);
              bOut:     out std_ulogic_vector(9 downto 0);
              nBlank:   out std_ulogic;
              nSync:    out std_ulogic;
              nHSync:   out std_ulogic;
              nVSync:   out std_ulogic);
    end component adv7123;

    component char_rom is
        port (clk:  in  std_ulogic;
              rst:  in  std_ulogic;
              char: in  charRomCharacter;
              offX: in  unsigned(3 downto 0);
              offY: in  unsigned(4 downto 0);
              px:   out std_ulogic);
    end component char_rom;

    component adv7123_sva_wrapper is
    end component adv7123_sva_wrapper;

    signal r: std_ulogic_vector(9 downto 0);
    signal g: std_ulogic_vector(9 downto 0);
    signal b: std_ulogic_vector(9 downto 0);

    signal pixelX:     unsigned((PIXEL_X_WIDTH - 1) downto 0);
    signal pixelY:     unsigned((PIXEL_Y_WIDTH - 1) downto 0);

    signal char: charRomCharacter;
    signal offX: unsigned(3 downto 0) := (others => '0');
    signal offY: unsigned(4 downto 0) := (others => '0');
    signal px:   std_ulogic;

    -- los carácteres son 16*32
    -- 800 / 16 = 50 (6 bits)
    signal bloqueX: unsigned(5 downto 0);
    -- 600 / 32 = 18.75 = 19 (5 bits)
    signal bloqueY: unsigned(4 downto 0);

    signal clk: std_ulogic := '0';
    signal rst: std_ulogic := '0';

    signal VGA_R:      std_ulogic_vector(9 downto 0);
    signal VGA_G:      std_ulogic_vector(9 downto 0);
    signal VGA_B:      std_ulogic_vector(9 downto 0);
    signal VGA_CLK:    std_ulogic;
    signal VGA_BLANK:  std_ulogic;
    signal VGA_HS:     std_ulogic;
    signal VGA_VS:     std_ulogic;
    signal VGA_SYNC:   std_ulogic;

    -- 50 MHz
    constant CLK_HZ:        natural := 50 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;

    constant LINE_TIME:     time := getLineTime(CLK_PERIOD);
    constant FRAME_TIME:    time := getFrameTime(CLK_PERIOD);
begin

    clk <= not clk after (CLK_PERIOD/2);

    bloqueX <= pixelX((PIXEL_X_WIDTH - 1) downto 4);   -- /16
    bloqueY <= pixelY((PIXEL_Y_WIDTH - 1) downto 5);   -- /32

    offX <= pixelX(3 downto 0);
    offy <= pixelY(4 downto 0);

    process (all)
    begin
        r <= (others => px);
        g <= (others => px);
        b <= (others => px);
        if (bloqueY = to_unsigned(9, bloqueY'length)) then
            case to_integer(bloqueX) is
                when 19 => char <= 'H';
                when 20 => char <= 'e';
                when 21 => char <= 'l';
                when 22 => char <= 'l';
                when 23 => char <= 'o';
                when 25 => char <= 'W';
                when 26 => char <= 'o';
                when 27 => char <= 'r';
                when 28 => char <= 'l';
                when 29 => char <= 'd';
                when others => char <= ' ';
            end case;
        else
            char <= ' ';
        end if;
    end process;

    inst:   adv7123 generic map(H_ACTIVE        => H_ACTIVE,
                                H_FRONT_PORCH   => H_FRONT_PORCH,
                                H_SYNC          => H_SYNC,
                                H_BACK_PORCH    => H_BACK_PORCH,
                                V_ACTIVE        => V_ACTIVE,
                                V_FRONT_PORCH   => V_FRONT_PORCH,
                                V_SYNC          => V_SYNC,
                                V_BACK_PORCH    => V_BACK_PORCH)
                    port map(clk => clk,
                             rst => rst,
                             rIn => r,
                             gIn => g,
                             bIn => b,

                             pixelX => pixelX,
                             pixelY => pixelY,

                             clkOut => VGA_CLK,
                             rOut   => VGA_R,
                             gOut   => VGA_G,
                             bOut   => VGA_B,
                             nBlank => VGA_BLANK,
                             nSync  => VGA_SYNC,
                             nHSync => VGA_HS,
                             nVSync => VGA_VS);

    cRom: char_rom  port map(clk => clk,
                             rst => rst,
                             char => char,
                             offX => offX,
                             offY => offY,
                             px => px);

    sva:    adv7123_sva_wrapper;

    process
    begin
        rst <= '1';
        wait for 100 ns;
        rst <= '0';
        wait for (3 * FRAME_TIME);
        std.env.stop;
    end process;

end architecture sim;