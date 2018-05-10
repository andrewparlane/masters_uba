library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.std_logic_textio.all;
use std.textio.all;

library common;
use common.all;

use work.adv7123_800_600_valores.all;
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

    component char_rom is
        port (clk:  in  std_logic;
              rst:  in  std_logic;
              char: in  charRomCharacter;
              offX: in  unsigned(3 downto 0);
              offY: in  unsigned(4 downto 0);
              px:   out std_logic);
    end component char_rom;

    component adv7123_sva_wrapper is
    end component adv7123_sva_wrapper;

    signal r: std_logic_vector(9 downto 0);
    signal g: std_logic_vector(9 downto 0);
    signal b: std_logic_vector(9 downto 0);

    signal pixel_x:     unsigned((PIXEL_X_WIDTH - 1) downto 0);
    signal pixel_y:     unsigned((PIXEL_Y_WIDTH - 1) downto 0);

    signal char: charRomCharacter;
    signal offX: unsigned(3 downto 0) := (others => '0');
    signal offY: unsigned(4 downto 0) := (others => '0');
    signal px:   std_logic;

    -- los carácteres son 16*32
    -- 800 / 16 = 50 (6 bits)
    signal bloqueX: unsigned(5 downto 0);
    -- 600 / 32 = 18.75 = 19 (5 bits)
    signal bloqueY: unsigned(4 downto 0);

    signal clk: std_logic := '0';
    signal rst: std_logic := '0';

    signal VGA_R:      std_logic_vector(9 downto 0);
    signal VGA_G:      std_logic_vector(9 downto 0);
    signal VGA_B:      std_logic_vector(9 downto 0);
    signal VGA_CLK:    std_logic;
    signal VGA_BLANK:  std_logic;
    signal VGA_HS:     std_logic;
    signal VGA_VS:     std_logic;
    signal VGA_SYNC:   std_logic;

    -- 50 MHz
    constant CLK_HZ:        natural := 50 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;

    constant LINE_TIME:     time := getLineTime(CLK_PERIOD);
    constant FRAME_TIME:    time := getFrameTime(CLK_PERIOD);
begin

    clk <= not clk after (CLK_PERIOD/2);

    bloqueX <= pixel_x((PIXEL_X_WIDTH - 1) downto 4);   -- /16
    bloqueY <= pixel_y((PIXEL_Y_WIDTH - 1) downto 5);   -- /32

    offX <= pixel_x(3 downto 0);
    offy <= pixel_y(4 downto 0);

    process (all)
    begin
        r <= (others => px);
        g <= (others => px);
        b <= (others => px);
        if (bloqueY = to_unsigned(9, bloqueY'length)) then
            if (bloqueX = to_unsigned(19, bloqueX'length)) then
                char <= 'H';
            elsif (bloqueX = to_unsigned(20, bloqueX'length)) then
                char <= 'e';
            elsif (bloqueX = to_unsigned(21, bloqueX'length)) then
                char <= 'l';
            elsif (bloqueX = to_unsigned(22, bloqueX'length)) then
                char <= 'l';
            elsif (bloqueX = to_unsigned(23, bloqueX'length)) then
                char <= 'o';
            elsif (bloqueX = to_unsigned(25, bloqueX'length)) then
                char <= 'W';
            elsif (bloqueX = to_unsigned(26, bloqueX'length)) then
                char <= 'o';
            elsif (bloqueX = to_unsigned(27, bloqueX'length)) then
                char <= 'r';
            elsif (bloqueX = to_unsigned(28, bloqueX'length)) then
                char <= 'l';
            elsif (bloqueX = to_unsigned(29, bloqueX'length)) then
                char <= 'd';
            else
                char <= ' ';
            end if;
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
                    port map(eClk => clk,
                             eRst => rst,
                             eR => r,
                             eG => g,
                             eB => b,

                             pixel_x => pixel_x,
                             pixel_y => pixel_y,

                             sClk   => VGA_CLK,
                             sR     => VGA_R,
                             sG     => VGA_G,
                             sB     => VGA_B,
                             sBlank => VGA_BLANK,
                             sSync  => VGA_SYNC,
                             sHSync => VGA_HS,
                             sVSync => VGA_VS);

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