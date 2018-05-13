library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;
use common.type_pkg.all;

use work.vga_timings_800_600_pkg.all;
use work.char_rom_pkg.all;

-- DATA_VOLT_IN_DIFFp = LVDS110p = N18 = GPIO_B10 = IO_A10 = JP1.13
-- DATA_VOLT_IN_DIFFn = LVDS110n = P18 = GPIO_B11 = IO_A11 = JP1.14
-- DATA_VOLT_OUT                 = D25 = GPIO_B0  = IO_A0  = JP1.16
-- VCC33                                                   = JP1.29
-- GND                                                     = JP1.30

entity tp2 is
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

end entity tp2;

architecture synth of tp2 is

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

    component adc is
        port (clk:          in  std_ulogic;
              rst:          in  std_ulogic;
              dInDiff:      in  std_ulogic;
              dOut:         out std_ulogic;
              resultado:    out unsignedArray(2 downto 0)(3 downto 0));
    end component adc;

    -- reset con KEY[0]
    signal rst: std_ulogic;

    -- Pixel valores RGB
    signal r: std_ulogic_vector(9 downto 0);
    signal g: std_ulogic_vector(9 downto 0);
    signal b: std_ulogic_vector(9 downto 0);

    -- Qué es el corriente pixel?
    signal pixelX:     unsigned((PIXEL_X_WIDTH - 1) downto 0) := (others => '0');
    signal pixelY:     unsigned((PIXEL_Y_WIDTH - 1) downto 0) := (others => '0');

    -- Qué carácter queremos?
    signal char: charRomCharacter;

    -- Qué pixel en el carácter?
    signal offX: unsigned(3 downto 0) := (others => '0');
    signal offY: unsigned(4 downto 0) := (others => '0');

    -- El pixel es incendido?
    signal px:   std_ulogic;

    -- Dividimos la pantalla en 50x18 cuadras
    -- 800 / 16 = 50 (6 bits)
    -- 600 / 32 = 18.75 = 19 (5 bits)
    signal bloqueX: unsigned(5 downto 0);
    signal bloqueY: unsigned(4 downto 0);

    -- La última muestra (3 cifras BCD)
    signal muestra: unsignedArray(2 downto 0)(3 downto 0);

begin

    -- KEY es activo bajo, rst es activo alto
    rst <= not KEY(0);

    -- Dividir la pantalla en cuadras de 16x32 pixales
    bloqueX <= pixelX((PIXEL_X_WIDTH - 1) downto 4);   -- /16
    bloqueY <= pixelY((PIXEL_Y_WIDTH - 1) downto 5);   -- /32

    -- Obtener el offset en la cuadra corriente
    offX <= pixelX(3 downto 0);
    offy <= pixelY(4 downto 0);

    -- Obtener una muestra
    adc_inst:           adc port map (clk => CLOCK_50,
                                      rst => rst,
                                      dInDiff => DATA_VOLT_IN_DIFF,
                                      dOut => DATA_VOLT_OUT,
                                      resultado => muestra);

    -- Salida VGA con la DAC adv7123
    adv7123_inst:
    adv7123 generic map(H_ACTIVE        => H_ACTIVE,
                        H_FRONT_PORCH   => H_FRONT_PORCH,
                        H_SYNC          => H_SYNC,
                        H_BACK_PORCH    => H_BACK_PORCH,
                        V_ACTIVE        => V_ACTIVE,
                        V_FRONT_PORCH   => V_FRONT_PORCH,
                        V_SYNC          => V_SYNC,
                        V_BACK_PORCH    => V_BACK_PORCH)
            port map(clk => CLOCK_50,
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

    -- Un ROM de caracteres
    cRom: char_rom  port map(clk => CLOCK_50,
                             rst => rst,
                             char => char,
                             offX => offX,
                             offY => offY,
                             px => px);

    -- Escribir la muestra corriente a la pantalla
    process (all)
    begin
        r <= (others => px);
        g <= (others => px);
        b <= (others => px);

        if (bloqueY = 5) then
            case to_integer(bloqueX) is
                when  5 => char <= 'V';
                when  6 => char <= 'i';
                when  7 => char <= 'n';
                when  8 => char <= '(';
                when  9 => char <= '0';
                when 10 => char <= ')';
                when 11 => char <= ' ';
                when 12 => char <= '=';
                when 13 => char <= ' ';
                when 14 => char <= bcdToCharacter(muestra(2));
                when 15 => char <= '.';
                when 16 => char <= bcdToCharacter(muestra(1));
                when 17 => char <= bcdToCharacter(muestra(0));
                when 18 => char <= 'V';
                when others => char <= ' ';
            end case;
        else
            char <= ' ';
        end if;
    end process;

end architecture synth;
