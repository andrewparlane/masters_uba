library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;
use common.type_pkg.all;

entity tp1 is
    generic (CLOCK_DIVIDER: natural := 1);
    port (CLOCK_50: in  std_ulogic;
          KEY:      in  std_ulogic_vector(1 downto 0);
          HEX0:     out std_ulogic_vector(6 downto 0);
          HEX1:     out std_ulogic_vector(6 downto 0);
          HEX2:     out std_ulogic_vector(6 downto 0);
          HEX3:     out std_ulogic_vector(6 downto 0);
          HEX4:     out std_ulogic_vector(6 downto 0);
          HEX5:     out std_ulogic_vector(6 downto 0);
          HEX6:     out std_ulogic_vector(6 downto 0);
          HEX7:     out std_ulogic_vector(6 downto 0));
end entity tp1;

architecture synth of tp1 is

    component contador is
        generic (WIDTH: natural;
                 MAX: natural);
        port (clk:      in  std_ulogic;
              en:       in  std_ulogic;
              rst:      in  std_ulogic;
              load:     in  std_ulogic;
              loadData: in  unsigned((WIDTH - 1) downto 0);
              count:    out unsigned((WIDTH - 1) downto 0);
              atZero:   out std_ulogic;
              atMax:    out std_ulogic);
    end component contador;

    component contador_bcd is
        generic (CIFRAS: natural);
        port (clk:      in  std_ulogic;
              en:       in  std_ulogic;
              rst:      in  std_ulogic;
              dout:     out unsignedArray((CIFRAS-1) downto 0)(3 downto 0));
    end component contador_bcd;

    component multi_seven_seg_bcd is
        generic (CIFRAS: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              en:       in  std_ulogic_vector((CIFRAS - 1) downto 0);
              bcd:      in  unsignedArray((CIFRAS - 1) downto 0)(3 downto 0);
              display:  out slvArray((CIFRAS - 1) downto 0)(6 downto 0));
    end component multi_seven_seg_bcd;

    -- Tenemos CLOCK_DIVIDER así que el banco de prueba
    -- no necesita simular 50.000.000 ticks para incrementar
    -- dígito 0 una vez.
    -- Usamos -1 aquí por que 0,1,2,3,4,5,0 es 6 ticks
    constant    ONE_HZ_EN_MAX:  natural := (50000000 / CLOCK_DIVIDER) - 1;
    constant    ONE_KHZ_EN_MAX: natural := (50000 / CLOCK_DIVIDER) - 1;

    signal d0en1Hz, d0en1KHz:   std_ulogic;
    signal bcdEn:               std_ulogic;
    signal bcdOut:              unsignedArray(3 downto 0)(3 downto 0);

    signal rst:                 std_ulogic;
    signal fast:                std_ulogic;
begin

    -- KEY(0) es nRESET (activa baja).
    -- KEY(1) es para contar más rápido (activa baja).
    rst <= not KEY(0);
    fast <= not KEY(1);

    -- el primer dígito cuenta a 1Hz en modo normal,
    -- y 1KHz en modo rápido.
    bcdEn <= d0en1KHz when (fast = '1') else d0en1Hz;

    -- generar enable @ 1Hz desde 50MHz clk
    en1Hz_inst: contador
                generic map    (WIDTH => 26,
                                MAX => ONE_HZ_EN_MAX)
                port map       (clk => CLOCK_50,
                                en => '1',
                                rst => rst,
                                load => '0',
                                loadData => to_unsigned(0, 26),
                                count => open,
                                atZero => open,
                                atMax => d0en1Hz);

    -- generar enable @ 1KHz desde 50MHz clk
    en1KHz_inst: contador
                 generic map   (WIDTH => 16,
                                MAX => ONE_KHZ_EN_MAX)
                 port map      (clk => CLOCK_50,
                                en => '1',
                                rst => rst,
                                load => '0',
                                loadData => to_unsigned(0, 16),
                                count => open,
                                atZero => open,
                                atMax => d0en1KHz);

    -- El contador BCD de 4 cifras
    contBcd_inst:       contador_bcd
                        generic map     (CIFRAS => 4)
                        port map        (clk => CLOCK_50,
                                         en => bcdEn,
                                         rst => rst,
                                         dout => bcdOut);

    multi7SegInst:
    multi_seven_seg_bcd generic map (CIFRAS => 8)
                        port map (clk => CLOCK_50,
                                  rst => rst,
                                  en => "00001111",
                                  bcd(3 downto 0) => bcdOut,
                                  bcd(7 downto 4) => (to_unsigned(0,4),
                                                      to_unsigned(0,4),
                                                      to_unsigned(0,4),
                                                      to_unsigned(0,4)),
                                  display(7) => HEX7,
                                  display(6) => HEX6,
                                  display(5) => HEX5,
                                  display(4) => HEX4,
                                  display(3) => HEX3,
                                  display(2) => HEX2,
                                  display(1) => HEX1,
                                  display(0) => HEX0);

end architecture synth;
