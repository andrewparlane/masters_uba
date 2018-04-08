library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity tp1 is
    generic (CLOCK_DIVIDER: natural := 1);
    port (CLOCK_50: in  std_logic;
          KEY:      in  std_logic_vector(1 downto 0);
          HEX0:     out std_logic_vector(6 downto 0);
          HEX1:     out std_logic_vector(6 downto 0);
          HEX2:     out std_logic_vector(6 downto 0);
          HEX3:     out std_logic_vector(6 downto 0));
end entity tp1;

architecture synth of tp1 is

    component contador is
        generic (WIDTH: natural;
                 MAX: natural);
        port (clk:      in  std_logic;
              en:       in  std_logic;
              rst:      in  std_logic;
              load:     in  std_logic;
              loadData: in  unsigned((WIDTH - 1) downto 0);
              o:        out unsigned((WIDTH - 1) downto 0);
              atMax:    out std_logic);
    end component contador;

    component sevenSegmentDisplay is
        port (n:        in  unsigned(3 downto 0);
              o:        out std_logic_vector(6 downto 0));
    end component sevenSegmentDisplay;

    -- Tenemos CLOCK_DIVIDER así que el banco de prueba
    -- no necesita simular 50.000.000 ticks para incrementar
    -- dígito 0 una vez.
    -- Usamos -1 aquí por que 0,1,2,3,4,5,0 es 6 ticks
    constant    ONE_HZ_EN_MAX:  natural := (50000000 / CLOCK_DIVIDER) - 1;
    constant    ONE_KHZ_EN_MAX: natural := (50000 / CLOCK_DIVIDER) - 1;

    signal d0en1Hz, d0en1KHz:           std_logic;
    signal d0en, d1en, d2en, d3en:      std_logic;
    signal d0atMax, d1atMax, d2atMax:   std_logic;
    signal d0out, d1out, d2out, d3out:  unsigned (3 downto 0);

    signal rst:                         std_logic;
    signal fast:                        std_logic;
begin

    -- KEY(0) es nRESET (activa baja).
    -- KEY(1) es para contar más rápido (activa baja).
    rst <= not KEY(0);
    fast <= not KEY(1);

    -- el primer dígito cuenta a 1Hz en modo normal,
    -- y 1KHz en modo rápido.
    d0en <= d0en1KHz when (fast = '1') else d0en1Hz;

    -- un dígito cuenta si el dígito anterior hace el transición 9 -> 0
    -- (en and atMax)
    d1en <= d0en and d0atMax;
    d2en <= d1en and d1atMax;
    d3en <= d2en and d2atMax;

    -- generar enable @ 1Hz desde 50MHz clk
    en1Hz_inst: contador
                generic map    (WIDTH => 26,
                                MAX => ONE_HZ_EN_MAX)
                port map       (clk => CLOCK_50,
                                en => '1',
                                rst => rst,
                                load => '0',
                                loadData => to_unsigned(0, 26),
                                -- o,
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
                                -- o,
                                atMax => d0en1KHz);

    -- dígito 0, 0-9
    d0Contador_inst:    contador
                        generic map    (WIDTH => 4,
                                        MAX => 9)
                        port map       (clk => CLOCK_50,
                                        en => d0en,
                                        rst => rst,
                                        load => '0',
                                        loadData => to_unsigned(0, 4),
                                        o => d0out,
                                        atMax => d0atMax);

    d0Display_inst:     sevenSegmentDisplay
                        port map       (n => d0out,
                                        o => HEX0);

    -- dígito 1, 0-9
    d1Contador_inst:    contador
                        generic map    (WIDTH => 4,
                                        MAX => 9)
                        port map       (clk => CLOCK_50,
                                        en => d1en,
                                        rst => rst,
                                        load => '0',
                                        loadData => to_unsigned(0, 4),
                                        o => d1out,
                                        atMax => d1atMax);

    d1Display_inst:     sevenSegmentDisplay
                        port map       (n => d1out,
                                        o => HEX1);

    -- dígito 2, 0-9
    d2Contador_inst:    contador
                        generic map    (WIDTH => 4,
                                        MAX => 9)
                        port map       (clk => CLOCK_50,
                                        en => d2en,
                                        rst => rst,
                                        load => '0',
                                        loadData => to_unsigned(0, 4),
                                        o => d2out,
                                        atMax => d2atMax);

    d2Display_inst:     sevenSegmentDisplay
                        port map       (n => d2out,
                                        o => HEX2);

    -- dígito 3, 0-9
    d3Contador_inst:    contador
                        generic map    (WIDTH => 4,
                                        MAX => 9)
                        port map       (clk => CLOCK_50,
                                        en => d3en,
                                        rst => rst,
                                        load => '0',
                                        loadData => to_unsigned(0, 4),
                                        o => d3out);
                                        -- atMax,

    d3Display_inst:     sevenSegmentDisplay
                        port map       (n => d3out,
                                        o => HEX3);

end architecture synth;
