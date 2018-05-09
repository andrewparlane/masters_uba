library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;
use common.type_pkg.all;

entity adc is
    port (clk:          in  std_logic;
          rst:          in  std_logic;
          dInDiff:      in  std_logic;
          dOut:         out std_logic;
          resultado:    out unsignedArray(2 downto 0)(3 downto 0));
end entity adc;

architecture synth of adc is

    -- contador de lib common
    component contador is
        generic (WIDTH: natural;
                 MAX: natural);
        port (clk:      in  std_logic;
              en:       in  std_logic;
              rst:      in  std_logic;
              load:     in  std_logic;
              loadData: in  unsigned((WIDTH - 1) downto 0);
              count:    out unsigned((WIDTH - 1) downto 0);
              atZero:   out std_logic;
              atMax:    out std_logic);
    end component contador;

    -- de lib common
    component contador_bcd is
        generic (CIFRAS: natural);
        port (clk:      in  std_logic;
              en:       in  std_logic;
              rst:      in  std_logic;
              dOut:     out unsignedArray((CIFRAS-1) downto 0)(3 downto 0));
    end component contador_bcd;

    signal dOutAux:                 std_logic;
    signal bcdRst:                  std_logic;
    signal contadorBinarioZero:     std_logic;
    signal contadorBinarioMax:      std_logic;

    signal bcdOut:      unsignedArray(4 downto 0)(3 downto 0);
begin

    -----------------------------------------------------------------
    -- Guardamos dInDiff en un registro
    -- y asignar a dOut
    -----------------------------------------------------------------
    --
    --        |\            ___
    --        | \          |   |
    --     ---|+ \_________|D Q|_________
    --     ---|- / dInDiff |>  |  |
    --        | /          |___|  |
    --        |/                  |
    --     _______________________|
    --      dOut
    --
    -----------------------------------------------------------------
    dOut <= dOutAux;
    process (clk)
    begin
        if (rising_edge(clk)) then
            dOutAux <= dInDiff;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Contamos desde 0 a 25001 con un contador binario.
    -----------------------------------------------------------------
    contBin:    contador    generic map (WIDTH => 15,
                                         MAX => 25001)
                            port map (clk => clk,
                                      rst => rst,
                                      en => '1',
                                      load => '0',
                                      loadData => to_unsigned(0, 15),
                                      count => open,
                                      atZero => contadorBinarioZero,
                                      atMax => contadorBinarioMax);

    -----------------------------------------------------------------
    -- usamos dOut por el en de un contador BCD de 5 cifras.
    -- El contador BCD es en reset cuando estamos en reset
    -- o cuando el contador binario es cero.
    -----------------------------------------------------------------
    bcdRst <= contadorBinarioZero OR rst;
    contBcd:    contador_bcd    generic map (CIFRAS => 5)
                                port map (clk => clk,
                                          en => dOutAux,
                                          rst => bcdRst,
                                          dOut => bcdOut);

    -----------------------------------------------------------------
    -- El resultado es el valor de bcdOut cuando el contador
    -- binario es a su valor máxima (25001) eso da un valor
    -- máxima de BCD a 25000
    -----------------------------------------------------------------
    process (clk, rst)
    begin
        if (rst) then
            resultado <= (others => "0000");
        elsif (rising_edge(clk)) then
            if (contadorBinarioMax = '1') then
                resultado <= bcdOut(4 downto 2);
            end if;
        end if;
    end process;

end architecture synth;
