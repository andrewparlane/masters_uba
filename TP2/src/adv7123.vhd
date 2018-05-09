library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;

entity adv7123 is
    -------------------------------------
    -- Ejemplo de valores:
    -------------------------------------
    -- H_ACTIVE        => 800,  -- ticks
    -- H_FRONT_PORCH   => 15,   -- ticks
    -- H_SYNC          => 80,   -- ticks
    -- H_BACK_PORCH    => 160,  -- ticks
    --
    -- V_ACTIVE        => 600,  -- líneas
    -- V_FRONT_PORCH   => 1,    -- líneas
    -- V_SYNC          => 3,    -- líneas
    -- V_BACK_PORCH    => 21)   -- líneas
    -------------------------------------
    -- con esto valores y eClk @ 50MHz
    -- tenemos 75.83 cuadros por segundo
    -------------------------------------
    generic (H_ACTIVE:      natural;    -- ticks
             H_FRONT_PORCH: natural;    -- ticks
             H_SYNC:        natural;    -- ticks
             H_BACK_PORCH:  natural;    -- ticks
             --
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
          pixel_x:   out unsigned((utils.min_width(H_ACTIVE) - 1) downto 0);
          pixel_y:   out unsigned((utils.min_width(V_ACTIVE) - 1) downto 0);
          -- salidas del FPGA
          sClk:      out std_logic;
          sR:        out std_logic_vector(9 downto 0);
          sG:        out std_logic_vector(9 downto 0);
          sB:        out std_logic_vector(9 downto 0);
          sBlank:    out std_logic;
          sSync:     out std_logic;
          sHSync:    out std_logic;
          sVSync:    out std_logic);

end entity adv7123;

architecture synth of adv7123 is

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

    -------------------------------------------------------------------------------------
    -- Constantes
    -------------------------------------------------------------------------------------

    -- horizontal
    constant H_TOTAL:               natural := H_ACTIVE +
                                               H_FRONT_PORCH +
                                               H_SYNC +
                                               H_BACK_PORCH;

    -- fp -> hsync -> bp -> activo
    constant H_SYNC_START:          natural := H_FRONT_PORCH;
    constant H_BP_START:            natural := H_SYNC_START + H_SYNC;
    constant H_ACTIVE_START:        natural := H_BP_START + H_BACK_PORCH;

    -- Vertical
    constant V_TOTAL:               natural := V_ACTIVE +
                                               V_FRONT_PORCH +
                                               V_SYNC +
                                               V_BACK_PORCH;

    -- fp -> hsync -> bp -> activo
    constant V_SYNC_START:          natural := V_FRONT_PORCH;
    constant V_BP_START:            natural := V_SYNC_START + V_SYNC;
    constant V_ACTIVE_START:        natural := V_BP_START + V_BACK_PORCH;

    -------------------------------------------------------------------------------------
    -- señales por las contadoras
    -------------------------------------------------------------------------------------
    -- Tenemos dos contadoras:
    --   xCont: cuenta desde 0 hasta H_TOTAL y simepre esta activa.
    --   yCont: cuenta desde 0 hasta V_TOTAL y solo es activa cuando
    --          el valor de xCont está el máximo.
    -------------------------------------------------------------------------------------

    constant COUNTER_X_WIDTH:   natural := utils.min_width(H_TOTAL - 1);
    constant COUNTER_Y_WIDTH:   natural := utils.min_width(V_TOTAL - 1);

    signal x: unsigned((COUNTER_X_WIDTH - 1) downto 0);
    signal y: unsigned((COUNTER_Y_WIDTH - 1) downto 0);

    signal xAtMax: std_logic;

    -------------------------------------------------------------------------------------
    -- señales auxiliar
    -------------------------------------------------------------------------------------
    signal hSyncAux: std_logic;
    signal vSyncAux: std_logic;
begin

    -------------------------------------------------------------------------------------
    -- las contadoras
    -------------------------------------------------------------------------------------
    xCont:  contador    generic map (WIDTH => COUNTER_X_WIDTH,
                                     MAX => H_TOTAL - 1)
                        port map (clk => eClk,
                                  rst => eRst,
                                  en => '1',
                                  load => '0',
                                  loadData => to_unsigned(0, x'length),
                                  count => x,
                                  atZero => open,
                                  atMax => xAtMax);

    yCont:  contador    generic map (WIDTH => COUNTER_Y_WIDTH,
                                     MAX => V_TOTAL - 1)
                        port map (clk => eClk,
                                  rst => eRst,
                                  en => xAtMax,
                                  load => '0',
                                  loadData => to_unsigned(0, y'length),
                                  count => y,
                                  atZero => open,
                                  atMax => open);

    -------------------------------------------------------------------------------------
    -- Salidas
    -------------------------------------------------------------------------------------
    -- El reloj de píxeles es el reloj de entrada
    sClk <= eClk;

    -- sVSync y sHSync están los auxiliares
    sVSync <= vSyncAux;
    sHSync <= hSyncAux;

    -- sSync está activo (bajo) durante vsync o hsync
    -- todos están activo bajo, así:
    -- not ((not sVSync) or (not sHSync)) = a and b
    -- por De Morgan
    sSync <= vSyncAux and hSyncAux;

    process (eClk, eRst)
    begin
        if (eRst = '1') then
            sR <= (others => '0');
            sG <= (others => '0');
            sB <= (others => '0');
            hSyncAux <= '0';
            vSyncAux <= '0';
            sBlank <= '0';
        elsif (rising_edge(eClk)) then
            -- sHSync está activo (bajo) durante el hsync
            if ((x >= H_SYNC_START) and
                (x < H_BP_START)) then
                hSyncAux <= '0';
            else
                hSyncAux <= '1';
            end if;

            -- sVSync está activo (bajo) durante el vsync
            if ((y >= V_SYNC_START) and
                (y < V_BP_START)) then
                vSyncAux <= '0';
            else
                vSyncAux <= '1';
            end if;

            if ((x < H_ACTIVE_START) or
                (y < V_ACTIVE_START)) then
                -- sBlank está activo (bajo) cuando no estamos ACTIVO
                sBlank <= '0';
                sR <= (others => '0');
                sG <= (others => '0');
                sB <= (others => '0');
            else
                sBlank <= '1';
                -- Las salidas de RGB son las entradas
                sR <= eR;
                sG <= eG;
                sB <= eB;
            end if;
        end if;
    end process;

    process (all)
    begin
        if ((x < H_ACTIVE_START) or
            (y < V_ACTIVE_START)) then
            pixel_x <= (others => '0');
        else
            pixel_x <= resize(x - to_unsigned(H_ACTIVE_START, x'length),
                              pixel_x'length);
        end if;

        if ((y < V_ACTIVE_START)) then
            pixel_y <= (others => '0');
        else
            pixel_y <= resize(y - to_unsigned(V_ACTIVE_START, y'length),
                              pixel_y'length);
        end if;
    end process;

end architecture synth;
