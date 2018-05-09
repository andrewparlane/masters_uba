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

    constant H_FRONT_PORCH_START:   natural := H_ACTIVE - 1;
    constant H_SYNC_START:          natural := H_FRONT_PORCH_START + H_FRONT_PORCH;
    constant H_BACK_PORCH_START:    natural := H_SYNC_START + H_SYNC;

    -- Vertical
    constant V_TOTAL:               natural := V_ACTIVE +
                                               V_FRONT_PORCH +
                                               V_SYNC +
                                               V_BACK_PORCH;

    constant V_FRONT_PORCH_START:   natural := V_ACTIVE;
    constant V_SYNC_START:          natural := V_FRONT_PORCH_START + V_FRONT_PORCH;
    constant V_BACK_PORCH_START:    natural := V_SYNC_START + V_SYNC;

    -------------------------------------------------------------------------------------
    -- señales por la machina de estados
    -------------------------------------------------------------------------------------
    -- Usamos una machina de estados para determinar
    -- en que region estamos. Tenemos uno por lineas
    -- y uno por pixeles.
    -- Podríamos decir ACTIVE = (x < H_FRONT_PORCH_START)
    -- y similar para las otras regiones. Pero creo
    -- que una machina de estados usa menos recursos.
    -------------------------------------------------------------------------------------

    type estado is (RESET, ACTIVO, FP, SYNC, BP);
    signal hEstado: estado;
    signal vEstado: estado;
    signal hEstadoNext: estado;
    signal vEstadoNext: estado;

    signal enRegionActiva:  std_logic;

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
    signal yAtMax: std_logic;

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
                                  atMax => yAtMax);

    -------------------------------------------------------------------------------------
    -- registro de estado
    -------------------------------------------------------------------------------------
    process (eClk, eRst)
    begin
        if (eRst = '1') then
            hEstado <= RESET;
            vEstado <= RESET;
        elsif (rising_edge(eClk)) then
            --if (hEstado /= hEstadoNext) then
            --    report ("hEstado cambiando desde " & estado'image(hEstado) &
            --            " hasta " & estado'image(hEstadoNext));
            --end if;
            --if (vEstado /= vEstadoNext) then
            --    report ("vEstado cambiando desde " & estado'image(vEstado) &
            --            " hasta " & estado'image(vEstadoNext));
            --end if;
            hEstado <= hEstadoNext;
            vEstado <= vEstadoNext;
        end if;
    end process;

    -------------------------------------------------------------------------------------
    -- lógica de estado siguiente (hEstado)
    -------------------------------------------------------------------------------------
    siguinteEstadoH: process (all)
    begin
        case hEstado is
            when RESET =>
                hEstadoNext <= ACTIVO;
            when ACTIVO =>
                if (x = H_FRONT_PORCH_START) then
                    hEstadoNext <= FP;
                else
                    hEstadoNext <= ACTIVO;
                end if;
            when FP =>
                if (x = H_SYNC_START) then
                    hEstadoNext <= SYNC;
                else
                    hEstadoNext <= FP;
                end if;
            when SYNC =>
                if (x = H_BACK_PORCH_START) then
                    hEstadoNext <= BP;
                else
                    hEstadoNext <= SYNC;
                end if;
            when BP =>
                if (xAtMax = '1') then
                    hEstadoNext <= ACTIVO;
                else
                    hEstadoNext <= BP;
                end if;
        end case;
    end process siguinteEstadoH;

    -------------------------------------------------------------------------------------
    -- lógica de estado siguiente (vEstado)
    -------------------------------------------------------------------------------------
    siguinteEstadoV: process (all)
    begin
        case vEstado is
            when RESET =>
                vEstadoNext <= ACTIVO;
            when ACTIVO =>
                if (y = V_FRONT_PORCH_START) then
                    vEstadoNext <= FP;
                else
                    vEstadoNext <= ACTIVO;
                end if;
            when FP =>
                if (y = V_SYNC_START) then
                    vEstadoNext <= SYNC;
                else
                    vEstadoNext <= FP;
                end if;
            when SYNC =>
                if (y = V_BACK_PORCH_START) then
                    vEstadoNext <= BP;
                else
                    vEstadoNext <= SYNC;
                end if;
            when BP =>
                if ((yAtMax = '1') and
                    (xAtMax = '1')) then
                    vEstadoNext <= ACTIVO;
                else
                    vEstadoNext <= BP;
                end if;
        end case;
    end process siguinteEstadoV;


    -------------------------------------------------------------------------------------
    -- Salidas
    -------------------------------------------------------------------------------------
    -- El reloj de píxeles es el reloj de entrada
    sClk <= eClk;

    -- Las salidas de RGB son las entradas
    sR <= eR;
    sG <= eG;
    sB <= eB;

    -- estamos en la región activa?
    enRegionActiva <= '1' when ((hEstado = ACTIVO) and
                                (vEstado = ACTIVO))
                          else '0';

    -- sHSync está activo (bajo) durante el hsync
    sHsync <= '0' when (hEstado = SYNC) else '1';

    -- sVSync está activo (bajo) durante el vsync
    sVsync <= '0' when (vEstado = SYNC) else '1';

    -- sSync está activo (bajo) durante vsync o hsync
    sSync <= '0' when (hEstado = SYNC or
                       vEstado = SYNC)
                 else '1';

    -- sBlank está activo (bajo) cuando no estamos ACTIVO
    sBlank <= '0' when (not enRegionActiva)
                  else '1';

    pixel_x <= resize(x, pixel_x'length) when (enRegionActiva = '1')
               else to_unsigned(0, pixel_x'length);
    pixel_y <= resize(y, pixel_x'length) when (enRegionActiva = '1')
               else to_unsigned(0, pixel_y'length);

end architecture synth;
