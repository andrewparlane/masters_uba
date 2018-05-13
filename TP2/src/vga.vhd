library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;

entity vga is
    -------------------------------------
    -- Hay valores predefinidos en
    -- vga_timings_pkg.vhd
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

    port (clk:      in  std_ulogic;
          rst:      in  std_ulogic;
          pixelX:   out unsigned((utils_pkg.min_width(H_ACTIVE) - 1) downto 0);
          pixelY:   out unsigned((utils_pkg.min_width(V_ACTIVE) - 1) downto 0);
          inActive: out std_ulogic;
          nHSync:   out std_ulogic;
          nVSync:   out std_ulogic);

end entity vga;

architecture synth of vga is

    -- contador de lib common
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

    constant COUNTER_X_WIDTH:   natural := utils_pkg.min_width(H_TOTAL - 1);
    constant COUNTER_Y_WIDTH:   natural := utils_pkg.min_width(V_TOTAL - 1);

    signal x: unsigned((COUNTER_X_WIDTH - 1) downto 0);
    signal y: unsigned((COUNTER_Y_WIDTH - 1) downto 0);

    signal xAtMax: std_ulogic;
begin

    -------------------------------------------------------------------------------------
    -- los contadores
    -------------------------------------------------------------------------------------
    xCont:  contador    generic map (WIDTH => COUNTER_X_WIDTH,
                                     MAX => H_TOTAL - 1)
                        port map (clk => clk,
                                  rst => rst,
                                  en => '1',
                                  load => '0',
                                  loadData => to_unsigned(0, x'length),
                                  count => x,
                                  atZero => open,
                                  atMax => xAtMax);

    yCont:  contador    generic map (WIDTH => COUNTER_Y_WIDTH,
                                     MAX => V_TOTAL - 1)
                        port map (clk => clk,
                                  rst => rst,
                                  en => xAtMax,
                                  load => '0',
                                  loadData => to_unsigned(0, y'length),
                                  count => y,
                                  atZero => open,
                                  atMax => open);

    -------------------------------------------------------------------------------------
    -- Salidas
    -------------------------------------------------------------------------------------

    process (clk, rst)
    begin
        if (rst = '1') then
            nHSync <= '0';      -- activo bajo
            nVSync <= '0';      -- activo bajo
            inActive <= '0';    -- activo alto
            pixelX <= (others => '0');
            pixelY <= (others => '0');
        elsif (rising_edge(clk)) then
            -- nHSync está activo (bajo) durante el hsync
            if ((x >= H_SYNC_START) and
                (x < H_BP_START)) then
                nHSync <= '0';
            else
                nHSync <= '1';
            end if;

            -- nVSync está activo (bajo) durante el vsync
            if ((y >= V_SYNC_START) and
                (y < V_BP_START)) then
                nVSync <= '0';
            else
                nVSync <= '1';
            end if;

            if ((x < H_ACTIVE_START) or
                (y < V_ACTIVE_START)) then
                pixelX <= (others => '0');
            else
                pixelX <= resize(x - to_unsigned(H_ACTIVE_START, x'length),
                                  pixelX'length);
            end if;

            if ((y < V_ACTIVE_START)) then
                pixelY <= (others => '0');
            else
                pixelY <= resize(y - to_unsigned(V_ACTIVE_START, y'length),
                                  pixelY'length);
            end if;

            -- estamos en la región activo?
            if ((x < H_ACTIVE_START) or
                (y < V_ACTIVE_START)) then
                inActive <= '0';
            else
                inActive <= '1';
            end if;
        end if;
    end process;

end architecture synth;
