library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library work;
use work.all;

entity adv7123 is
    -------------------------------------
    -- There are predefined timing in
    -- vga_timings_pkg.vhd.
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

    port (clk:          in  std_ulogic;
          rst:          in  std_ulogic;
          rIn:          in  std_ulogic_vector(9 downto 0);
          gIn:          in  std_ulogic_vector(9 downto 0);
          bIn:          in  std_ulogic_vector(9 downto 0);
          pixelX:       out unsigned((utils_pkg.min_width(H_ACTIVE) - 1) downto 0);
          pixelY:       out unsigned((utils_pkg.min_width(V_ACTIVE) - 1) downto 0);
          endOfFrame:   out std_ulogic;
          clkOut:       out std_ulogic;
          rOut:         out std_ulogic_vector(9 downto 0);
          gOut:         out std_ulogic_vector(9 downto 0);
          bOut:         out std_ulogic_vector(9 downto 0);
          nBlank:       out std_ulogic;
          nSync:        out std_ulogic;
          nHSync:       out std_ulogic;
          nVSync:       out std_ulogic);

end entity adv7123;

architecture synth of adv7123 is
    component vga is
        generic (H_ACTIVE:      natural;    -- ticks
                 H_FRONT_PORCH: natural;    -- ticks
                 H_SYNC:        natural;    -- ticks
                 H_BACK_PORCH:  natural;    -- ticks
                 --
                 V_ACTIVE:      natural;    -- líneas
                 V_FRONT_PORCH: natural;    -- líneas
                 V_SYNC:        natural;    -- líneas
                 V_BACK_PORCH:  natural);   -- líneas

        port (clk:          in  std_ulogic;
              rst:          in  std_ulogic;
              pixelX:       out unsigned((utils_pkg.min_width(H_ACTIVE) - 1) downto 0);
              pixelY:       out unsigned((utils_pkg.min_width(V_ACTIVE) - 1) downto 0);
              endOfFrame:   out std_ulogic;
              inActive:     out std_ulogic;
              nHSync:       out std_ulogic;
              nVSync:       out std_ulogic);

    end component vga;

    signal inActive:        std_ulogic;
    signal nHSyncAux:       std_ulogic;
    signal nVSyncAux:       std_ulogic;
    signal endOfFrameAux:   std_ulogic;
begin

    vgaInst:    vga generic map (H_ACTIVE       => H_ACTIVE,
                                 H_FRONT_PORCH  => H_FRONT_PORCH,
                                 H_SYNC         => H_SYNC,
                                 H_BACK_PORCH   => H_BACK_PORCH,
                                 V_ACTIVE       => V_ACTIVE,
                                 V_FRONT_PORCH  => V_FRONT_PORCH,
                                 V_SYNC         => V_SYNC,
                                 V_BACK_PORCH   => V_BACK_PORCH)
                    port map (clk => clk,
                              rst => rst,
                              pixelX => pixelX,
                              pixelY => pixelY,
                              inActive => inActive,
                              nHSync => nHSyncAux,
                              nVSync => nVSyncAux,
                              endOfFrame => endOfFrameAux);

    -- the output clock that goes to the ADV7123 is
    -- the input clock.
    clkOut <= clk;

    process(clk,rst)
    begin
        if (rst) then
            rOut <= (others => '0');
            gOut <= (others => '0');
            bOut <= (others => '0');
            nBlank <= '0';
            nSync  <= '0';
            nHSync <= '0';
            nVSync <= '0';
            endOfFrame <= '0';
        elsif (rising_edge(clk)) then
            -- inActive is active high
            -- blank <= not inActive
            -- nBlank <= not blank <= inActive
            nBlank <= inActive;

            -- nSync is active low
            -- when nHSync = 0 or nVSync = 0
            -- nSync <= !(!nHSync | !nVSync) = nHSync and nVSync
            nSync <= nHSyncAux and nVSyncAux;

            nHSync <= nHSyncAux;
            nVSync <= nVSyncAux;

            endOfFrame <= endOfFrameAux;

            if (inActive = '1') then
                rOut <= rIn;
                gOut <= gIn;
                bOut <= bIn;
            else
                rOut <= (others => '0');
                gOut <= (others => '0');
                bOut <= (others => '0');
            end if;
        end if;
    end process;

end architecture synth;
