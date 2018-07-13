library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library work;
use work.all;

entity adv7123 is
    -----------------------------------------------------------------
    -- There are predefined timing in vga_timings_pkg.vhd.
    -- DELAY_TICKS specifies how many ticks to delay the
    -- blanking and sync signals. This is for when it takes
    -- some number of ticks to provide the pixel data.
    -----------------------------------------------------------------
    generic (DELAY_TICKS:   natural := 1;

             H_ACTIVE:      natural;    -- ticks
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

    component delay is
        generic (DELAY: natural;
                 WIDTH: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              output:   out std_ulogic_vector((WIDTH - 1) downto 0));
    end component delay;

    signal inActive:            std_ulogic;
    signal inActiveDelayed:     std_ulogic;
    signal nHSyncAux:           std_ulogic;
    signal nHSyncDelayed:       std_ulogic;
    signal nVSyncAux:           std_ulogic;
    signal nVSyncDelayed:       std_ulogic;
    signal endOfFrameAux:       std_ulogic;
    signal endOfFrameDelayed:   std_ulogic;

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

    inActiveDelay: delay
        generic map (DELAY => DELAY_TICKS,
                     WIDTH => 1)
        port map (clk => clk,
                  rst => rst,
                  input(0) => inActive,
                  output(0) => inActiveDelayed);

    nHSyncDelay: delay
        generic map (DELAY => DELAY_TICKS,
                     WIDTH => 1)
        port map (clk => clk,
                  rst => rst,
                  input(0) => nHSyncAux,
                  output(0) => nHSyncDelayed);

    nVSyncDelay: delay
        generic map (DELAY => DELAY_TICKS,
                     WIDTH => 1)
        port map (clk => clk,
                  rst => rst,
                  input(0) => nVSyncAux,
                  output(0) => nVSyncDelayed);

    endOfFrameDelay: delay
        generic map (DELAY => DELAY_TICKS,
                     WIDTH => 1)
        port map (clk => clk,
                  rst => rst,
                  input(0) => endOfFrameAux,
                  output(0) => endOfFrameDelayed);

    process (all)
    begin
        -- inActive is active high
        -- blank <= not inActive
        -- nBlank <= not blank <= inActive
        nBlank <= inActiveDelayed;

        nHSync <= nHSyncDelayed;
        nVSync <= nVSyncDelayed;
        endOfFrame <= endOfFrameDelayed;

        -- nSync is active low
        -- when nHSync = 0 or nVSync = 0
        -- nSync <= !(!nHSync | !nVSync) = nHSync and nVSync
        nSync <= nHSyncDelayed and nVSyncDelayed;

        if (inActiveDelayed = '1') then
            rOut <= rIn;
            gOut <= gIn;
            bOut <= bIn;
        else
            rOut <= (others => '0');
            gOut <= (others => '0');
            bOut <= (others => '0');
        end if;
    end process;

end architecture synth;
