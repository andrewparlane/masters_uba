library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library altera_mf;
use altera_mf.all;

entity buttons is
    port (i_clk:            in  std_ulogic;
          i_reset:          in  std_ulogic;
          i_buttonAlpha:    in  std_ulogic;
          i_buttonBeta:     in  std_ulogic;
          i_buttonGamma:    in  std_ulogic;
          i_reverse:        in  std_ulogic;
          i_update:         in  std_ulogic;
          o_alpha:          out unsigned(31 downto 0);
          o_beta:           out unsigned(31 downto 0);
          o_gamma:          out unsigned(31 downto 0));
end entity buttons;

architecture synth of buttons is

    component altera_std_synchronizer_bundle is
        generic (DEPTH : integer := 3;              -- must be >= 2
                 WIDTH : integer := 1);
        port (clk     : in  std_logic;
              reset_n : in  std_logic;
              din     : in  std_logic_vector(width-1 downto 0);
              dout    : out std_logic_vector(width-1 downto 0));
    end component altera_std_synchronizer_bundle;

    -- Everything below uses Q10.22 instead of the normal
    -- Q9.23. This is because 360 degrees in Q9.23
    -- is: 0xB4000000, so you have to be unsigned.
    -- Then you can't detect < 0.
    -- Whereas with Q10.22 we lose a small amount of precision
    -- which doesn't affect the value of our DELTA below.

    -- The spec says max rotation spped is: 35.15625 degrees/s.
    -- We pulse i_update once per frame.
    -- Our frame rate is ~60 frames per second
    -- so our delta is 0.5859375 degrees per frame.
    -- or in Q10.22: 2457600
    constant DELTA: signed(31 downto 0) := to_signed(2457600, 32);

    -- we wrap 0 <-> 360
    constant FIXED_360: signed(31 downto 0)
                := to_signed(360, 10) &
                   (21 downto 0 => '0');

    signal newAlpha:    signed(31 downto 0);
    signal newBeta:     signed(31 downto 0);
    signal newGamma:    signed(31 downto 0);

    signal alpha:       signed(31 downto 0);
    signal beta:        signed(31 downto 0);
    signal gamma:       signed(31 downto 0);

    signal buttonAlpha:     std_ulogic;
    signal buttonBeta:      std_ulogic;
    signal buttonGamma:     std_ulogic;
    signal reverse:         std_ulogic;
begin

    -- syncronize the buttons and reverse switch
    -- note we don't need to worry about the update signal
    -- not being in sync, because it's not that important
    -- since everything depends on when the user lets go
    -- of the button.
    sync: altera_std_synchronizer_bundle
        generic map (DEPTH => 2,
                     WIDTH => 4)
        port map    (clk        => i_clk,
                     reset_n    => not i_reset,
                     din(0)     => i_buttonAlpha,
                     din(1)     => i_buttonBeta,
                     din(2)     => i_buttonGamma,
                     din(3)     => i_reverse,
                     dout(0)    => buttonAlpha,
                     dout(1)    => buttonBeta,
                     dout(2)    => buttonGamma,
                     dout(3)    => reverse);


    process (all)
        variable alphaTmp:  signed(31 downto 0);
        variable betaTmp:   signed(31 downto 0);
        variable gammaTmp:  signed(31 downto 0);
    begin
        if (reverse = '1') then
            alphaTmp := alpha - DELTA;
            betaTmp  :=  beta - DELTA;
            gammaTmp := gamma - DELTA;

            if (alphaTmp < 0) then
                alphaTmp := alphaTmp + FIXED_360;
            end if;
            if (betaTmp < 0) then
                betaTmp := betaTmp + FIXED_360;
            end if;
            if (gammaTmp < 0) then
                gammaTmp := gammaTmp + FIXED_360;
            end if;
        else
            alphaTmp := alpha + DELTA;
            betaTmp  :=  beta + DELTA;
            gammaTmp := gamma + DELTA;

            if (alphaTmp >= FIXED_360) then
                alphaTmp := alphaTmp - FIXED_360;
            end if;
            if (betaTmp >= FIXED_360) then
                betaTmp := betaTmp - FIXED_360;
            end if;
            if (gammaTmp >= FIXED_360) then
                gammaTmp := gammaTmp - FIXED_360;
            end if;
        end if;

        newAlpha <= alphaTmp;
        newBeta  <= betaTmp;
        newGamma <= gammaTmp;
    end process;

    process (i_clk, i_reset)
    begin
        if (i_reset = '1') then
            alpha <= (others => '0');
            beta  <= (others => '0');
            gamma <= (others => '0');
        elsif (rising_edge(i_clk)) then
            if (i_update = '1') then
                -- only update them if the button is pressed
                if (buttonAlpha = '1') then
                    alpha <= newAlpha;
                end if;
                if (buttonBeta = '1') then
                    beta <= newBeta;
                end if;
                if (buttonGamma = '1') then
                    gamma <= newGamma;
                end if;
            end if;
        end if;
    end process;

    -- convert the outputs back to unsigned Q9.23
    o_alpha <= unsigned(alpha(30 downto 0) & '0');
    o_beta  <= unsigned(beta(30 downto 0) & '0');
    o_gamma <= unsigned(gamma(30 downto 0) & '0');

end architecture synth;
