library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;

entity transform is
    port (i_clk:                in  std_ulogic;
          i_reset:              in  std_ulogic;
          i_start:              in  std_ulogic;
          i_value:              in  signed(15 downto 0);
          i_valid:              in  std_ulogic;
          i_alpha:              in  unsigned(31 downto 0);
          i_beta:               in  unsigned(31 downto 0);
          i_gamma:              in  unsigned(31 downto 0);
          o_setPixelAddr:       out unsigned(15 downto 0);
          o_setPixelBitMask:    out unsigned(7 downto 0);
          o_setPixel:           out std_ulogic);
end entity transform;

architecture synth of transform is
    component cordic_rotation_3d is
        generic (N: natural;
                 M: natural;
                 STEPS: natural);
        port (i_clk:    in  std_ulogic;
              i_reset:  in  std_ulogic;
              i_en:     in  std_ulogic;
              i_x:      in  signed((N + M - 1) downto 0);
              i_y:      in  signed((N + M - 1) downto 0);
              i_z:      in  signed((N + M - 1) downto 0);
              i_alpha:  in  unsigned((N + M - 1) downto 0);
              i_beta:   in  unsigned((N + M - 1) downto 0);
              i_gamma:  in  unsigned((N + M - 1) downto 0);
              o_x:      out signed((N + M - 1) downto 0);
              o_y:      out signed((N + M - 1) downto 0);
              o_z:      out signed((N + M - 1) downto 0);
              o_valid:  out std_ulogic);
    end component cordic_rotation_3d;

    type coordinateComponent is
    (
        CoordinateComponent_X,
        CoordinateComponent_Y,
        CoordinateComponent_Z
    );

    signal currentComponent: coordinateComponent;

    signal cordic_en:       std_ulogic;
    signal aux:             signed(31 downto 0);
    signal original_x:      signed(31 downto 0);
    signal original_y:      signed(31 downto 0);
    signal original_z:      signed(31 downto 0);
    signal alpha:           unsigned(31 downto 0);
    signal beta:            unsigned(31 downto 0);
    signal gamma:           unsigned(31 downto 0);
    signal rotated_x:       signed(31 downto 0);
    signal rotated_y:       signed(31 downto 0);
    signal cordic_valid:    std_ulogic;

    signal cordic_valid_delayed:    std_ulogic;
    signal intX:                    unsigned(9 downto 0);
    signal intY:                    unsigned(8 downto 0);

begin

    -----------------------------------------------------------------
    -- Extend the value
    -----------------------------------------------------------------
    -- we extend the read sram data from Q6.10 to Q9.23
    -- adding zeros to the lower bits and sign extending the
    -- upper bits
    -----------------------------------------------------------------
    aux(12 downto 0) <= (others => '0');
    aux(28 downto 13) <= signed(i_value);
    aux(31 downto 29) <= (others => i_value(15));

    -----------------------------------------------------------------
    -- Set the correct component
    -----------------------------------------------------------------
    -- we only receive one value at a time
    -- so latch it in when valid to the correct copmonent
    -----------------------------------------------------------------
    process (i_clk, i_reset)
        variable comp:  coordinateComponent;
    begin
        if (i_reset = '1') then
            cordic_en <= '0';
            alpha <= (others => '0');
            beta <= (others => '0');
            gamma <= (others => '0');
        elsif (rising_edge(i_clk)) then
            -- deassert en (if it was set)
            cordic_en <= '0';

            if (i_start = '1') then
                comp := CoordinateComponent_X;
            else
                comp := currentComponent;
            end if;

            if (i_valid = '1') then
                if (comp = CoordinateComponent_X) then
                    original_x <= aux;
                    currentComponent <= CoordinateComponent_Y;
                elsif (comp = CoordinateComponent_Y) then
                    original_y <= aux;
                    currentComponent <= CoordinateComponent_Z;
                elsif (comp = CoordinateComponent_Z) then
                    original_z <= aux;
                    currentComponent <= CoordinateComponent_X;

                    -- now all the data is valid,
                    -- latch in the angles and
                    -- start the cordic
                    alpha <= i_alpha;
                    beta <= i_beta;
                    gamma <= i_gamma;
                    cordic_en <= '1';
                end if;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- CORDIC 3D
    -----------------------------------------------------------------
    cordic: cordic_rotation_3d
            generic map (N => 9,
                         M => 23,
                         STEPS => 10)
            port map (i_clk => i_clk,
                      i_reset => i_reset,
                      i_en => cordic_en,
                      i_x => original_x,
                      i_y => original_y,
                      i_z => original_z,
                      i_alpha => alpha,
                      i_beta  => beta,
                      i_gamma => gamma,
                      o_x => rotated_x,
                      o_y => rotated_y,
                      o_z => open,
                      o_valid => cordic_valid);

    -----------------------------------------------------------------
    -- Get pixel address and bit
    -----------------------------------------------------------------
    -- I've pipelined this because I was failing timing
    -- when trying to do it all as combinatory logic.
    -- First we get the integer part of the pixel co-ordinate
    -- and add an offset to it. This brings it into the domain
    -- of screen co-ordinates 0 - 639, 0 - 478.
    -- Then in the next tick, we do (y*WIDTH) + x, to get the
    -- pixel number, and split that into the bit to set and the
    -- byte to address.
    -----------------------------------------------------------------

    -- Get the pixel coordinate
    process (i_clk, i_reset)
        variable intXTmp:   signed(10 downto 0);
        variable intYTmp:   signed(9 downto 0);
    begin
        if (i_reset = '1') then
            intX <= (others => '0');
            intY <= (others => '0');
            cordic_valid_delayed <= '0';
        elsif (rising_edge(i_clk)) then
            if (cordic_valid) then
                -- rotated_x and rotated_y are between (approx)
                -- -225.0 and 225.0, so we first convert to be between
                -- (for x) 95 and 545
                -- (for y) 15 and 465

                -- sign extend the integer part of rotated_x
                -- by two bits then add 320
                intXTmp := (rotated_x(31) &
                            rotated_x(31) &
                            rotated_x(31 downto 23)) +
                           to_signed(320, 11);
                -- then cast it back to a 10 bit unsigned
                intX <= unsigned(intXTmp(9 downto 0));

                -- sign extend the integer part of rotated_y
                -- by one bit, then add 240
                intYTmp := (rotated_y(31) &
                            rotated_y(31 downto 23)) +
                           to_signed(240, 10);
                -- then cast it back to a 9 bit unsigned
                intY <= unsigned(intYTmp(8 downto 0));

            else
                intX <= (others => '0');
                intY <= (others => '0');
            end if;
            cordic_valid_delayed <= cordic_valid;
        end if;
    end process;

    process (i_clk, i_reset)
        variable pixelIdx:  unsigned(18 downto 0);
    begin
        if (i_reset = '1') then
            o_setPixelAddr <= (others => '0');
            o_setPixelBitMask <= (others => '0');
            o_setPixel <= '0';
        elsif (rising_edge(i_clk)) then
            pixelIdx := intY * to_unsigned(640, 10);
            pixelIdx := pixelIdx + intX;

            -- the pixel address is the top 16 bits of that
            o_setPixelAddr <= pixelIdx(18 downto 3);

            -- then the bit mask is the decoded lower 3 bits
            o_setPixelBitMask <= (others => '0');
            o_setPixelBitMask(to_integer(pixelIdx(2 downto 0))) <= '1';
            o_setPixel <= cordic_valid_delayed;
        end if;
    end process;

end architecture synth;
