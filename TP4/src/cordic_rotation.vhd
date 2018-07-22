library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;

library common;
use common.type_pkg.all;

-- i_alpha is the angle to rotate in degrees.
-- 0.0 <= i_alpha < 360.0
entity cordic_rotation is
    generic (N: natural;
             M: natural;
             STEPS: natural);
    port (i_clk:    in  std_ulogic;
          i_reset:  in  std_ulogic;
          i_en:     in  std_ulogic;
          i_x:      in  signed((N + M - 1) downto 0);
          i_y:      in  signed((N + M - 1) downto 0);
          i_alpha:  in  unsigned((N + M - 1) downto 0);
          o_x:      out signed((N + M - 1) downto 0);
          o_y:      out signed((N + M - 1) downto 0);
          o_valid:  out std_ulogic);
end entity cordic_rotation;

architecture synth of cordic_rotation is
    -- function that returns the fixed point representation
    -- in Qn.m format for the arctan(2**-i) in degrees
    -- note: this should only be used for constants
    function get_param(i: natural) return signed is
        variable tmp: real;
        variable res: signed((N + M - 1) downto 0);
    begin
        -- get the arc tan of 2**-i
        tmp := ARCTAN(2.0**(-real(i)));
        -- convert to degrees
        tmp := (tmp * 180.0) / MATH_PI;
        -- convert it to fixed point
        tmp := floor((tmp * (2.0**M)) + 0.5);
        res := to_signed(integer(tmp), N + M);
        return res;
    end function get_param;

    -- helper function to get an array of all the needed
    -- parameters from 0 to STEPS - 1
    function get_all_params return signedArray is
        variable res: signedArray((STEPS - 1) downto 0)((N + M - 1) downto 0);
    begin
        for i in 0 to (STEPS - 1) loop
            res(i) := get_param(i);
        end loop;
        return res;
    end function get_all_params;

    constant PARAMS: signedArray((STEPS - 1) downto 0)((N + M - 1) downto 0)
                     := get_all_params;

    constant FIXED_90:  unsigned((N + M - 1) downto 0)
                        := to_unsigned(90, N) &
                           to_unsigned(0, M);
    constant FIXED_180: unsigned((N + M - 1) downto 0)
                        := to_unsigned(180, N) &
                           to_unsigned(0, M);
    constant FIXED_270: unsigned((N + M - 1) downto 0)
                        := to_unsigned(270, N) &
                           to_unsigned(0, M);
    constant FIXED_360: unsigned((N + M - 1) downto 0)
                        := to_unsigned(360, N) &
                           to_unsigned(0, M);

    -- each stage of the pipeline uses and produces x,y,z
    -- plus we pass through a valid signal
    signal x: signedArray(STEPS downto 0)((N + M - 1) downto 0);
    signal y: signedArray(STEPS downto 0)((N + M - 1) downto 0);
    signal z: signedArray(STEPS downto 0)((N + M - 1) downto 0);
    signal valid: std_ulogic_vector(STEPS downto 0);
begin
    -- convert the inputs so that the angle is: -90.0 <= z < 90.0
    process (all)
    begin
        if (i_alpha >= FIXED_270) then
            -- minus 360 from the angle
            -- means we don't change the co-ordinates
            -- just rotate the other direction
            x(0) <= i_x;
            y(0) <= i_y;
            z(0) <= signed(i_alpha - FIXED_360);
        elsif (i_alpha >= FIXED_90) then
            -- minus 180 from the angle
            -- and invert the co-ordinates
            x(0) <= -i_x;
            y(0) <= -i_y;
            z(0) <= signed(i_alpha - FIXED_180);
        else
            x(0) <= i_x;
            y(0) <= i_y;
            z(0) <= signed(i_alpha);
        end if;
    end process;

    valid(0) <= i_en;

    pipelineSteps:
    for step in 0 to (STEPS - 1) generate
    begin

        process (i_clk, i_reset)
            variable tmpX: signed((N + M - 1) downto 0);
            variable tmpY: signed((N + M - 1) downto 0);
            variable tmpP: signed((N + M - 1) downto 0);
            variable comp2: std_ulogic;
        begin
            if (i_reset = '1') then
                x(step+1) <= to_signed(0, N+M);
                y(step+1) <= to_signed(0, N+M);
                z(step+1) <= to_signed(0, N+M);
                valid(step+1) <= '0';
            elsif (rising_edge(i_clk)) then
                valid(step+1) <= valid(step);

                -- we need to take the twos complement of
                -- the previous x and y if the z(step) < 0
                -- so just take the sign bit.
                comp2 := z(step)(N + M - 1);

                -- then if the sign bit was 1
                -- get the twos complement of x and y
                -- and the parameter
                if (comp2 = '1') then
                    tmpX := -x(step);
                    tmpY := -y(step);
                    tmpP := -PARAMS(step);
                else
                    tmpX := x(step);
                    tmpY := y(step);
                    tmpP := PARAMS(step);
                end if;

                -- now get the next x, y and z
                x(step+1) <= x(step) - (SHIFT_RIGHT(tmpY, step));
                y(step+1) <= y(step) + (SHIFT_RIGHT(tmpX, step));
                z(step+1) <= z(step) - tmpP;
            end if;
        end process;

    end generate;

    -- outputs
    o_x <= x(STEPS);
    o_y <= y(STEPS);
    o_valid <= valid(STEPS);

end architecture synth;
