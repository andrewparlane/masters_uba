library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;

library common;
use common.type_pkg.all;

entity cordic_rotation_3d is
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
end entity cordic_rotation_3d;

architecture synth of cordic_rotation_3d is
    component cordic_rotation is
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
    end component cordic_rotation;

    component delay is
        generic (DELAY: natural;
                 WIDTH: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              output:   out std_ulogic_vector((WIDTH - 1) downto 0));
    end component delay;

    function calculate_cordic_gain(steps: natural) return signed is
        variable tmp: real := 1.0;
        variable res: signed((N + M - 1) downto 0);
    begin
        for step in 0 to (STEPS - 1) loop
            tmp := tmp * SQRT(1.0 + 2.0**(2.0*(-real(step))));
        end loop;

        -- convert to fixed point
        tmp := floor((tmp * (2.0**M)) + 0.5);
        res := to_signed(integer(tmp), N + M);
        return res;
    end function calculate_cordic_gain;

    constant GAIN:  signed((N + M - 1) downto 0) := calculate_cordic_gain(STEPS);

    signal x:       signedArray(2 downto 0)((N + M - 1) downto 0);
    signal y:       signedArray(2 downto 0)((N + M - 1) downto 0);
    signal z:       signedArray(2 downto 0)((N + M - 1) downto 0);
    signal mult:    signedArray(2 downto 0)(((2 * (N + M)) - 1) downto 0);
    signal xyValid: std_ulogic;
    signal yzValid: std_ulogic;
    signal xzValid: std_ulogic;

begin

    -----------------------------------------------------------------
    -- first round. Rotate around axis Z
    -----------------------------------------------------------------
    -- we multiply z by the gain of a 10 pass cordic
    -- because both x and y have the same gain applied
    -- We also must delay the Z signal the correct number
    -- of ticks to keep it in sync with the output of the cordic
    -----------------------------------------------------------------
    cordicXY: cordic_rotation
              generic map (N => N,
                           M => M,
                           STEPS => STEPS)
              port map (i_clk => i_clk,
                        i_reset => i_reset,
                        i_en => i_en,
                        i_x => i_x,
                        i_y => i_y,
                        i_alpha => i_alpha,
                        o_x => x(0),
                        o_y => y(0),
                        o_valid => xyValid);

    mult(0) <= (i_z * GAIN);
    delayZ: delay
            generic map (DELAY => STEPS,
                         WIDTH => (N + M))
            port map (clk => i_clk,
                      rst => i_reset,
                      input => std_ulogic_vector(mult(0)((((2 * M) + N) - 1) downto M)),
                      signed(output) => z(0));

    -----------------------------------------------------------------
    -- Second round. Rotate around axis x
    -----------------------------------------------------------------
    -- we multiply x by the gain of a 10 pass cordic
    -- because both y and z have the same gain applied
    -- We also must delay the x signal the correct number
    -- of ticks to keep it in sync with the output of the cordic
    -----------------------------------------------------------------
    cordicYZ: cordic_rotation
              generic map (N => N,
                           M => M,
                           STEPS => STEPS)
              port map (i_clk => i_clk,
                        i_reset => i_reset,
                        i_en => xyValid,
                        i_x => y(0),
                        i_y => z(0),
                        i_alpha => i_beta,
                        o_x => y(1),
                        o_y => z(1),
                        o_valid => yzValid);

    mult(1) <= (x(0) * GAIN);
    delayX: delay
            generic map (DELAY => STEPS,
                         WIDTH => (N + M))
            port map (clk => i_clk,
                      rst => i_reset,
                      input => std_ulogic_vector(mult(1)((((2 * M) + N) - 1) downto M)),
                      signed(output) => x(1));

    -----------------------------------------------------------------
    -- final round. Rotate around axis Y
    -----------------------------------------------------------------
    -- we multiply y by the gain of a 10 pass cordic
    -- because both x and z have the same gain applied
    -- We also must delay the Y signal the correct number
    -- of ticks to keep it in sync with the output of the cordic
    -----------------------------------------------------------------
    cordicXZ: cordic_rotation
              generic map (N => N,
                           M => M,
                           STEPS => STEPS)
              port map (i_clk => i_clk,
                        i_reset => i_reset,
                        i_en => yzValid,
                        i_x => z(1),
                        i_y => x(1),
                        i_alpha => i_gamma,
                        o_x => z(2),
                        o_y => x(2),
                        o_valid => xzValid);

    mult(2) <= (y(1) * GAIN);
    delayY: delay
            generic map (DELAY => STEPS,
                         WIDTH => (N + M))
            port map (clk => i_clk,
                      rst => i_reset,
                      input => std_ulogic_vector(mult(2)((((2 * M) + N) - 1) downto M)),
                      signed(output) => y(2));

    -----------------------------------------------------------------
    -- Outputs
    -----------------------------------------------------------------
    o_x <= x(2);
    o_y <= y(2);
    o_z <= z(2);
    o_valid <= xzValid;

end architecture synth;
