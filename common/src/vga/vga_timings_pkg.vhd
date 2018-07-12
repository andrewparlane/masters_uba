library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package vga_timings_helper_pkg is
    function getLineTime(clkPeriodo:        time;
                         H_ACTIVE:          natural;
                         H_FRONT_PORCH:     natural;
                         H_SYNC:            natural;
                         H_BACK_PORCH:      natural) return time;

    function getFrameTime(clkPeriodo:       time;
                          H_ACTIVE:          natural;
                          H_FRONT_PORCH:     natural;
                          H_SYNC:            natural;
                          H_BACK_PORCH:      natural;
                          V_ACTIVE:         natural;
                          V_FRONT_PORCH:    natural;
                          V_SYNC:           natural;
                          V_BACK_PORCH:     natural) return time;
end package vga_timings_helper_pkg;

package body vga_timings_helper_pkg is
    function getLineTime(clkPeriodo:        time;
                         H_ACTIVE:          natural;
                         H_FRONT_PORCH:     natural;
                         H_SYNC:            natural;
                         H_BACK_PORCH:      natural) return time is
    begin
        return clkPeriodo * (H_ACTIVE +
                             H_FRONT_PORCH +
                             H_SYNC +
                             H_BACK_PORCH);
    end function getLineTime;

    function getFrameTime(clkPeriodo:       time;
                          H_ACTIVE:         natural;
                          H_FRONT_PORCH:    natural;
                          H_SYNC:           natural;
                          H_BACK_PORCH:     natural;
                          V_ACTIVE:         natural;
                          V_FRONT_PORCH:    natural;
                          V_SYNC:           natural;
                          V_BACK_PORCH:     natural) return time is
        constant lineTime: time
            := getLineTime(clkPeriodo      => clkPeriodo,
                           H_ACTIVE        => H_ACTIVE,
                           H_FRONT_PORCH   => H_FRONT_PORCH,
                           H_SYNC          => H_SYNC,
                           H_BACK_PORCH    => H_BACK_PORCH);
    begin
        return lineTime * (V_ACTIVE +
                           V_FRONT_PORCH +
                           V_SYNC +
                           V_BACK_PORCH);
    end function getFrameTime;
end package body vga_timings_helper_pkg;


library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.all;

package vga_timings_800_600_pkg is
    constant H_ACTIVE:      natural := 800; -- ticks
    constant H_FRONT_PORCH: natural := 15;  -- ticks
    constant H_SYNC:        natural := 80;  -- ticks
    constant H_BACK_PORCH:  natural := 160; -- ticks

    constant V_ACTIVE:      natural := 600; -- líneas
    constant V_FRONT_PORCH: natural := 1;   -- líneas
    constant V_SYNC:        natural := 3;   -- líneas
    constant V_BACK_PORCH:  natural := 21;  -- líneas

    constant PIXEL_X_WIDTH: natural := utils_pkg.min_width(H_ACTIVE);
    constant PIXEL_Y_WIDTH: natural := utils_pkg.min_width(V_ACTIVE);

    function getLineTime(clkPeriodo:  time) return time;
    function getFrameTime(clkPeriodo: time) return time;
end package vga_timings_800_600_pkg;

package body vga_timings_800_600_pkg is
    function getLineTime(clkPeriodo: time) return time is
    begin
        return vga_timings_helper_pkg.getLineTime(clkPeriodo,
                                             H_ACTIVE,
                                             H_FRONT_PORCH,
                                             H_SYNC,
                                             H_BACK_PORCH);
    end function getLineTime;

    function getFrameTime(clkPeriodo: time) return time is
    begin
        return vga_timings_helper_pkg.getFrameTime(clkPeriodo,
                                              H_ACTIVE,
                                              H_FRONT_PORCH,
                                              H_SYNC,
                                              H_BACK_PORCH,
                                              V_ACTIVE,
                                              V_FRONT_PORCH,
                                              V_SYNC,
                                              V_BACK_PORCH);
    end function getFrameTime;
end package body vga_timings_800_600_pkg;

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.all;

package vga_timings_640_480_pkg is
    constant H_ACTIVE:      natural := 640; -- ticks
    constant H_FRONT_PORCH: natural := 16;  -- ticks
    constant H_SYNC:        natural := 96;  -- ticks
    constant H_BACK_PORCH:  natural := 48;  -- ticks

    constant V_ACTIVE:      natural := 480; -- líneas
    constant V_FRONT_PORCH: natural := 10;  -- líneas
    constant V_SYNC:        natural := 2;   -- líneas
    constant V_BACK_PORCH:  natural := 33;  -- líneas

    constant PIXEL_X_WIDTH: natural := utils_pkg.min_width(H_ACTIVE);
    constant PIXEL_Y_WIDTH: natural := utils_pkg.min_width(V_ACTIVE);

    function getLineTime(clkPeriodo:  time) return time;
    function getFrameTime(clkPeriodo: time) return time;
end package vga_timings_640_480_pkg;

package body vga_timings_640_480_pkg is
    function getLineTime(clkPeriodo: time) return time is
    begin
        return vga_timings_helper_pkg.getLineTime(clkPeriodo,
                                             H_ACTIVE,
                                             H_FRONT_PORCH,
                                             H_SYNC,
                                             H_BACK_PORCH);
    end function getLineTime;

    function getFrameTime(clkPeriodo: time) return time is
    begin
        return vga_timings_helper_pkg.getFrameTime(clkPeriodo,
                                              H_ACTIVE,
                                              H_FRONT_PORCH,
                                              H_SYNC,
                                              H_BACK_PORCH,
                                              V_ACTIVE,
                                              V_FRONT_PORCH,
                                              V_SYNC,
                                              V_BACK_PORCH);
    end function getFrameTime;
end package body vga_timings_640_480_pkg;

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.all;

package vga_timings_10_10_pkg is
    constant H_ACTIVE:      natural := 10; -- ticks
    constant H_FRONT_PORCH: natural := 4;  -- ticks
    constant H_SYNC:        natural := 5;  -- ticks
    constant H_BACK_PORCH:  natural := 6; -- ticks

    constant V_ACTIVE:      natural := 10; -- líneas
    constant V_FRONT_PORCH: natural := 1;   -- líneas
    constant V_SYNC:        natural := 2;   -- líneas
    constant V_BACK_PORCH:  natural := 3;  -- líneas

    constant PIXEL_X_WIDTH: natural := utils_pkg.min_width(H_ACTIVE);
    constant PIXEL_Y_WIDTH: natural := utils_pkg.min_width(V_ACTIVE);

    function getLineTime(clkPeriodo:  time) return time;
    function getFrameTime(clkPeriodo: time) return time;
end package vga_timings_10_10_pkg;

package body vga_timings_10_10_pkg is
    function getLineTime(clkPeriodo: time) return time is
    begin
        return vga_timings_helper_pkg.getLineTime(clkPeriodo,
                                             H_ACTIVE,
                                             H_FRONT_PORCH,
                                             H_SYNC,
                                             H_BACK_PORCH);
    end function getLineTime;

    function getFrameTime(clkPeriodo: time) return time is
    begin
        return vga_timings_helper_pkg.getFrameTime(clkPeriodo,
                                              H_ACTIVE,
                                              H_FRONT_PORCH,
                                              H_SYNC,
                                              H_BACK_PORCH,
                                              V_ACTIVE,
                                              V_FRONT_PORCH,
                                              V_SYNC,
                                              V_BACK_PORCH);
    end function getFrameTime;
end package body vga_timings_10_10_pkg;
