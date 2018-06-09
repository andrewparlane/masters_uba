library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.type_pkg.all;

entity fp_decode_tb is
end entity fp_decode_tb;

architecture sim of fp_decode_tb is
    package floatHelperPkg
            is new work.fp_helper_pkg
            generic map (TBITS => 32,
                         EBITS => 8);

    constant num:   unsignedArray(0 to 9)(31 downto 0)
                    := ("00111110001001010101101000011001",     -- +1.29181206226348876953125 * 2^-3
                        "10111100101110111000010110110010",     -- -1.4650175571441650390625 * 2^-6
                        "00000000000000000000000000000000",     -- +0
                        "10000000000000000000000000000000",     -- -0
                        "01111111100000000000000000000000",     -- +inf
                        "11111111100000000000000000000000",     -- -inf
                        "01111111100000000000000000000001",     -- NaN
                        "11111111100000000000000000000001",     -- NaN
                        "00000000001001010101101000011001",     -- +0.29181206226348876953125 * 2^-126
                        "10000000001110111000010110110010");    -- -0.4650175571441650390625 * 2^-126

    signal idx:     natural := 0;
    signal fp:      floatHelperPkg.fpUnpacked;
begin

    fp      <= floatHelperPkg.unpack(std_ulogic_vector(num(idx)));

    process
    begin
        for i in num'range loop
            idx <= i;
            wait for 100 ns;
            report floatHelperPkg.to_string(fp);
        end loop;
        std.env.stop;
    end process;

end architecture sim;
