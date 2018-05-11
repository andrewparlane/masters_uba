library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use ieee.math_real.all;

entity contaCerosN_tb is
end entity contaCerosN_tb;

architecture synth of contaCerosN_tb is
    component contaCerosN
        generic (WIDTH: integer := 8);
        port (a: in  std_ulogic_vector((WIDTH - 1) downto 0);
              o: out unsigned(integer(ceil(log2(real(WIDTH)))) downto 0));
    end component contaCerosN;

    constant WIDTH: integer     := 8;
    constant OUT_WIDTH: integer := integer(ceil(log2(real(WIDTH)))) + 1;

    signal input: std_ulogic_vector ((WIDTH - 1) downto 0);
    signal output: unsigned((OUT_WIDTH - 1) downto 0);

begin

    dut:    contaCerosN     generic map (WIDTH => WIDTH)
                            port map   (a => input,
                                        o => output);

    process is
        variable errores: integer := 0;
        variable expectedOutput: unsigned((OUT_WIDTH - 1) downto 0);
    begin
        -- por todo los inputs posibles
        startloop: for i in 0 to ((2 ** input'length) - 1) loop
            input <= std_ulogic_vector(to_unsigned(i, input'length));
            wait for 100 ns;

            -- ceil(log2(i+1)) es igual al numero de bits que
            -- necesitamos para almacer i.
            -- i = 0 => ceil(log2(1)) = 0
            -- i = 6 => ceil(log2(7)) = 3
            -- i = 7 => ceil(log2(8)) = 3
            -- i = 8 => ceil(log2(9)) = 4
            expectedOutput := to_unsigned(WIDTH - integer(ceil(log2(real(i+1)))), OUT_WIDTH);

            report  integer'image(i) & " => " &
                    integer'image(to_integer(output));

            assert (expectedOutput = output)
                report  "falla esperado " & integer'image(to_integer(expectedOutput))
                severity error;

            if (expectedOutput /= output) then
                errores := errores + 1;
            end if;

        end loop startloop;

        if (errores /= 0) then
            report "FALLA! con " & integer'image(errores) & " errores";
        else
            report "APROBAR!";
        end if;

        std.env.stop;
    end process;

end architecture synth;