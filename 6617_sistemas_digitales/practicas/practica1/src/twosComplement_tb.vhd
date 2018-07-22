library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity twosComplement_tb is
end entity twosComplement_tb;

architecture synth of twosComplement_tb is
    component twosComplement
        generic (WIDTH: integer := 8);
        port (a: in  std_ulogic_vector((WIDTH - 1) downto 0);
              o: out std_ulogic_vector((WIDTH - 1) downto 0));
    end component twosComplement;

    constant WIDTH: integer     := 4;

    signal input: std_ulogic_vector ((WIDTH - 1) downto 0);
    signal output: std_ulogic_vector((WIDTH - 1) downto 0);

begin

    dut:    twosComplement  generic map (WIDTH => WIDTH)
                            port map   (a => input,
                                        o => output);

    process is
        variable expectedOutput: std_ulogic_vector((WIDTH - 1) downto 0);
        variable errores: integer := 0;
    begin
        -- por todo los inputs posibles
        startloop: for i in 0 to ((2 ** input'length) - 1) loop
            input <= std_ulogic_vector(to_unsigned(i, input'length));
            wait for 100 ns;

            expectedOutput := std_ulogic_vector(-signed(input));

            report  integer'image(to_integer(signed(input))) & " => " &
                    integer'image(to_integer(signed(output)));

            assert (expectedOutput = output)
                report  "falla esperado " & integer'image(to_integer(signed(expectedOutput)))
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