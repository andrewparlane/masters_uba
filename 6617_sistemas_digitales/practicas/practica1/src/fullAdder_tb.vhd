-- preuba por fullAdder1

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity fullAdder_tb is
end entity fullAdder_tb;

architecture synth of fullAdder_tb is
    component fullAdder
        port (a, b: in  std_ulogic;
              cIn:  in  std_ulogic;
              o:    out std_ulogic;
              cOut: out std_ulogic);
    end component fullAdder;

    signal inputs: std_ulogic_vector (2 downto 0);
    signal output: std_ulogic_vector(1 downto 0);
begin

    dut:    fullAdder port map (a => inputs(2),
                                b => inputs(1),
                                cIn => inputs(0),
                                o => output(0),
                                cOut => output(1));

    process is
        variable expectedOutput: std_ulogic_vector(1 downto 0);
        variable errores: integer := 0;
    begin
        -- por todo los inputs posibles
        startloop: for i in 0 to ((2**inputs'length) - 1) loop
            inputs <= std_ulogic_vector(to_unsigned(i,inputs'length));
            wait for 100 ns;
            expectedOutput := std_ulogic_vector(unsigned('0' & inputs(2 downto 2)) +
                                               unsigned('0' & inputs(1 downto 1)) +
                                               unsigned('0' & inputs(0 downto 0)));

            report  std_ulogic'image(inputs(2)) & " + " &
                    std_ulogic'image(inputs(1)) & " + " &
                    std_ulogic'image(inputs(0)) & " = " &
                    integer'image(to_integer(unsigned(output)));

            assert (expectedOutput = output)
                report  "FALLA! esperado " & integer'image(to_integer(unsigned(expectedOutput)))
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
