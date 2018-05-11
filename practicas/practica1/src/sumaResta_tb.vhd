-- preuba por sumaResta
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.suma_resta_package.all;

entity sumaResta_tb is
end entity sumaResta_tb;

architecture synth of sumaResta_tb is
    component sumaResta
        generic(WIDTH: integer);
        port(a, b:  in  std_ulogic_vector((WIDTH - 1) downto 0);
             op:    in  sumaRestaOp;
             o:     out std_ulogic_vector((WIDTH - 1) downto 0);
             cOut:  out std_ulogic);
    end component sumaResta;

    constant WIDTH: integer     := 4;

    -- 2 inputs de WIDTH bits cada uno
    -- así necesitamos (2 * WIDTH)
    signal inputs: std_ulogic_vector (((2 * WIDTH) - 1) downto 0);
    -- operación
    signal op: sumaRestaOp;

    -- 1 output de WIDTH bits más 1 bit de Cout
    signal output: std_ulogic_vector(WIDTH downto 0);
begin

    dut:    sumaResta   generic map (WIDTH => WIDTH)
                           port map (a => inputs(((2 * WIDTH) - 1) downto WIDTH),
                                     b => inputs((WIDTH - 1) downto 0),
                                     op => op,
                                     o => output((WIDTH - 1) downto 0),
                                     cOut => output(WIDTH));

    process is
        variable expectedOutput: std_ulogic_vector(WIDTH downto 0);
        variable errores: integer := 0;
    begin
        -- primero +
        -- por todo los inputs posibles
        sumaLoop: for i in 0 to ((2 ** inputs'length) - 1) loop
            inputs <= std_ulogic_vector(to_unsigned(i, inputs'length));
            op <= SUMA;
            wait for 100 ns;

            expectedOutput := std_ulogic_vector(resize(unsigned(inputs(((2 * WIDTH) - 1) downto WIDTH)), expectedOutput'length) +
                                               resize(unsigned(inputs((WIDTH - 1) downto 0)), expectedOutput'length));

            report  integer'image(to_integer(unsigned(inputs(((2 * WIDTH) - 1) downto WIDTH)))) & " + " &
                    integer'image(to_integer(unsigned(inputs((WIDTH - 1) downto 0))))           & " = " &
                    integer'image(to_integer(unsigned(output)));

            assert (expectedOutput = output)
                report  "FALLA! esperado " & integer'image(to_integer(unsigned(expectedOutput)))
                severity error;

            if (expectedOutput /= output) then
                errores := errores + 1;
            end if;

        end loop sumaLoop;

        -- ahora -
        -- por todo los inputs posibles
        restaLoop: for i in 0 to ((2 ** inputs'length) - 1) loop
            inputs <= std_ulogic_vector(to_unsigned(i, inputs'length));
            op <= RESTA;
            wait for 100 ns;

            expectedOutput := std_ulogic_vector(resize(unsigned('0' & inputs(((2 * WIDTH) - 1) downto WIDTH)), expectedOutput'length) -
                                               resize(unsigned('0' & inputs((WIDTH - 1) downto 0)), expectedOutput'length));

            report  integer'image(to_integer(unsigned(inputs(((2 * WIDTH) - 1) downto WIDTH)))) & " - " &
                    integer'image(to_integer(unsigned(inputs((WIDTH - 1) downto 0))))           & " = " &
                    integer'image(to_integer(unsigned(output)));

            assert (expectedOutput = output)
                report  "FALLA! esperado " & integer'image(to_integer(unsigned(expectedOutput)))
                severity error;

            if (expectedOutput /= output) then
                errores := errores + 1;
            end if;

        end loop restaLoop;

        if (errores /= 0) then
            report "FALLA! con " & integer'image(errores) & " errores";
        else
            report "APROBAR!";
        end if;

        std.env.stop;
    end process;

end architecture synth;
