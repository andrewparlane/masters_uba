-- preuba por rippleAdderN
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity rippleAdderN_tb is
end entity rippleAdderN_tb;

architecture synth of rippleAdderN_tb is
    component rippleAdderN
        generic(WIDTH: integer := 8);
        port(A, B:  in  STD_LOGIC_VECTOR((WIDTH - 1) downto 0);
             Cin:   in  STD_LOGIC;
             O:     out STD_LOGIC_VECTOR((WIDTH - 1) downto 0);
             Cout:  out STD_LOGIC);
    end component rippleAdderN;

    constant WIDTH: integer     := 4;

    -- 2 inputs de WIDTH bits cada uno, más 1 bit de Cin
    -- así necesitamos (2 * WIDTH) + 1 bits
    signal inputs: std_logic_vector ((2 * WIDTH) downto 0);
    -- 1 output de WIDTH bits más 1 bit de Cout
    signal output: std_logic_vector(WIDTH downto 0);
begin

    dut:    rippleAdderN   generic map (WIDTH => WIDTH)
                           port map (a => inputs((2 * WIDTH) downto (WIDTH + 1)),
                                     b => inputs(WIDTH downto 1),
                                     cIn => inputs(0),
                                     o => output((WIDTH - 1) downto 0),
                                     cOut => output(WIDTH));

    process is
        variable expectedOutput: std_logic_vector(WIDTH downto 0);
        variable errores: integer := 0;
    begin
        -- por todo los inputs posibles
        startloop: for i in 0 to ((2 ** inputs'length) - 1) loop
            inputs <= std_logic_vector(to_unsigned(i, inputs'length));
            wait for 100 ns;

            expectedOutput := std_logic_vector(unsigned('0' & inputs((2 * WIDTH) downto (WIDTH + 1))) +
                                               unsigned('0' & inputs(WIDTH downto 1)) +
                                               unsigned('0' & inputs(0 downto 0)));

            report  integer'image(to_integer(unsigned(inputs((2 * WIDTH) downto (WIDTH + 1))))) & " + " &
                    integer'image(to_integer(unsigned(inputs(WIDTH downto 1))))                 & " + " &
                    std_logic'image(inputs(0))                                                  & " = " &
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
