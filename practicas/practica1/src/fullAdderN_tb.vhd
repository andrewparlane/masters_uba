-- preuba por fullAdderN
-- tiempo de ejecutación es 512 * 100ns = 51200

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity fullAdderN_tb is
end entity fullAdderN_tb;

architecture synth of fullAdderN_tb is
    component fullAdderN
        generic(WIDTH: integer := 8);
        port(A, B:  in  STD_LOGIC_VECTOR((WIDTH - 1) downto 0);
             Cin:   in  STD_LOGIC;
             O:     out STD_LOGIC_VECTOR((WIDTH - 1) downto 0);
             Cout:  out STD_LOGIC);
    end component fullAdderN;

    constant WIDTH: integer     := 4;

    -- 2 inputs de WIDTH bits cada uno, más 1 bit de Cin
    -- así necesitamos (2 * WIDTH) + 1 bits
    signal inputs: std_logic_vector ((2 * WIDTH) downto 0);
    -- 1 output de WIDTH bits más 1 bit de Cout
    signal output: std_logic_vector(WIDTH downto 0);
begin

    dut:    fullAdderN  generic map (WIDTH => WIDTH)
                           port map (A => inputs((2 * WIDTH) downto (WIDTH + 1)),
                                     B => inputs(WIDTH downto 1),
                                     Cin => inputs(0),
                                     O => output((WIDTH - 1) downto 0),
                                     Cout => output(WIDTH));

    process is
        variable expectedOutput: std_logic_vector(WIDTH downto 0);
    begin
        -- por todo los inputs posibles
        startloop: for i in 0 to ((2 ** inputs'length) - 1) loop
            inputs <= std_logic_vector(to_unsigned(i, inputs'length));
            wait for 100 ns;

            expectedOutput := std_logic_vector(unsigned('0' & inputs((2 * WIDTH) downto (WIDTH + 1))) +
                                               unsigned('0' & inputs(WIDTH downto 1)) +
                                               unsigned('0' & inputs(0 downto 0)));

            assert (expectedOutput = output)
                report  "falla con " &
                        "inputs: " & integer'image(to_integer(unsigned(inputs((2 * WIDTH) downto (WIDTH + 1))))) &
                              ", " & integer'image(to_integer(unsigned(inputs(WIDTH downto 1)))) &
                              ", " & std_logic'image(inputs(0)) &
                        " expectedOutput: " & integer'image(to_integer(unsigned(expectedOutput))) &
                        " actualOutput: "   & integer'image(to_integer(unsigned(output)))
                severity error;
        end loop startloop;
        std.env.stop;
    end process;

end architecture synth;
