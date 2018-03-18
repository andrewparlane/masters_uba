-- preuba por fullAdder1

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity fullAdder1_tb is
end entity fullAdder1_tb;

architecture synth of fullAdder1_tb is
    component fullAdder1
        port (A, B: in  std_logic;
              Cin:  in  std_logic;
              O:    out std_logic;
              Cout: out std_logic);
    end component fullAdder1;

    signal inputs: std_logic_vector (2 downto 0);
    signal output: std_logic_vector(1 downto 0);
begin

    dut:    fullAdder1 port map (A => inputs(2),
                                 B => inputs(1),
                                 Cin => inputs(0),
                                 O => output(0),
                                 Cout => output(1));

    process is
        variable expectedOutput: std_logic_vector(1 downto 0);
    begin
        -- por todo los inputs posibles
        startloop: for i in 0 to 7 loop
            inputs <= std_logic_vector(to_unsigned(i,3));
            wait for 100 ns;
            expectedOutput := std_logic_vector(unsigned('0' & inputs(2 downto 2)) +
                                               unsigned('0' & inputs(1 downto 1)) +
                                               unsigned('0' & inputs(0 downto 0)));

            assert (expectedOutput = output)
                report  "falla con " &
                        "inputs: " & std_logic'image(inputs(2)) &
                              ", " & std_logic'image(inputs(1)) &
                              ", " & std_logic'image(inputs(0)) &
                        " expectedOutput: " & integer'image(to_integer(unsigned(expectedOutput))) &
                        " actualOutput: "   & integer'image(to_integer(unsigned(output)))
                severity error;
        end loop startloop;
        std.env.stop;
    end process;

end architecture synth;
