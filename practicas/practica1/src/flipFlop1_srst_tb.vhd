-- preuba parar flipFlop1_srst
library ieee;
use ieee.std_logic_1164.all;

entity flipFlop1_srst_tb is
end entity flipFlop1_srst_tb;

architecture synth of flipFlop1_srst_tb is
    component flipFlop1_srst
        port (clk:  in  std_logic;
              d:    in  std_logic;
              en:   in  std_logic;
              srst: in  std_logic;
              q:    out std_logic);
    end component flipFlop1_srst;

    signal clk: std_logic := '0';
    signal d, en, srst, q: std_logic;
    signal expectedQ: std_logic;
begin

    -- clk period = 100ns
    clk <= not clk after 50 ns;

    dut:    flipFlop1_srst  port map (clk => clk,
                                      d => d,
                                      en => en,
                                      srst => srst,
                                      q => q);

    -- comprobación
    process
    begin
        wait for 51 ns;
        loop
            assert  (q = expectedQ)
                    report "q = " & std_logic'image(q) &
                       " esperado " & std_logic'image(expectedQ)
                    severity error;

            wait for 100 ns;
        end loop;
    end process;

    -- codigo de preuba
    process
    begin
        srst <= '1';
        en <= '1';
        d <= '1';
        expectedQ <= '0';
        wait for 500 ns;

        srst <= '0';
        expectedQ <= '1';
        wait for 500 ns;

        en <= '0';
        wait for 500 ns;

        d <= '0';
        wait for 500 ns;

        en <= '1';
        expectedQ <= '0';
        wait for 500 ns;

        en <= '0';
        wait for 500 ns;

        d <= '1';
        wait for 500 ns;

        en <= '1';
        expectedQ <= '1';
        wait for 500 ns;

        srst <= '1';
        expectedQ <= '0';
        wait for 500 ns;

        srst <= '0';
        expectedQ <= '1';
        wait for 500 ns;

        std.env.stop;
    end process;

end architecture synth;