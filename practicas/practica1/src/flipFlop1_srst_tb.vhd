-- preuba parar flipFlop1_srst
library ieee;
use ieee.std_logic_1164.all;

entity flipFlop1_srst_tb is
end entity flipFlop1_srst_tb;

architecture synth of flipFlop1_srst_tb is
    component flipFlop1_srst
        port (clk:  in  std_ulogic;
              d:    in  std_ulogic;
              en:   in  std_ulogic;
              srst: in  std_ulogic;
              q:    out std_ulogic);
    end component flipFlop1_srst;

    signal clk: std_ulogic := '0';
    signal d, en, srst, q: std_ulogic;
    signal expectedQ: std_ulogic;
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
                    report "q = " & std_ulogic'image(q) &
                       " esperado " & std_ulogic'image(expectedQ)
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