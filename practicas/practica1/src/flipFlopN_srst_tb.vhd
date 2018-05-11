-- preuba parar flipFlopN_srst
library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity flipFlopN_srst_tb is
end entity flipFlopN_srst_tb;

architecture synth of flipFlopN_srst_tb is
    component flipFlopN_srst
        generic (WIDTH: integer);
        port (clk:  in  std_ulogic;
              d:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              en:   in  std_ulogic;
              srst: in  std_ulogic;
              q:    out std_ulogic_vector((WIDTH - 1) downto 0));
    end component flipFlopN_srst;

    constant WIDTH: integer := 4;

    signal clk: std_ulogic := '0';
    signal en, srst: std_ulogic;
    signal d, q, expectedQ: std_ulogic_vector((WIDTH - 1) downto 0);
begin

    -- clk period = 100ns
    clk <= not clk after 50 ns;

    dut:    flipFlopN_srst  generic map (WIDTH => WIDTH)
                            port map (clk => clk,
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
                    report "q = " & integer'image(to_integer(unsigned(q))) &
                       " esperado " & integer'image(to_integer(unsigned(expectedQ)))
                    severity error;

            wait for 100 ns;
        end loop;
    end process;

    -- codigo de preuba
    process
    begin
        srst <= '1';
        en <= '1';
        d <= "1111";
        expectedQ <= "0000";
        wait for 500 ns;

        srst <= '0';
        expectedQ <= d;
        wait for 500 ns;

        en <= '0';
        wait for 500 ns;

        d <= "0000";
        wait for 500 ns;

        en <= '1';
        expectedQ <= d;
        wait for 500 ns;

        en <= '0';
        wait for 500 ns;

        d <= "0101";
        wait for 500 ns;

        en <= '1';
        expectedQ <= d;
        wait for 500 ns;

        srst <= '1';
        expectedQ <= "0000";
        wait for 500 ns;

        srst <= '0';
        expectedQ <= d;
        wait for 500 ns;

        std.env.stop;
    end process;

end architecture synth;