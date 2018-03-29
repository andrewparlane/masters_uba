library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity tp1_tb is
end entity tp1_tb;

architecture synth of tp1_tb is

    component tp1 is
        generic (CLOCK_DIVIDER:  natural);
        port (CLOCK_50: in  std_logic;
              KEY:      in  std_logic_vector(1 downto 0);
              HEX0:     out std_logic_vector(6 downto 0);
              HEX1:     out std_logic_vector(6 downto 0);
              HEX2:     out std_logic_vector(6 downto 0);
              HEX3:     out std_logic_vector(6 downto 0));
    end component tp1;

    signal clk:         std_logic   := '0';
    signal rst_key:     std_logic   := '1';     -- keys son activa baja
    signal fast_key:    std_logic   := '1';
    signal key:         std_logic_vector(1 downto 0);

begin

    dut:    tp1 generic map    (CLOCK_DIVIDER => 10000)   -- incrementar el primer dígito cada 5000 ticks
                port map       (CLOCK_50 => clk,
                                KEY => key);

    -- clk = 50MHz => periodo = 20ns
    clk <= not clk after 10 ns;

    -- key
    key <= fast_key & rst_key;

    process
    begin
        -- recuerdes que los keys son activa baja
        rst_key <= '0';
        wait for 100 ns;
        rst_key <= '1';
        wait for 1100 ms;
        rst_key <= '0';
        wait for 500 ns;
        rst_key <= '1';
        fast_key <= '0';
        wait for 1100 us;

        std.env.stop;
    end process;

end architecture synth;
