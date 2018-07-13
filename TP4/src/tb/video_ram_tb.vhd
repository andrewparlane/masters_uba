library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;

entity video_ram_tb is
end entity video_ram_tb;

architecture sim of video_ram_tb is
    component video_ram
        port (address_a:    in std_logic_vector (18 downto 0);
              address_b:    in std_logic_vector (15 downto 0);
              clock_a:      in std_logic;
              clock_b:      in std_logic;
              data_a:       in std_logic_vector (0 downto 0);
              data_b:       in std_logic_vector (7 downto 0);
              wren_a:       in std_logic;
              wren_b:       in std_logic;
              q_a:          out std_logic_vector (0 downto 0);
              q_b:          out std_logic_vector (7 downto 0));
    end component video_ram;

    component delay is
        generic (DELAY: natural;
                 WIDTH: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              output:   out std_ulogic_vector((WIDTH - 1) downto 0));
    end component delay;

    signal addr:                    unsigned(15 downto 0);
    signal initAddr:                unsigned(15 downto 0);
    signal incRdAddr:               unsigned(15 downto 0);
    signal incRdAddrDelayed:        unsigned(15 downto 0);
    signal incRdAddrValid:          std_ulogic;
    signal incRdAddrValidDelayed:   std_ulogic;

    signal wdata:               unsigned(7 downto 0);
    signal wen:                 std_ulogic;
    signal rdata:               unsigned(7 downto 0);

    signal init:                std_ulogic;
    signal count:               unsigned(1 downto 0);
    signal inc_loops:           natural;

    signal clk:                 std_ulogic := '0';
    signal reset:               std_ulogic := '1';

    -- 50 MHz
    constant CLK_HZ:        natural := 50 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;
begin

    clk <= not clk after (CLK_PERIOD/2);

    addrDelay: delay
        generic map (DELAY => 2,
                     WIDTH => 16)
        port map (clk => clk,
                  rst => reset,
                  input => std_ulogic_vector(incRdAddr),
                  unsigned(output) => incRdAddrDelayed);

    validDelay: delay
        generic map (DELAY => 2,
                     WIDTH => 1)
        port map (clk => clk,
                  rst => reset,
                  input(0) => incRdAddrValid,
                  output(0) => incRdAddrValidDelayed);

    process (all)
    begin
        if (init = '1') then
            addr <= initAddr;
            wdata <= initAddr(5 downto 0) & "00";
            wen <= '1';
        elsif (incRdAddrValid = '1') then
            addr <= incRdAddr;
            wdata <= (others => 'U');
            wen <= '0';
        else
            addr <= incRdAddrDelayed;
            wdata <= rdata + to_unsigned(1, 8);
            wen <= incRdAddrValidDelayed;
        end if;
    end process;

    dut: video_ram
    port map (address_a     => (others => '0'),
              address_b     => std_logic_vector(addr),
              clock_a       => '0',
              clock_b       => clk,
              data_a        => (others => '0'),
              data_b        => std_logic_vector(wdata),
              wren_a        => '0',
              wren_b        => wen,
              q_a           => open,
              unsigned(q_b) => rdata);

    -- Generate incAddr
    process (clk, reset)
    begin
        if (reset = '1') then
            incRdAddr <= to_unsigned(0, 16);
            incRdAddrValid <= '0';
            count <= to_unsigned(0, 2);
            inc_loops <= 0;
        elsif (rising_edge(clk)) then
            if (count = to_unsigned(2, 2)) then
                count <= to_unsigned(0, 2);
                incRdAddrValid <= '1';
                if (incRdAddr = to_unsigned(2, 16)) then
                    incRdAddr <= to_unsigned(0, 16);
                    inc_loops <= inc_loops + 1;
                else
                    incRdAddr <= incRdAddr + to_unsigned(1, 16);
                end if;
            else
                incRdAddrValid <= '0';
                if (init = '0') then
                    count <= count + to_unsigned(1, 2);
                end if;
            end if;
        end if;
    end process;

    -- Generate initAddr then swap to inc mode
    process (clk, reset)
    begin
        if (reset = '1') then
            init <= '1';
            initAddr <= to_unsigned(0, 16);
        elsif (rising_edge(clk)) then
            if (init = '1') then
                if (initAddr = to_unsigned(2, 16)) then
                    -- done
                    init <= '0';
                else
                    initAddr <= initAddr + to_unsigned(1, 16);
                end if;
            end if;
        end if;
    end process;

    -- generate reset signal
    process
    begin
        -- reset the logic
        reset <= '1';
        wait for (CLK_PERIOD*5);
        wait until rising_edge(clk);
        reset <= '0';
        wait until (inc_loops = 5);

        std.env.stop;
    end process;

end architecture sim;
