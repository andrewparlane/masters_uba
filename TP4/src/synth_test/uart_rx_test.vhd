library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library altera_mf;
use altera_mf.all;

entity uart_rx_test is
    port (CLOCK_50:     in      std_ulogic;
          KEY:          in      std_ulogic_vector(0 downto 0);
          GPIO_0:       in      std_ulogic_vector(0 downto 0);
          LEDR:         out     std_ulogic_vector(7 downto 0));
end entity uart_rx_test;

architecture synth of uart_rx_test is

    component pll
        port (areset:   in  std_logic;
              inclk0:   in  std_logic;
              c0:       out std_logic;
              c1:       out std_logic;
              locked:   out std_logic);
    end component;

    component uart_rx is
        generic (CLOCK_PERIOD_NS:   natural;
                 BIT_TIME_NS:       natural);
        port ( -- Clock/reset
              i_clk:            in  std_ulogic;
              i_reset:          in  std_ulogic;

              -- Bus ports
              i_rx:             in  std_ulogic;

              -- Data ports
              o_readData:       out std_ulogic_vector(7 downto 0);
              o_readDataValid:  out std_ulogic;
              o_readDataError:  out std_ulogic;

              -- Status ports
              o_receiving:      out std_ulogic;
              o_isBreak:        out std_ulogic);
    end component uart_rx;

    signal clk100M:         std_ulogic;
    signal pll_locked:      std_ulogic;

    signal uart_rdata:          std_ulogic_vector(7 downto 0);
    signal uart_rdata_valid:    std_ulogic;

    signal reset:           std_ulogic;

begin

    -- in reset if either the reset button is pressed
    -- or the PLL is not locked
    reset <= not (KEY(0) and pll_locked);

    process (clk100M, reset)
    begin
        if (reset = '1') then
            LEDR <= (others => '0');
        elsif (rising_edge(clk100M)) then
            if (uart_rdata_valid = '1') then
                LEDR <= uart_rdata;
            end if;
        end if;
    end process;

    ----------------------------------------------------------------
    -- PLLs
    -----------------------------------------------------------------
    pll_inst: pll port map (areset  => '0',
                            inclk0  => CLOCK_50,
                            c0      => clk100M,
                            c1      => open,
                            locked  => pll_locked);

    -----------------------------------------------------------------
    -- UART Rx
    -----------------------------------------------------------------
    -- The UART_RX pin is put through a syncronizer in
    -- the uart_rx component
    -----------------------------------------------------------------
    uart: uart_rx
        generic map (CLOCK_PERIOD_NS => 10, -- 100MHz
                     BIT_TIME_NS => 8680)   -- Baud rate 115200
        port map (i_clk             => clk100M,
                  i_reset           => reset,
                  i_rx              => GPIO_0(0),
                  o_readData        => uart_rdata,
                  o_readDataValid   => uart_rdata_valid,
                  o_readDataError   => open,
                  o_receiving       => open,
                  o_isBreak         => open);

end architecture synth;
