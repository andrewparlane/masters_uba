library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library altera_mf;
use altera_mf.all;

entity uart_rx is
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
end entity uart_rx;

architecture synth of uart_rx is
    component altera_std_synchronizer_bundle is
        generic (depth: integer := 3;   -- must be >= 2
                 width: integer := 1);

        port (clk:      in  std_logic;
              reset_n:  in  std_logic;
              din:      in  std_logic_vector((width-1) downto 0);
              dout:     out std_logic_vector((width-1) downto 0));
    end component altera_std_synchronizer_bundle;

    -- signals for syncronising and debouncing rx in
    signal rxSyncronized:   std_ulogic;
    signal rxDebounceBuff:  std_ulogic_vector(3 downto 0);
    signal rx:              std_ulogic;

    -- state machine signals
    signal receiving:   std_ulogic;
    signal isBreak:     std_ulogic;
    signal oldRx:       std_ulogic;
    signal counter:     natural;
    signal bitIdx:      unsigned(3 downto 0);
    signal frame:       std_ulogic_vector(9 downto 0);
begin

    ---------------------------------------------------------------------------
    -- Input syncrhonisation and debouncing
    ---------------------------------------------------------------------------

    -- Synchronise incoming signals
    rxSync: altera_std_synchronizer_bundle
        generic map (depth => 2)
        port map (clk       => i_clk,
                  reset_n   => not i_reset,
                  din(0)    => i_rx,
                  dout(0)   => rxSyncronized);

    -- Debounce / check line is stable
    process (i_clk, i_reset)
    begin
        if (i_reset = '1') then
            -- Idle high
            rx <= '1';
            rxDebounceBuff <= (others => '1');
        elsif (rising_edge(i_clk)) then
            -- Feed signals through shift register
            rxDebounceBuff <= rxDebounceBuff(2 downto 0) &
                              rxSyncronized;

            -- Only change state if signal state is consistent
            if (rxDebounceBuff = "0000") then
                rx <= '0';
            elsif (rxDebounceBuff = "1111") then
                rx <= '1';
            end if;
        end if;
    end process;

    ---------------------------------------------------------------------------
    -- Receive state machine
    ---------------------------------------------------------------------------

    process (i_clk, i_reset)
    begin
        if (i_reset = '1') then
            receiving <= '0';
            isBreak <= '0';
            o_readData <= (others => '0');
            o_readDataValid <= '0';
            o_readDataError <= '0';
        elsif (rising_edge(i_clk)) then
            -- cache old value so we can detect edges
            oldRx <= rx;

            -- are we in the middle of receiving?
            if (receiving = '0') then
                -- currently idle
                -- clear rd_data_error and rd_data_valid flags
                o_readDataValid <= '0';
                o_readDataError <= '0';

                -- wait for falling edge
                -- to indicate start of Rx
                if ((rx = '0') and (oldRx = '1')) then
                    -- got it
                    receiving <= '1';
                    frame <= (others => '0');
                    bitIdx <= (others => '0');
                    isBreak <= '0';

                    -- sample first data bit halfway through
                    -- ie. BIT_TIME_NS / 2 from now
                    counter <= BIT_TIME_NS/2;
                end if;
            elsif (isBreak = '1') then
                -- we are currently receiving a break
                -- don't bother sampling the bits
                -- just wait for rx to return to idle
                if (rx = '1') then
                    -- end of break
                    isBreak <= '0';
                    receiving <= '0';
                end if;
            else
                -- reading a normal frame (so far)

                -- have we just sampled the stop bit?
                if (bitIdx = to_unsigned(10, 4)) then
                    -- yep
                    -- if all the bits (data, start and stop)
                    -- are zeros, then it's a break.
                    if (frame = (9 downto 0 => '0')) then
                        -- keep receiving until we detect
                        -- a rising edge (end of break)
                        isBreak <= '1';
                    elsif ((frame(9) = '0') OR (frame(0) = '1')) then
                        -- start bit = 1 or stop bit = 0
                        -- means we have an invalid frame
                        o_readDataError <= '1';
                        receiving <= '0';
                    else
                        -- data valid
                        o_readData <= frame(8 downto 1);
                        o_readDataValid <= '1';
                        receiving <= '0';
                    end if;
                else
                    -- We only sample the data
                    -- when the counter expires
                    if (counter <= CLOCK_PERIOD_NS) then
                        -- shift the data frame right by one
                        -- bringing in the current value
                        -- as the Msb
                        frame <= rx & frame(9 downto 1);
                        bitIdx <= bitIdx + to_unsigned(1, 4);

                        -- sample the next bit in one bit period
                        -- ie. half way through the next bit
                        counter <= BIT_TIME_NS;
                    else
                        counter <= counter - CLOCK_PERIOD_NS;
                    end if;
                end if;
            end if;
        end if;
    end process;

    -- outputs
    o_receiving <= receiving;
    o_isBreak <= isBreak;

end architecture synth;
