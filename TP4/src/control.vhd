library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;
use common.type_pkg.all;

entity control is
    port (i_clk:            in  std_ulogic;
          i_reset:          in  std_ulogic;
          i_uartData:       in  std_ulogic_vector(7 downto 0);
          i_uartDataValid:  in  std_ulogic;
          i_requestNewData: in  std_ulogic;
          o_transformStart: out std_ulogic;
          o_sramStart:      out std_ulogic;
          o_sramRnW:        out std_ulogic;
          o_sramAddr:       out unsigned(17 downto 0);
          o_sramWdata:      out std_ulogic_vector(15 downto 0);
          o_waitingForData: out std_ulogic;
          o_transforming:   out std_ulogic;
          o_hexDisplays:    out slvArray(7 downto 0)(6 downto 0));
end entity control;

architecture synth of control is
    component multi_seven_seg_hex is
        generic (CIFRAS: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              en:       in  std_ulogic_vector((CIFRAS - 1) downto 0);
              hex:      in  unsignedArray((CIFRAS - 1) downto 0)(3 downto 0);
              display:  out slvArray((CIFRAS - 1) downto 0)(6 downto 0));
    end component multi_seven_seg_hex;

    type State is
    (
        State_WAITING_FOR_NUM_COORDS,
        State_WAITING_FOR_COORDS,
        State_IDLE,
        State_TRANSFORMING
    );

    signal currentState:        State;
    signal numCoordinates:      unsigned(15 downto 0);
    signal numCoordinateWords:  unsigned(17 downto 0);
    signal wordsReceived:       unsigned(17 downto 0);

    signal isUpper:             std_ulogic;

    signal sramAddr:            unsigned(17 downto 0);
    signal nextSramAddr:        unsigned(17 downto 0);

begin

    -- Display the expected number of words on the left hand
    -- block of 4 HEX displays.
    -- and the amount actually received on the right hand
    -- block of 4 HEX displays.
    -- Actually wordsReceived and numCoordinateWords are 18
    -- bits, and we have to ignore the upper two bits of ecah
    -- here, because we only have the 8 HEX outputs
    multi7SegInst:
    multi_seven_seg_hex
        generic map (CIFRAS => 8)
        port map (clk => i_clk,
                  rst => i_reset,
                  en => "11111111",
                  hex(7) => numCoordinateWords(15 downto 12),
                  hex(6) => numCoordinateWords(11 downto 8),
                  hex(5) => numCoordinateWords(7 downto 4),
                  hex(4) => numCoordinateWords(3 downto 0),
                  hex(3) => wordsReceived(15 downto 12),
                  hex(2) => wordsReceived(11 downto 8),
                  hex(1) => wordsReceived(7 downto 4),
                  hex(0) => wordsReceived(3 downto 0),
                  display => o_hexDisplays);

    -- we expect that amount of coordinates
    -- each of which has three components
    -- each of which is one word (16 bits)
    -- so the number of words expected
    -- is numCoordinates * 3
    -- = (numCoordinates << 1) + numCoordinates
    numCoordinateWords <= ('0' & numCoordinates & '0') +
                          ("00" & numCoordinates);

    process (i_clk, i_reset)
    begin
        if (i_reset = '1') then
            currentState <= State_WAITING_FOR_NUM_COORDS;

            sramAddr <= (others => '0');
            o_sramStart <= '0';
            o_sramRnW <= '1';

            o_transformStart <= '0';

            isUpper <= '0';
            numCoordinates <= (others => '0');
            wordsReceived <= (others => '0');
            nextSramAddr <= (others => '0');
        elsif (rising_edge(i_clk)) then

            -- transformStart and sramRnW should only be
            -- pulsed for one tick at a time
            o_transformStart <= '0';
            o_sramRnw <= '1';
            -- sramStart should only be one tick long
            -- for writes. However it can be longer for writes
            -- so we deassert it here, which can be overwritten
            -- in the transform case
            o_sramStart <= '0';

            case (currentState) is
                -----------------------------------------------------------------
                -- State_WAITING_FOR_NUM_COORDS
                -----------------------------------------------------------------
                -- Wait to receive two bytes over uart
                -- as a 16 bit little endien word
                -- which represents how many co-ordinates
                -- we are about to receive
                -----------------------------------------------------------------

                when State_WAITING_FOR_NUM_COORDS =>
                    if (i_uartDataValid = '1') then
                        -- got some data, is it the upper byte?
                        if (isUpper = '1') then
                            -- MSB
                            numCoordinates(15 downto 8) <= unsigned(i_uartData);

                            -- get the LSB of the next word
                            isUpper <= '0';

                            -- and that next word will be the first
                            -- of the co-ordinates
                            currentState <= State_WAITING_FOR_COORDS;

                            -- which we'll write to the first word of SRAM
                            nextSramAddr <= (others => '0');
                        else
                            -- LSB
                            numCoordinates(7 downto 0) <= unsigned(i_uartData);

                            -- get the MSB next
                            isUpper <= '1';
                        end if;
                    end if;

                -----------------------------------------------------------------
                -- State_WAITING_FOR_COORDS
                -----------------------------------------------------------------
                -- We receive all the coordinates over UART
                -- each coordinate component is sent as 16 bit
                -- little endien words. In the order X,Y,Z.
                -- Every time we receive a full word, we write
                -- it to SRAM.
                -----------------------------------------------------------------

                when State_WAITING_FOR_COORDS =>
                    -- are we done?
                    if (wordsReceived = numCoordinateWords) then
                        -- yep, go idle
                        currentState <= State_IDLE;
                    elsif (i_uartDataValid = '1') then
                        -- got some data, is it the upper byte?
                        if (isUpper = '1') then
                            -- MSB
                            o_sramWdata(15 downto 8) <= i_uartData;

                            -- write it to sram
                            sramAddr <= nextSramAddr;
                            o_sramStart <= '1';
                            o_sramRnW <= '0';
                            nextSramAddr <= nextSramAddr + 1;

                            -- get the LSB of the next word
                            isUpper <= '0';
                            wordsReceived <= wordsReceived + 1;
                        else
                            -- LSB
                            o_sramWdata(7 downto 0) <= i_uartData;

                            -- get the MSB next
                            isUpper <= '1';
                        end if;
                    end if;

                -----------------------------------------------------------------
                -- State_IDLE
                -----------------------------------------------------------------
                -- Do nothing until we receive the requestNewData
                -- signal. Once we get the request move to
                -- State_TRANSFORMING
                -----------------------------------------------------------------

                when State_IDLE =>
                    -- wait for start signal
                    if (i_requestNewData = '1') then
                        currentState <= State_TRANSFORMING;

                        -- start reading from sram
                        sramAddr <= to_unsigned(0, 18);
                        o_sramStart <= '1';
                        o_sramRnW <= '1';

                        -- force the transform unit to expect
                        -- the X component
                        o_transformStart <= '1';
                    end if;

                -----------------------------------------------------------------
                -- State_TRANSFORMING
                -----------------------------------------------------------------
                -- Read all the coordinates back out of SRAM
                -- word by word.
                -----------------------------------------------------------------

                when State_TRANSFORMING =>
                    -- have we finished reading?
                    if (sramAddr = (numCoordinateWords - 1)) then
                        -- we are done
                        currentState <= State_IDLE;
                        o_sramStart <= '0';
                    else
                        o_sramStart <= '1';
                    end if;

                    -- read the next address
                    sramAddr <= sramAddr + to_unsigned(1, 18);

                -----------------------------------------------------------------
                -- Others
                -----------------------------------------------------------------
                -- We shouldn't get here
                -- Put some logic in to reset the state machine
                -- just in case something goes wrong.
                -----------------------------------------------------------------

                when others =>
                    currentState <= State_WAITING_FOR_NUM_COORDS;
            end case;
        end if;
    end process;

    -- sramAddr
    o_sramAddr <= sramAddr;

    -- couple of status outputs
    o_waitingForData <= '1' when ((currentState = State_WAITING_FOR_NUM_COORDS) OR
                                  (currentState = State_WAITING_FOR_COORDS))
                            else '0';

    o_transforming <= '1' when (currentState = State_TRANSFORMING)
                          else '0';

end architecture synth;
