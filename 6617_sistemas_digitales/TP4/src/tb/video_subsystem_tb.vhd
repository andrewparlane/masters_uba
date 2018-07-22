library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;

entity video_subsystem_tb is
end entity video_subsystem_tb;

architecture sim of video_subsystem_tb is
    component video_subsystem is
        port (i_clk100M:            in  std_ulogic;
              i_clk25M:             in  std_ulogic;
              i_reset:              in  std_ulogic;
              i_setPixelAddr:       in  unsigned(15 downto 0);
              i_setPixelBitMask:    in  unsigned(7 downto 0);
              i_setPixel:           in  std_ulogic;
              o_requestNewData:     out std_ulogic;
              o_vgaClk:             out std_ulogic;
              o_rOut:               out std_ulogic_vector(9 downto 0);
              o_gOut:               out std_ulogic_vector(9 downto 0);
              o_bOut:               out std_ulogic_vector(9 downto 0);
              o_nBlank:             out std_ulogic;
              o_nSync:              out std_ulogic;
              o_nHSync:             out std_ulogic;
              o_nVSync:             out std_ulogic);
    end component video_subsystem;

    component adv7123_sva_wrapper is
    end component adv7123_sva_wrapper;

    signal clk100M: std_ulogic := '0';
    signal clk25M:  std_ulogic := '0';
    signal reset:   std_ulogic;

    signal setPixelAddr:    unsigned(15 downto 0);
    signal setPixelBitMask: unsigned(7 downto 0);
    signal setPixel:        std_ulogic;
    signal requestNewData:  std_ulogic;

    signal nBlank:      std_ulogic;
    signal nSync:       std_ulogic;
    signal nHSync:      std_ulogic;
    signal nVSync:      std_ulogic;
    signal endOfFrame:  std_ulogic;

    signal rOut:        std_ulogic_vector(9 downto 0);
    signal gOut:        std_ulogic_vector(9 downto 0);
    signal bOut:        std_ulogic_vector(9 downto 0);

    signal clkOut:      std_ulogic;

    -- 100 MHz
    constant CLK_100MHZ:        natural := 100 * 1000 * 1000;
    constant CLK_100M_PERIOD:   time := 1 sec / CLK_100MHZ;
    -- 25 MHz
    constant CLK_25MHZ:         natural := 25 * 1000 * 1000;
    constant CLK_25M_PERIOD:    time := 1 sec / CLK_25MHZ;
begin

    clk100M <= not clk100M after (CLK_100M_PERIOD/2);
    clk25M <= not clk25M after (CLK_25M_PERIOD/2);

    dut: video_subsystem
        port map (i_clk100M             => clk100M,
                  i_clk25M              => clk25M,
                  i_reset               => reset,
                  i_setPixelAddr        => setPixelAddr,
                  i_setPixelBitMask     => setPixelBitMask,
                  i_setPixel            => setPixel,
                  o_requestNewData      => requestNewData,
                  o_vgaClk              => clkOut,
                  o_rOut                => rOut,
                  o_gOut                => gOut,
                  o_bOut                => bOut,
                  o_nBlank              => nBlank,
                  o_nSync               => nSync,
                  o_nHSync              => nHSync,
                  o_nVSync              => nVSync);

    sva:    adv7123_sva_wrapper;

    process
        variable pixelNum:      unsigned(18 downto 0);
    begin
        -- Reset the DUT
        reset <= '1';
        setPixel <= '0';
        setPixelAddr <= (others => '0');
        setPixelBitMask <= (others => '0');
        wait for (CLK_100M_PERIOD*5);
        wait until rising_edge(clk100M);
        reset <= '0';

        -------------------------------------------------------------
        -- FRAME 1 - blank
        -------------------------------------------------------------

        -- wait for requestNewData
        wait until (requestNewData = '1');
        wait until rising_edge(clk100M);
        -- do nothing

        -------------------------------------------------------------
        -- FRAME 2 - corner pixels
        -------------------------------------------------------------

        -- wait for requestNewData
        wait until (requestNewData = '1');

        -- set top left pixel
        wait until rising_edge(clk100M);    -- tick 0
        setPixelAddr <= to_unsigned(0, 16);
        setPixelBitMask <= "00000001";
        setPixel <= '1';
        wait until rising_edge(clk100M);    -- tick 1
        setPixel <= '0';
        wait until rising_edge(clk100M);    -- tick 2

        -- set top right pixel
        wait until rising_edge(clk100M);    -- tick 0
        setPixelAddr <= to_unsigned(79, 16);
        setPixelBitMask <= "10000000";
        setPixel <= '1';
        wait until rising_edge(clk100M);    -- tick 1
        setPixel <= '0';
        wait until rising_edge(clk100M);    -- tick 2

        -- set bottom left pixel
        wait until rising_edge(clk100M);    -- tick 0
        setPixelAddr <= to_unsigned(38320, 16);
        setPixelBitMask <= "00000001";
        setPixel <= '1';
        wait until rising_edge(clk100M);    -- tick 1
        setPixel <= '0';
        wait until rising_edge(clk100M);    -- tick 2

        -- set bottom right pixel
        wait until rising_edge(clk100M);    -- tick 0
        setPixelAddr <= to_unsigned(38399, 16);
        setPixelBitMask <= "10000000";
        setPixel <= '1';
        wait until rising_edge(clk100M);    -- tick 1
        setPixel <= '0';
        wait until rising_edge(clk100M);    -- tick 2

        -------------------------------------------------------------
        -- FRAME 2 - PLUS symbol
        -------------------------------------------------------------

        -- wait for requestNewData
        wait until (requestNewData = '1');

        -- vertical bar
        for y in 0 to 479 loop
            for x in 318 to 321 loop
                wait until rising_edge(clk100M);    -- tick 0
                pixelNum := to_unsigned((y * 640) + x, 19);
                setPixelAddr <= pixelNum(18 downto 3);
                setPixelBitMask <= (others => '0');
                setPixelBitMask(to_integer(pixelNum(2 downto 0))) <= '1';

                setPixel <= '1';
                wait until rising_edge(clk100M);    -- tick 1
                setPixel <= '0';
                wait until rising_edge(clk100M);    -- tick 2
             end loop;
        end loop;

        -- horizontal bar
        for y in 238 to 241 loop
            for x in 0 to 639 loop
                wait until rising_edge(clk100M);    -- tick 0
                pixelNum := to_unsigned((y * 640) + x, 19);
                setPixelAddr <= pixelNum(18 downto 3);
                setPixelBitMask <= (others => '0');
                setPixelBitMask(to_integer(pixelNum(2 downto 0))) <= '1';
                setPixel <= '1';
                wait until rising_edge(clk100M);    -- tick 1
                setPixel <= '0';
                wait until rising_edge(clk100M);    -- tick 2
             end loop;
        end loop;

        -------------------------------------------------------------
        -- FRAME 3 - blank
        -------------------------------------------------------------
        -- wait for requestNewData
        wait until (requestNewData = '1');

        -------------------------------------------------------------
        -- Finally wait until the next requestNewData
        -- which indicates end of frame
        -------------------------------------------------------------
        wait until (requestNewData = '1');


        std.env.stop;

    end process;

end architecture sim;
