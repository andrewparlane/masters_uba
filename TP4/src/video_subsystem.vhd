library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;
use common.vga_timings_640_480_pkg.all;

entity video_subsystem is
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
end entity video_subsystem;

architecture synth of video_subsystem is
    component video_ram
        port (address_a:    in std_logic_vector (15 downto 0);
              address_b:    in std_logic_vector (18 downto 0);
              clock_a:      in std_logic;
              clock_b:      in std_logic;
              data_a:       in std_logic_vector (7 downto 0);
              data_b:       in std_logic_vector (0 downto 0);
              wren_a:       in std_logic;
              wren_b:       in std_logic;
              q_a:          out std_logic_vector (7 downto 0);
              q_b:          out std_logic_vector (0 downto 0));
    end component video_ram;

    component adv7123 is
        generic (DELAY_TICKS:   natural;    -- ticks

                 H_ACTIVE:      natural;    -- ticks
                 H_FRONT_PORCH: natural;    -- ticks
                 H_SYNC:        natural;    -- ticks
                 H_BACK_PORCH:  natural;    -- ticks

                 V_ACTIVE:      natural;    -- líneas
                 V_FRONT_PORCH: natural;    -- líneas
                 V_SYNC:        natural;    -- líneas
                 V_BACK_PORCH:  natural);   -- líneas

        port (clk:          in  std_ulogic;
              rst:          in  std_ulogic;
              rIn:          in  std_ulogic_vector(9 downto 0);
              gIn:          in  std_ulogic_vector(9 downto 0);
              bIn:          in  std_ulogic_vector(9 downto 0);
              pixelX:       out unsigned((utils_pkg.min_width(H_ACTIVE) - 1) downto 0);
              pixelY:       out unsigned((utils_pkg.min_width(V_ACTIVE) - 1) downto 0);
              endOfFrame:   out std_ulogic;
              clkOut:       out std_ulogic;
              rOut:         out std_ulogic_vector(9 downto 0);
              gOut:         out std_ulogic_vector(9 downto 0);
              bOut:         out std_ulogic_vector(9 downto 0);
              nBlank:       out std_ulogic;
              nSync:        out std_ulogic;
              nHSync:       out std_ulogic;
              nVSync:       out std_ulogic);
    end component adv7123;

    component delay is
        generic (DELAY: natural;
                 WIDTH: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              output:   out std_ulogic_vector((WIDTH - 1) downto 0));
    end component delay;

    constant PIXEL_X_WIDTH: natural := utils_pkg.min_width(H_ACTIVE);
    constant PIXEL_Y_WIDTH: natural := utils_pkg.min_width(V_ACTIVE);

    constant LAST_VIDEO_RAM_ADDR:   natural := ((H_ACTIVE * V_ACTIVE) / 8) - 1;

    signal endOfFrame:      std_ulogic;
    signal pixelX:          unsigned((PIXEL_X_WIDTH - 1) downto 0);
    signal pixelY:          unsigned((PIXEL_Y_WIDTH - 1) downto 0);

    signal setPixelDelayed:         std_ulogic;
    signal setPixelAddrDelayed:     unsigned(15 downto 0);
    signal setPixelBitMaskDelayed:  unsigned(7 downto 0);

    signal sramAddrPortA100MHz:     unsigned(15 downto 0);
    signal wdataPortA100MHz:        unsigned(7 downto 0);
    signal rdataPortA100MHz:        unsigned(7 downto 0);
    signal wenPortA100MHz:          std_ulogic;

    signal sramAddrPortA25MHz:      unsigned(18 downto 0);
    signal pixelOn:                 std_ulogic;

    signal zeroing:                 std_ulogic;
    signal zeroingAddr:             unsigned(15 downto 0);

begin

    -----------------------------------------------------------------
    -- Delays
    -----------------------------------------------------------------
    -- We first read the data at i_setPixelAddr
    -- then 2 clock ticks later we set the correct bit
    -- and write it back
    -----------------------------------------------------------------

    setPixelAddrDelay: delay
        generic map (DELAY => 2,
                     WIDTH => 16)
        port map (clk => i_clk100M,
                  rst => i_reset,
                  input => std_ulogic_vector(i_setPixelAddr),
                  unsigned(output) => setPixelAddrDelayed);

    setPixelBitMaskDelay: delay
        generic map (DELAY => 2,
                     WIDTH => 8)
        port map (clk => i_clk100M,
                  rst => i_reset,
                  input => std_ulogic_vector(i_setPixelBitMask),
                  unsigned(output) => setPixelBitMaskDelayed);

    setPixelDelay: delay
        generic map (DELAY => 2,
                     WIDTH => 1)
        port map (clk => i_clk100M,
                  rst => i_reset,
                  input(0) => i_setPixel,
                  output(0) => setPixelDelayed);


    -----------------------------------------------------------------
    -- Video ram
    -----------------------------------------------------------------
    -- 640*480 bits, byte addressable = 38,400 bytes
    -- two read/write ports (although we never write from the second)
    -- A) clocked with i_clk100M
    --    pipelined: read, set, write.
    --    The cordic gives us x,y which gives us our address
    --    we read that byte
    --    set the correct bit
    --    then write it back
    -- B) clocked with clk25M (read only)
    --    addressed by vga pixelX and pixelY
    -----------------------------------------------------------------

    video_ram_inst: video_ram
    port map (-- PORT A @100MHz
              clock_a       => i_clk100M,
              address_a     => std_logic_vector(sramAddrPortA100MHz),
              data_a        => std_logic_vector(wdataPortA100MHz),
              wren_a        => wenPortA100MHz,
              unsigned(q_a) => rdataPortA100MHz,
              -- PORT B @25MHz
              clock_b       => i_clk25M,
              address_b     => std_logic_vector(sramAddrPortA25MHz),
              data_b        => "0",
              wren_b        => '0',
              q_b(0)        => pixelOn);

    -- logic as to which byte is set
    process (all)
    begin
        if (zeroing = '1') then
            -- when we are zeroing memory, write address
            -- is the address generated by the zeroing logic.
            -- we are always writing and the value we write is 0
            sramAddrPortA100MHz <= zeroingAddr;
            wdataPortA100MHz    <= (others => '0');
            wenPortA100MHz      <= '1';
        elsif (i_setPixel = '1') then
            -- when we get a setPixel request, we read from
            -- i_setPixelAddr
            sramAddrPortA100MHz <= i_setPixelAddr;
            wdataPortA100MHz    <= (others => '0');
            wenPortA100MHz      <= '0';
        else
            -- Otherwise two ticks after reading we write
            -- the data back but ORd with the bit mask
            sramAddrPortA100MHz <= setPixelAddrDelayed;
            wdataPortA100MHz    <= rdataPortA100MHz OR
                                   setPixelBitMaskDelayed;
            wenPortA100MHz      <= setPixelDelayed;
        end if;
    end process;

    -----------------------------------------------------------------
    -- VGA
    -----------------------------------------------------------------
    -- 640x480 with 25MHz clock -> 59.5 frames/second
    -- We update the video ram during the vertical blanking
    -- period which is 45 lines of 800 pixels = 1.44ms
    -----------------------------------------------------------------

    adv7123Inst: adv7123
        generic map(DELAY_TICKS     => 2,   -- it takes 2 ticks to read from SRAM

                    H_ACTIVE        => H_ACTIVE,
                    H_FRONT_PORCH   => H_FRONT_PORCH,
                    H_SYNC          => H_SYNC,
                    H_BACK_PORCH    => H_BACK_PORCH,
                    V_ACTIVE        => V_ACTIVE,
                    V_FRONT_PORCH   => V_FRONT_PORCH,
                    V_SYNC          => V_SYNC,
                    V_BACK_PORCH    => V_BACK_PORCH)
        port map(clk => i_clk25M,
                 rst => i_reset,
                 rIn => (others => pixelOn),
                 gIn => (others => pixelOn),
                 bIn => (others => pixelOn),

                 pixelX     => pixelX,
                 pixelY     => pixelY,
                 endOfFrame => endOfFrame,

                 clkOut => o_vgaClk,
                 rOut   => o_rOut,
                 gOut   => o_gOut,
                 bOut   => o_bOut,
                 nBlank => o_nBlank,
                 nSync  => o_nSync,
                 nHSync => o_nHSync,
                 nVSync => o_nVSync);

    sramAddrPortA25MHz <= to_unsigned((to_integer(pixelY) * H_ACTIVE) + to_integer(pixelX), 19);

    -----------------------------------------------------------------
    -- Zeroing
    -----------------------------------------------------------------
    -- logic to zero SRAM and then request new data
    -----------------------------------------------------------------

    process (i_clk100M, i_reset)
    begin
        if (i_reset = '1') then
            zeroing <= '0';
            zeroingAddr <= (others => '0');
            o_requestNewData <= '0';
        elsif (rising_edge(i_clk100M)) then
            -- only pulse for one tick
            o_requestNewData <= '0';

            if (zeroing = '1') then
                -- we are currently zeroing video ram
                -- update the address
                zeroingAddr <= zeroingAddr + to_unsigned(1, 16);

                -- are we done?
                if (zeroingAddr = LAST_VIDEO_RAM_ADDR) then
                    zeroing <= '0';
                    o_requestNewData <= '1';
                end if;
            elsif (endOfFrame = '1') then
                -- we are entering the vertical blanking region
                -- so update the video ram.
                -- start by zeroing the data
                zeroing <= '1';
                zeroingAddr <= (others => '0');
            end if;
        end if;
    end process;

end architecture synth;
