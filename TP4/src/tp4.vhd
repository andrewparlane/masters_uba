library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.type_pkg.all;

entity tp4 is
    port (CLOCK_50:     in      std_ulogic;
          KEY:          in      std_ulogic_vector(3 downto 0);
          SW:           in      std_ulogic_vector(0 downto 0);
          GPIO_UART_RX: in      std_ulogic;
          LEDR:         out     std_ulogic_vector(3 downto 0);
          LEDG:         out     std_ulogic_vector(7 downto 0);
          SRAM_ADDR:    out     std_ulogic_vector(17 downto 0);
          SRAM_DQ:      inout   std_ulogic_vector(15 downto 0);
          SRAM_WE_N:    out     std_ulogic;
          SRAM_OE_N:    out     std_ulogic;
          SRAM_UB_N:    out     std_ulogic;
          SRAM_LB_N:    out     std_ulogic;
          SRAM_CE_N:    out     std_ulogic;
          VGA_R:        out     std_ulogic_vector(9 downto 0);
          VGA_G:        out     std_ulogic_vector(9 downto 0);
          VGA_B:        out     std_ulogic_vector(9 downto 0);
          VGA_CLK:      out     std_ulogic;
          VGA_BLANK:    out     std_ulogic;
          VGA_HS:       out     std_ulogic;
          VGA_VS:       out     std_ulogic;
          VGA_SYNC:     out     std_ulogic;
          HEX0:         out     std_ulogic_vector(6 downto 0);
          HEX1:         out     std_ulogic_vector(6 downto 0);
          HEX2:         out     std_ulogic_vector(6 downto 0);
          HEX3:         out     std_ulogic_vector(6 downto 0);
          HEX4:         out     std_ulogic_vector(6 downto 0);
          HEX5:         out     std_ulogic_vector(6 downto 0);
          HEX6:         out     std_ulogic_vector(6 downto 0);
          HEX7:         out     std_ulogic_vector(6 downto 0));
end entity tp4;

architecture synth of tp4 is
    component control is
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
    end component control;

    component cordic_rotation_3d is
        generic (N: natural;
                 M: natural;
                 STEPS: natural);
        port (i_clk:    in  std_ulogic;
              i_reset:  in  std_ulogic;
              i_en:     in  std_ulogic;
              i_x:      in  signed((N + M - 1) downto 0);
              i_y:      in  signed((N + M - 1) downto 0);
              i_z:      in  signed((N + M - 1) downto 0);
              i_alpha:  in  unsigned((N + M - 1) downto 0);
              i_beta:   in  unsigned((N + M - 1) downto 0);
              i_gamma:  in  unsigned((N + M - 1) downto 0);
              o_x:      out signed((N + M - 1) downto 0);
              o_y:      out signed((N + M - 1) downto 0);
              o_z:      out signed((N + M - 1) downto 0);
              o_valid:  out std_ulogic);
    end component cordic_rotation_3d;

    -- writes take two cycles
    -- read data appears after 4 ticks
    --  1 to process the start request
    --  1 to get it from the SRAM
    --  2 in the syncronizer
    component sram is
        port (i_clk:            in      std_ulogic; -- max clk 100MHz
              i_reset:          in      std_ulogic;
              -- inputs
              i_addr:           in      unsigned(17 downto 0);
              i_wdata:          in      std_ulogic_vector(15 downto 0);
              i_rnw:            in      std_ulogic;
              i_start:          in      std_ulogic;
              -- outputs
              o_rdata:          out     std_ulogic_vector(15 downto 0);
              -- status
              o_busy:           out     std_ulogic;
              o_rdata_valid:    out     std_ulogic;
              -- bus ports
              io_data:          inout   std_ulogic_vector(15 downto 0);
              o_addr:           out     std_ulogic_vector(17 downto 0);
              o_nCE:            out     std_ulogic;
              o_nOE:            out     std_ulogic;
              o_nWE:            out     std_ulogic;
              o_nLB:            out     std_ulogic;
              o_nUB:            out     std_ulogic);
    end component sram;

    component transform is
        port (i_clk:                in  std_ulogic;
              i_reset:              in  std_ulogic;
              i_start:              in  std_ulogic;
              i_value:              in  signed(15 downto 0);
              i_valid:              in  std_ulogic;
              i_alpha:              in  unsigned(31 downto 0);
              i_beta:               in  unsigned(31 downto 0);
              i_gamma:              in  unsigned(31 downto 0);
              o_setPixelAddr:       out unsigned(15 downto 0);
              o_setPixelBitMask:    out unsigned(7 downto 0);
              o_setPixel:           out std_ulogic);
    end component transform;

    component video_subsystem is
        port (i_clk100M:            in  std_ulogic;
              i_clk25M:             in  std_ulogic;
              i_reset:              in  std_ulogic;
              i_setPixelAddr:       in  unsigned(15 downto 0);
              i_setPixelBitMask:    in  unsigned(7 downto 0);
              i_setPixel:           in  std_ulogic;
              o_endOfFrame:         out std_ulogic;
              o_dataDuringActive:   out std_ulogic;
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

    component buttons is
        port (i_clk:            in  std_ulogic;
              i_reset:          in  std_ulogic;
              i_buttonAlpha:    in  std_ulogic;
              i_buttonBeta:     in  std_ulogic;
              i_buttonGamma:    in  std_ulogic;
              i_reverse:        in  std_ulogic;
              i_update:         in  std_ulogic;
              o_alpha:          out unsigned(31 downto 0);
              o_beta:           out unsigned(31 downto 0);
              o_gamma:          out unsigned(31 downto 0);
              o_alphaPressed:   out std_ulogic;
              o_betaPressed:    out std_ulogic;
              o_gammaPressed:   out std_ulogic);
    end component buttons;

    signal clk25M:          std_ulogic;
    signal clk100M:         std_ulogic;
    signal pll_locked:      std_ulogic;

    signal uart_rdata:          std_ulogic_vector(7 downto 0);
    signal uart_rdata_valid:    std_ulogic;

    signal sram_address:        unsigned(17 downto 0);
    signal sram_rnw:            std_ulogic;
    signal sram_start:          std_ulogic;
    signal sram_rdata:          std_ulogic_vector(15 downto 0);
    signal sram_wdata:          std_ulogic_vector(15 downto 0);
    signal sram_rdata_valid:    std_ulogic;

    signal alpha:         unsigned(31 downto 0);
    signal beta:          unsigned(31 downto 0);
    signal gamma:         unsigned(31 downto 0);

    signal transformStart:  std_ulogic;
    signal setPixel:        std_ulogic;
    signal setPixelAddr:    unsigned(15 downto 0);
    signal setPixelBitMask: unsigned(7 downto 0);
    signal endOfFrame:      std_ulogic;
    signal requestNewData:  std_ulogic;

    signal reset:           std_ulogic;

    signal led_in_rx_mode:  std_ulogic;
    signal led_rx:          std_ulogic;
    signal led_transform:   std_ulogic;
    signal led_error:       std_ulogic;
    signal led_reset:       std_ulogic;
    signal led_alpha:       std_ulogic;
    signal led_beta:        std_ulogic;
    signal led_gamma:       std_ulogic;

begin

    -- in reset if either the reset button is pressed
    -- or the PLL is not locked
    reset <= not (KEY(0) and pll_locked);
    led_reset <= reset;

    -----------------------------------------------------------------
    -- LEDs
    -----------------------------------------------------------------
    LEDR(0) <= led_in_rx_mode;
    LEDR(1) <= led_rx;
    LEDR(2) <= led_transform;
    LEDR(3) <= led_error;

    LEDG(1 downto 0) <= (others => led_reset);
    LEDG(3 downto 2) <= (others => led_alpha);
    LEDG(5 downto 4) <= (others => led_beta);
    LEDG(7 downto 6) <= (others => led_gamma);

    -----------------------------------------------------------------
    -- Buttons
    -----------------------------------------------------------------
    -- The buttons and the switch are put through a syncronizer
    -- to avoid metastability.
    -- We update alpha, beta and gamma on the endOfFrame signal
    -- which gives plenty of time before we actually need the
    -- new angles
    -----------------------------------------------------------------
    buttonsInst: buttons
        port map (i_clk             => clk100M,
                  i_reset           => reset,
                  i_buttonAlpha     => not KEY(1),
                  i_buttonBeta      => not KEY(2),
                  i_buttonGamma     => not KEY(3),
                  i_reverse         => SW(0),
                  i_update          => endOfFrame,
                  o_alpha           => alpha,
                  o_beta            => beta,
                  o_gamma           => gamma,
                  o_alphaPressed    => led_alpha,
                  o_BetaPressed     => led_beta,
                  o_gammaPressed    => led_gamma);

    ----------------------------------------------------------------
    -- PLLs
    -----------------------------------------------------------------
    pll_inst: pll port map (areset  => '0',
                            inclk0  => CLOCK_50,
                            c0      => clk100M,
                            c1      => clk25M,
                            locked  => pll_locked);

    -----------------------------------------------------------------
    -- Control logic
    -----------------------------------------------------------------
    controlInst: control
        port map (i_clk             => clk100M,
                  i_reset           => reset,
                  i_uartData        => uart_rdata,
                  i_uartDataValid   => uart_rdata_valid,
                  i_requestNewData  => requestNewData,
                  o_transformStart  => transformStart,
                  o_sramStart       => sram_start,
                  o_sramRnW         => sram_rnw,
                  o_sramAddr        => sram_address,
                  o_sramWdata       => sram_wdata,
                  o_waitingForData  => led_in_rx_mode,
                  o_transforming    => led_transform,
                  o_hexDisplays(0)  => HEX0,
                  o_hexDisplays(1)  => HEX1,
                  o_hexDisplays(2)  => HEX2,
                  o_hexDisplays(3)  => HEX3,
                  o_hexDisplays(4)  => HEX4,
                  o_hexDisplays(5)  => HEX5,
                  o_hexDisplays(6)  => HEX6,
                  o_hexDisplays(7)  => HEX7);

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
                  i_rx              => GPIO_UART_RX,
                  o_readData        => uart_rdata,
                  o_readDataValid   => uart_rdata_valid,
                  o_readDataError   => open,
                  o_receiving       => led_rx,
                  o_isBreak         => open);

    -----------------------------------------------------------------
    -- SRAM
    -----------------------------------------------------------------
    sramInst:
    sram port map (i_clk        => clk100M,
                   i_reset      => reset,
                   -- inputs
                   i_addr           => sram_address,
                   i_wdata          => sram_wdata,
                   i_rnw            => sram_rnw,
                   i_start          => sram_start,
                   -- outputs
                   o_rdata          => sram_rdata,
                   -- status
                   o_busy           => open,
                   o_rdata_valid    => sram_rdata_valid,
                   -- bus ports
                   io_data          => SRAM_DQ,
                   o_addr           => SRAM_ADDR,
                   o_nCE            => SRAM_CE_N,
                   o_nOE            => SRAM_OE_N,
                   o_nWE            => SRAM_WE_N,
                   o_nLB            => SRAM_LB_N,
                   o_nUB            => SRAM_UB_N);

    -----------------------------------------------------------------
    -- Rotate the co-ordinates and obtain the pixel address
    -----------------------------------------------------------------
    transformInst: transform
        port map (i_clk              => clk100M,
                  i_reset            => reset,
                  i_start            => transformStart,
                  i_value            => signed(sram_rdata),
                  i_valid            => sram_rdata_valid,
                  i_alpha            => alpha,
                  i_beta             => beta,
                  i_gamma            => gamma,
                  o_setPixelAddr     => setPixelAddr,
                  o_setPixelBitMask  => setPixelBitMask,
                  o_setPixel         => setPixel);

    -----------------------------------------------------------------
    -- Video subsystem
    -----------------------------------------------------------------
    videoSubystem: video_subsystem
        port map (i_clk100M             => clk100M,
                  i_clk25M              => clk25M,
                  i_reset               => reset,
                  i_setPixelAddr        => setPixelAddr,
                  i_setPixelBitMask     => setPixelBitMask,
                  i_setPixel            => setPixel,
                  o_endOfFrame          => endOfFrame,
                  o_dataDuringActive    => led_error,
                  o_requestNewData      => requestNewData,
                  o_vgaClk              => VGA_CLK,
                  o_rOut                => VGA_R,
                  o_gOut                => VGA_G,
                  o_bOut                => VGA_B,
                  o_nBlank              => VGA_BLANK,
                  o_nSync               => VGA_SYNC,
                  o_nHSync              => VGA_HS,
                  o_nVSync              => VGA_VS);

end architecture synth;
