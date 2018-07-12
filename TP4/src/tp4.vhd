library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;
use common.vga_timings_640_480_pkg.all;

entity tp4 is
    port (CLOCK_50:     in      std_ulogic;
          KEY:          in      std_ulogic_vector(0 downto 0);
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
          VGA_SYNC:     out     std_ulogic);
end entity tp4;

architecture synth of tp4 is
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
    -- read data appears after 3 ticks
    --  1 to get it from the SRAM
    --  2 in the syncronizer
    component sram is
        port (i_clk:    in      std_ulogic; -- max clk 100MHz
              i_reset:  in      std_ulogic;
              -- inputs
              i_addr:   in      unsigned(17 downto 0);
              i_wdata:  in      std_ulogic_vector(15 downto 0);
              i_rnw:    in      std_ulogic;
              i_start:  in      std_ulogic;
              -- outputs
              o_rdata:  out     std_ulogic_vector(15 downto 0);
              -- status
              o_busy:   out     std_ulogic;
              -- bus ports
              io_data:  inout   std_ulogic_vector(15 downto 0);
              o_addr:   out     std_ulogic_vector(17 downto 0);
              o_nCE:    out     std_ulogic;
              o_nOE:    out     std_ulogic;
              o_nWE:    out     std_ulogic;
              o_nLB:    out     std_ulogic;
              o_nUB:    out     std_ulogic);
    end component sram;

    component delay is
        generic (DELAY: natural;
                 WIDTH: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              input:    in  std_ulogic_vector((WIDTH - 1) downto 0);
              output:   out std_ulogic_vector((WIDTH - 1) downto 0));
    end component delay;

    component adv7123 is
        generic (H_ACTIVE:      natural;    -- ticks
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

    component pll25M
        port (areset:   in std_logic;
              inclk0:   in std_logic;
              c0:       out std_logic;
              locked:   out std_logic);
    end component pll25M;

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


    type CoOrd is
    (
        CoOrd_X,
        CoOrd_Y,
        CoOrd_Z
    );

    constant NUM_COORDS:    natural := 5;

    signal clk25M:          std_ulogic;
    signal clk25M_locked:   std_ulogic;

    signal idle:            std_ulogic;
    signal idleDelayed:     std_ulogic;
    signal start_rotations: std_ulogic;
    signal currentCoOrd:    CoOrd;

    signal sram_address:    unsigned(17 downto 0);
    signal sram_rnw:        std_ulogic;
    signal sram_start:      std_ulogic;
    signal sram_rdata:      std_ulogic_vector(15 downto 0);
    signal sram_rdata_ext:  signed(31 downto 0);

    signal cordic_en:       std_ulogic;
    signal original_x:      signed(31 downto 0);
    signal original_y:      signed(31 downto 0);
    signal original_z:      signed(31 downto 0);
    signal rotated_x:       signed(31 downto 0);
    signal rotated_y:       signed(31 downto 0);
    signal rotated_z:       signed(31 downto 0);
    constant alpha:         unsigned(31 downto 0) := (others => '0');
    constant beta:          unsigned(31 downto 0) := (others => '0');
    constant gamma:         unsigned(31 downto 0) := (others => '0');
    signal cordic_valid:    std_ulogic;

    signal pixelOn:         std_ulogic;
    signal endOfFrame:      std_ulogic;
    signal pixelX:          unsigned((utils_pkg.min_width(H_ACTIVE) - 1) downto 0);
    signal pixelY:          unsigned((utils_pkg.min_width(V_ACTIVE) - 1) downto 0);

    signal reset:           std_ulogic;

begin

    reset <= not (KEY(0) or clk25M_locked);

    -----------------------------------------------------------------
    -- PLLs
    -----------------------------------------------------------------
    pll25M_inst: pll25M port map (areset  => '0',
                                  inclk0  => CLOCK_50,
                                  c0      => clk25M,
                                  locked  => clk25M_locked);

    -----------------------------------------------------------------
    -- SRAM
    -----------------------------------------------------------------

    sram_rnw <= '1';

    sramInst:
    sram port map (i_clk        => CLOCK_50,
                   i_reset      => reset,
                   -- inputs
                   i_addr       => sram_address,
                   i_wdata      => std_ulogic_vector(to_unsigned(0, 16)),
                   i_rnw        => sram_rnw,
                   i_start      => sram_start,
                   -- outputs
                   o_rdata      => sram_rdata,
                   -- status
                   o_busy       => open,
                   -- bus ports
                   io_data      => SRAM_DQ,
                   o_addr       => SRAM_ADDR,
                   o_nCE        => SRAM_CE_N,
                   o_nOE        => SRAM_OE_N,
                   o_nWE        => SRAM_WE_N,
                   o_nLB        => SRAM_LB_N,
                   o_nUB        => SRAM_UB_N);

    -- we extend the read sram data from Q9.7 to Q9.23
    sram_rdata_ext(15 downto 0) <= (others => '0');
    sram_rdata_ext(31 downto 16) <= signed(sram_rdata);

    -- We need to know when we are reading sram. This is the
    -- idle signal. However our reads are delayed by 3 ticks
    -- so we must delay idle by 3 ticks too
    dly:    delay
            generic map (DELAY => 3,
                         WIDTH => 1)
            port map (clk => CLOCK_50,
                      rst => reset,
                      input(0) => idle,
                      output(0) => idleDelayed);

    -- Control logic
    process (CLOCK_50, reset)
    begin
        if (reset = '1') then
            idle <= '0';
            sram_start <= '0';
        elsif (rising_edge(CLOCK_50)) then
            if (idle = '1') then
                -- wait for start signal
                if (start_rotations = '1') then
                    idle <= '0';
                    sram_address <= to_unsigned(0, 18);
                    sram_start <= '1';
                end if;
            else
                -- have we finished reading?
                if (sram_address = (to_unsigned(3 * NUM_COORDS, 18))) then
                    -- we are done
                    idle <= '1';
                    sram_start <= '0';
                end if;

                -- read the next address
                sram_address <= sram_address + to_unsigned(1, 18);
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- CORDIC 3D
    -----------------------------------------------------------------

    -- set up the input co-ordinates
    process (CLOCK_50, reset)
    begin
        if (reset = '1') then
            currentCoOrd <= CoOrd_X;
            cordic_en <= '0';
        elsif (rising_edge(CLOCK_50)) then
            -- deassert en (if it was set)
            cordic_en <= '0';

            if (idleDelayed) then
                currentCoOrd <= CoOrd_X;
            else
                -- sram_rdata should contain our data now
                -- we put it in the correct spot
                if (currentCoOrd = CoOrd_X) then
                    original_x <= sram_rdata_ext;
                    currentCoOrd <= CoOrd_Y;
                elsif (currentCoOrd = CoOrd_Y) then
                    original_y <= sram_rdata_ext;
                    currentCoOrd <= CoOrd_Z;
                elsif (currentCoOrd = CoOrd_Z) then
                    original_z <= sram_rdata_ext;
                    currentCoOrd <= CoOrd_X;

                    -- now all the data is valid start the cordic
                    cordic_en <= '1';
                end if;
            end if;
        end if;
    end process;

    cordic: cordic_rotation_3d
            generic map (N => 9,
                         M => 23,
                         STEPS => 10)
            port map (i_clk => CLOCK_50,
                      i_reset => reset,
                      i_en => cordic_en,
                      i_x => original_x,
                      i_y => original_y,
                      i_z => original_z,
                      i_alpha => alpha,
                      i_beta  => beta,
                      i_gamma => gamma,
                      o_x => rotated_x,
                      o_y => rotated_y,
                      o_z => rotated_z,
                      o_valid => cordic_valid);


    -----------------------------------------------------------------
    -- Video ram
    -----------------------------------------------------------------
    -- 640*480 bits, byte addressable = 38,400 bytes
    -- two read/write ports (although we never write from the second)
    -- A) clocked with CLOCK_50
    --    pipelined: read, set, write.
    --    The cordic gives us x,y which gives us our address
    --    we read that byte
    --    set the correct bit
    --    then write it back
    -- B) clocked with clk25M (read only)
    --    addressed by vga pixelX and pixelY
    --    ?? ticks of delay
    -----------------------------------------------------------------
    --video_ram_inst:
    --video_ram
    --port map (address_a => ,
    --          address_b => ,
    --          clock_a   => ,
    --          clock_b   => ,
    --          data_a    => ,
    --          data_b    => ,
    --          wren_a    => ,
    --          wren_b    => ,
    --          q_a       => ,
    --          q_b       => );

    -----------------------------------------------------------------
    -- VGA
    -----------------------------------------------------------------
    -- 640x480 with 25MHz clock -> 59.5 frames/second
    -- We update the video ram during the vertical blanking
    -- period which is 45 lines of 800 pixels = 1.44ms
    -----------------------------------------------------------------

    adv7123_inst:
    adv7123 generic map(H_ACTIVE        => H_ACTIVE,
                        H_FRONT_PORCH   => H_FRONT_PORCH,
                        H_SYNC          => H_SYNC,
                        H_BACK_PORCH    => H_BACK_PORCH,
                        V_ACTIVE        => V_ACTIVE,
                        V_FRONT_PORCH   => V_FRONT_PORCH,
                        V_SYNC          => V_SYNC,
                        V_BACK_PORCH    => V_BACK_PORCH)
            port map(clk => clk25M,
                     rst => reset,
                     rIn => (others => pixelOn),
                     gIn => (others => pixelOn),
                     bIn => (others => pixelOn),

                     pixelX     => pixelX,
                     pixelY     => pixelY,
                     endOfFrame => endOfFrame,

                     clkOut => VGA_CLK,
                     rOut   => VGA_R,
                     gOut   => VGA_G,
                     bOut   => VGA_B,
                     nBlank => VGA_BLANK,
                     nSync  => VGA_SYNC,
                     nHSync => VGA_HS,
                     nVSync => VGA_VS);

end architecture synth;
