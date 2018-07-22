library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;
use common.type_pkg.all;

library altera_mf;
use altera_mf.all;

entity sram_test is
    port (CLOCK_50:     in      std_ulogic;
          KEY:          in      std_ulogic_vector(3 downto 0);
          SW:           in      std_ulogic_vector(17 downto 0);
          SRAM_ADDR:    out     std_ulogic_vector(17 downto 0);
          SRAM_DQ:      inout   std_ulogic_vector(15 downto 0);
          SRAM_WE_N:    out     std_ulogic;
          SRAM_OE_N:    out     std_ulogic;
          SRAM_UB_N:    out     std_ulogic;
          SRAM_LB_N:    out     std_ulogic;
          SRAM_CE_N:    out     std_ulogic;
          LEDR:         out     std_ulogic_vector(17 downto 0);
          HEX0:         out     std_ulogic_vector(6 downto 0);
          HEX1:         out     std_ulogic_vector(6 downto 0);
          HEX2:         out     std_ulogic_vector(6 downto 0);
          HEX3:         out     std_ulogic_vector(6 downto 0);
          HEX4:         out     std_ulogic_vector(6 downto 0);
          HEX5:         out     std_ulogic_vector(6 downto 0);
          HEX6:         out     std_ulogic_vector(6 downto 0);
          HEX7:         out     std_ulogic_vector(6 downto 0));
end entity sram_test;

architecture synth of sram_test is
    -- writes take two cycles
    -- read data appears after 3 ticks
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

    component multi_seven_seg_hex is
        generic (CIFRAS: natural);
        port (clk:      in  std_ulogic;
              rst:      in  std_ulogic;
              en:       in  std_ulogic_vector((CIFRAS - 1) downto 0);
              hex:      in  unsignedArray((CIFRAS - 1) downto 0)(3 downto 0);
              display:  out slvArray((CIFRAS - 1) downto 0)(6 downto 0));
    end component multi_seven_seg_hex;

    component altera_std_synchronizer_bundle is
        generic (DEPTH : integer := 3;              -- must be >= 2
                 WIDTH : integer := 1);
        port (clk     : in  std_logic;
              reset_n : in  std_logic;
              din     : in  std_logic_vector(width-1 downto 0);
              dout    : out std_logic_vector(width-1 downto 0));
    end component altera_std_synchronizer_bundle;

    component pll
        port (areset:   in  std_logic;
              inclk0:   in  std_logic;
              c0:       out std_logic;
              c1:       out std_logic;
              locked:   out std_logic);
    end component;

    signal rdata:   unsigned(15 downto 0);
    signal wdata:   unsigned(15 downto 0);
    signal start:   std_ulogic;
    signal busy:    std_ulogic;
    signal rnw:     std_ulogic;

    signal rst:                 std_ulogic;
    signal clear:               std_ulogic;
    signal inc:                 std_ulogic;
    signal waitingForRelease:   boolean;

    signal addr:                unsigned(17 downto 0);
    signal lastAddr:            unsigned(17 downto 0);

    signal readWhenFree:    std_ulogic;
    signal valid:           std_ulogic;
    signal v:               unsigned(15 downto 0);
    signal reads:           unsigned(3 downto 0);

    signal clk100M:         std_ulogic;
    signal pll_locked:      std_ulogic;

begin

    pll_inst: pll
        port map (areset  => '0',
                  inclk0  => CLOCK_50,
                  c0      => clk100M,
                  c1      => open,
                  locked  => pll_locked);

    rst <= not (KEY(0) and pll_locked);

    syncSW: altera_std_synchronizer_bundle
    generic map (DEPTH => 2,
                 WIDTH => 18)
    port map    (clk        => clk100M,
                 reset_n    => not rst,
                 din        => std_logic_vector(SW),
                 unsigned(dout)       => addr);

    syncButtons: altera_std_synchronizer_bundle
    generic map (DEPTH => 2,
                 WIDTH => 2)
    port map    (clk        => clk100M,
                 reset_n    => not rst,
                 din(0)     => not KEY(1),
                 din(1)     => not KEY(3),
                 dout(0)    => clear,
                 dout(1)    => inc);

    LEDR(0) <= rst;
    LEDR(1) <= clear;
    LEDR(2) <= inc;
    LEDR(3) <= '1' when waitingForRelease else '0';
    LEDR(4) <= rnw;
    LEDR(5) <= start;
    LEDR(6) <= busy;

    process (clk100M, rst)
    begin
        if (rst = '1') then
            v <= (others => '0');
            reads <= (others => '0');
        elsif (rising_edge(clk100M)) then
            if (valid = '1') then
                v <= rdata;
                reads <= reads + to_unsigned(1, 4);
            end if;
        end if;
    end process;

    process (clk100M, rst)
    begin
        if (rst = '1') then
            rnw <= '1';
            wdata <= (others => '0');
            readWhenFree <= '1';
            waitingForRelease <= false;
        elsif (rising_edge(clk100M)) then
            -- start and rnw only high for one pulse at a time
            start <= '0';
            rnw <= '1'; -- read

            lastAddr <= addr;

            if (waitingForRelease) then
                -- don't allow anything more until
                -- inc and clear are released
                if ((inc = '0') and
                    (clear = '0')) then
                    waitingForRelease <= false;
                end if;
            elsif (clear = '1') then
                wdata <= (others => '0');
                rnw <= '0'; -- write
                start <= '1';
                readWhenFree <= '1';
                waitingForRelease <= true;
            elsif (inc = '1') then
                wdata <= v + to_unsigned(1, wdata'length);
                rnw <= '0'; -- write
                start <= '1';
                readWhenFree <= '1';
                waitingForRelease <= true;
            else
                rnw <= '1'; -- read
                if ((lastAddr /= addr) or
                    ((busy = '0') and
                     (readWhenFree = '1'))) then
                    start <= '1';
                    readWhenFree <= '0';
                end if;
            end if;
        end if;
    end process;

    inst: sram port map (i_clk              => clk100M,
                         i_reset            => rst,
                         -- input
                         i_addr             => addr,
                         i_wdata            => std_ulogic_vector(wdata),
                         i_rnw              => rnw,
                         i_start            => start,
                         -- output
                         unsigned(o_rdata)  => rdata,
                         -- status
                         o_busy             => busy,
                         o_rdata_valid      => valid,
                         -- bus ports
                         io_data            => SRAM_DQ,
                         o_addr             => SRAM_ADDR,
                         o_nCE              => SRAM_CE_N,
                         o_nOE              => SRAM_OE_N,
                         o_nWE              => SRAM_WE_N,
                         o_nLB              => SRAM_LB_N,
                         o_nUB              => SRAM_UB_N);

    multi7SegInst:
    multi_seven_seg_hex generic map (CIFRAS => 8)
                        port map (clk => clk100M,
                                  rst => rst,
                                  en => "10001111",
                                  hex(0) => unsigned(v(3 downto 0)),
                                  hex(1) => unsigned(v(7 downto 4)),
                                  hex(2) => unsigned(v(11 downto 8)),
                                  hex(3) => unsigned(v(15 downto 12)),
                                  hex(7) => unsigned(reads(3 downto 0)),
                                  hex(6 downto 4) => (to_unsigned(0,4),
                                                      to_unsigned(0,4),
                                                      to_unsigned(0,4)),
                                  display(7) => HEX7,
                                  display(6) => HEX6,
                                  display(5) => HEX5,
                                  display(4) => HEX4,
                                  display(3) => HEX3,
                                  display(2) => HEX2,
                                  display(1) => HEX1,
                                  display(0) => HEX0);

end architecture synth;
