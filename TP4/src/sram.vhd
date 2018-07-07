library ieee;
use ieee.std_logic_1164.all;

library altera_mf;
use altera_mf.all;

-- writes take two cycles
-- read data appears after 3 ticks
--  1 to get it from the SRAM
--  2 in the syncronizer
entity sram is
    port (i_clk:    in      std_ulogic; -- max clk 100MHz
          i_reset:  in      std_ulogic;
          -- inputs
          i_addr:   in      std_ulogic_vector(17 downto 0);
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
end entity sram;

architecture synth of sram is

    component altera_std_synchronizer_bundle is
    generic (DEPTH : integer := 3;              -- must be >= 2
             WIDTH : integer := 1);
    port (clk     : in  std_logic;
          reset_n : in  std_logic;
          din     : in  std_logic_vector(width-1 downto 0);
          dout    : out std_logic_vector(width-1 downto 0));
    end component altera_std_synchronizer_bundle;

    signal busy:    std_ulogic;
begin

    -- syncronize the input data
    rdata_sync: altera_std_synchronizer_bundle
        generic map (DEPTH => 2,
                     WIDTH => 16)
        port map    (clk        => i_clk,
                     reset_n    => not i_reset,
                     din        => std_logic_vector(io_data),
                     std_ulogic_vector(dout)    => o_rdata);

    process (i_clk, i_reset)
    begin
        if (i_reset = '1') then
            o_nCE <= '1';
            o_nOE <= '1';
            o_nWE <= '1';
            o_nLB <= '1';
            o_nUB <= '1';
            io_data <= (others => 'Z');

            busy <= '0';
        elsif (rising_edge(i_clk)) then
            if (busy = '0') then
                -- not doing anything
                -- wait for read or write request
                if (i_start) then
                    -- we have a request
                    o_addr <= i_addr;

                    if (i_rnw = '1') then
                        -- read
                        io_data <= (others => 'Z');
                        o_nOE <= '0';
                        o_nWE <= '1';
                    else
                        -- write
                        io_data <= i_wdata;
                        o_nOE <= '1';
                        o_nWE <= '0';

                        -- we take more than one cycle for writes
                        -- so have to say we're busy
                        busy <= '1';
                    end if;

                    o_nCE <= '0';
                    o_nUB <= '0';
                    o_nLB <= '0';
                else
                    -- not busy and not starting anything new
                    -- so disable everything
                    o_nCE <= '1';
                    o_nOE <= '1';
                    o_nWE <= '1';
                    o_nLB <= '1';
                    o_nUB <= '1';
                    io_data <= (others => 'Z');
                end if;
            else
                -- busy -> writing
                -- finish off the write by releasing everything
                o_nCE <= '1';
                o_nOE <= '1';
                o_nWE <= '1';
                o_nLB <= '1';
                o_nUB <= '1';
                io_data <= (others => 'Z');

                busy <= '0';
            end if;
        end if;
    end process;

    o_busy <= busy;

end architecture synth;
