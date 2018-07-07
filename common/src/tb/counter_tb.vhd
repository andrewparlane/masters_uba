library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity counter_tb is
end entity counter_tb;

architecture sim of counter_tb is

    component counter is
        generic (WIDTH: natural;
                 MAX: natural);
        port (clk:      in  std_ulogic;
              en:       in  std_ulogic;
              rst:      in  std_ulogic;
              load:     in  std_ulogic;
              loadData: in  unsigned((WIDTH - 1) downto 0);
              count:    out unsigned((WIDTH - 1) downto 0);
              atZero:   out std_ulogic;
              atMax:    out std_ulogic);
    end component counter;

    constant WIDTH: natural := 4;
    constant MAX: natural := 9;

    -- dut señales
    signal clk:         std_ulogic := '0';
    signal rst:         std_ulogic := '1';
    signal en:          std_ulogic := '0';
    signal load:        std_ulogic := '0';
    signal loadData:    unsigned((WIDTH - 1) downto 0) := (others => '0');
    signal count:       unsigned((WIDTH - 1) downto 0);
    signal atZero:      std_ulogic;
    signal atMax:       std_ulogic;

begin

    -- clk period = 100ns
    clk <= not clk after 50 ns;

    dut: counter    generic map    (WIDTH => WIDTH,
                                    MAX => MAX)
                    port map       (clk => clk,
                                    rst => rst,
                                    en => en,
                                    load => load,
                                    loadData => loadData,
                                    count => count,
                                    atZero => atZero,
                                    atMax => atMax);

    --process (count)
    --begin
    --    report "count changed to " & integer'image(to_integer(count));
    --end process;

    -- pruebas con PSL
    -- ---------------
    -- psl default clock is rising_edge(clk);
    --
    -- psl preubaRst:
    --      assert always rst -> next count = 0
    --      report "Failure: reset error";
    --
    -- psl preubaLoad:
    --      assert always (en and load) -> next count = loadData
    --      report "Failure: load error";
    --
    -- psl preubaCero:
    --      assert always (count = 0) -> atZero
    --      report "Failure: atZero error - atZero not set when it should be";
    --
    -- psl preubaNCero:
    --      assert always (count /= 0) -> not atZero
    --      report "Failure: atZero error - atZero set when it shouldn't be";
    --
    -- psl preubaMax:
    --      assert always (count = MAX) -> atMax
    --      report "Failure: atMax error - atMax not set when it should be";
    --
    -- psl preubaNMax:
    --      assert always (count /= MAX) -> not atMax
    --      report "Failure: atMax error - atMax set when it shouldn't be";
    --
    -- psl preubaCount:
    --      assert forall i in {0 to (MAX - 1)}:
    --          always ((count = i) and
    --                  (rst = '0') and
    --                  (load = '0') and
    --                  (en = '1'))
    --          -> next ((count = i + 1) or
    --                   (rst = '1') or
    --                   (load = '1'))
    --      report "Failure: counter error - didn't increment";
    --
    -- psl preubaCountOverflow:
    --      assert always ((count = MAX) and
    --                     (rst = '0') and
    --                     (load = '0') and
    --                     (en = '1'))
    --             -> next count = 0
    --      report "Failure: counter error - didn't overflow";
    --
    -- psl preubaEn:
    --      assert forall i in {0 to (MAX - 1)}:
    --          always ((count = i) and
    --                  (rst = '0') and
    --                  (en = '0'))
    --          -> next ((count = i) or
    --                   (rst = '1'))
    --      report "Failure: counter error - changed when en and rst were 0";

    process
    begin
        report "Comprobamos que o es 0 siempre cuándo estámos en reset";
        rst <= '1';
        en <= '0';
        wait for 500 ns;

        report "aun si en es 1";
        en <= '1';
        wait for 500 ns;

        report "contando cada tick";
        rst <= '0';
        wait for 3500 ns;

        report "se queda a loadData cuando load es alto";
        loadData <= to_unsigned(4, WIDTH);
        load <= '1';
        wait for 500 ns;

        report "y comenza desde load cuando load baja";
        load <= '0';
        wait for 1000 ns;

        report "nada pasa si load es alto hasta en es alto";
        load <= '1';
        en <= '0';
        wait for 500 ns;
        en <= '1';
        wait for 500 ns;
        load <= '0';
        wait for 500 ns;

        report "en sólo alto una vez cada 10 ticks";
        rst <= '1';
        wait for 100 ns;
        rst <= '0';
        for i in 0 to 40 loop
            en <= '0';
            wait for 900 ns;
            en <= '1';
            wait for 100 ns;
        end loop;

        std.env.stop;
    end process;

end architecture sim;
