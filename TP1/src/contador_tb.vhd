library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity contador_tb is
end entity contador_tb;

architecture sim of contador_tb is

    component contador is
        generic (WIDTH: natural;
                 MAX: natural);
        port (clk:      in  std_logic;
              en:       in  std_logic;
              rst:      in  std_logic;
              load:     in  std_logic;
              loadData: in  unsigned((WIDTH - 1) downto 0);
              count:    out unsigned((WIDTH - 1) downto 0);
              atMax:    out std_logic);
    end component contador;

    constant WIDTH: natural := 4;
    constant MAX: natural := 9;

    -- dut señales
    signal clk:         std_logic := '0';
    signal rst:         std_logic := '1';
    signal en:          std_logic := '0';
    signal load:        std_logic := '0';
    signal loadData:    unsigned((WIDTH - 1) downto 0) := (others => '0');
    signal count:       unsigned((WIDTH - 1) downto 0);
    signal atMax:       std_logic;

begin

    -- clk period = 100ns
    clk <= not clk after 50 ns;

    dut: contador   generic map    (WIDTH => WIDTH,
                                    MAX => MAX)
                    port map       (clk => clk,
                                    rst => rst,
                                    en => en,
                                    load => load,
                                    loadData => loadData,
                                    count => count,
                                    atMax => atMax);

    process (count)
    begin
        report "count changed to " & integer'image(to_integer(count));
    end process;

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
