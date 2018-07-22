library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.type_pkg.all;

entity tp1_tb is
end entity tp1_tb;

architecture sim of tp1_tb is

    component tp1 is
        generic (CLOCK_DIVIDER:  natural);
        port (CLOCK_50: in  std_ulogic;
              KEY:      in  std_ulogic_vector(1 downto 0);
              HEX0:     out std_ulogic_vector(6 downto 0);
              HEX1:     out std_ulogic_vector(6 downto 0);
              HEX2:     out std_ulogic_vector(6 downto 0);
              HEX3:     out std_ulogic_vector(6 downto 0));
    end component tp1;

    signal clk:         std_ulogic   := '0';
    signal nRst:        std_ulogic   := '0';
    signal nFast:       std_ulogic   := '1';
    signal key:         std_ulogic_vector(1 downto 0) := "00";

    -- usamos esto por los outputs de los contadores
    signal counts: unsignedArray(3 downto 0)(3 downto 0);

begin

    -- clk = 50MHz => periodo = 20ns
    clk <= not clk after 10 ns;

    -- key
    key <= nFast & nRst;

    dut:    tp1 generic map    (CLOCK_DIVIDER => 10000)   -- incrementar el primer dígito cada 5000 ticks
                port map       (CLOCK_50 => clk,
                                KEY => key);

    -- leer las salidas de las contadores en tp1.
    counts <= <<signal dut.bcdOut: unsignedArray(3 downto 0)(3 downto 0)>>;

    -- pruebas con PSL
    -- ---------------
    -- psl default clock is rising_edge(clk);
    --
    enRstGenerate: for c in 0 to 3 generate
        type ticksEntreCambioArray is array (0 to 3) of natural;
        constant fastTicksEntreCambio: ticksEntreCambioArray
                                    := (5, 50, 500, 5000);
        constant normalTicksEntreCambio: ticksEntreCambioArray
                                    := (5000, 50000, 500000, 5000000);
    begin
        -- ----------------------------------------------------------
        -- si estamos en rst todo los counts debería estar 0
        -- ----------------------------------------------------------
        -- psl enRst:
        --      assert always (nRst = '0') ->
        --                    (counts(c) = 0)
        --      report "Error: counts(c) != 0 cuando en reset";
        -- ----------------------------------------------------------
        --
        -- ----------------------------------------------------------
        -- en modo rápido cada fastTicksEntreCambio(c) counts(c)
        -- deberia incrementar
        -- ----------------------------------------------------------
        -- psl fastCount:
        --      assert forall i in {0 to 8}:
        --          always ((counts(c) = i) and
        --                  (nFast = '0') and
        --                  (nRst = '1'))
        --          -> next[fastTicksEntreCambio(c)]
        --             (counts(c) = i + 1)
        --             abort ((nRst = '0') or
        --                    (nFast = '1'))
        --      report "Error: counts(c) modo rápido no cuenta correcto";
        -- ----------------------------------------------------------
        --
        -- ----------------------------------------------------------
        -- en modo rápido si counts(c) es 9, en
        -- fastTicksEntreCambio(c) ticks count(c)
        -- debería estar 0
        -- ----------------------------------------------------------
        -- psl fastOverflow:
        --      assert always ((counts(c) = 9) and
        --                     (nFast = '0') and
        --                     (nRst = '1'))
        --             -> next[fastTicksEntreCambio(c)]
        --                (counts(c) = 0)
        --                abort ((nRst = '0') or
        --                       (nFast = '1'))
        --      report "Error: counts(c) modo rápido no hizo overflow";
        -- ----------------------------------------------------------
        --
        -- ----------------------------------------------------------
        -- en modo normal cada normalTicksEntreCambio(c) counts(c)
        -- deberia incrementar
        -- ----------------------------------------------------------
        -- psl normalCount:
        --      assert forall i in {0 to 8}:
        --          always ((counts(c) = i) and
        --                  (nFast = '1') and
        --                  (nRst = '1'))
        --          -> next[normalTicksEntreCambio(c)]
        --             (counts(c) = i + 1)
        --             abort ((nRst = '0') or
        --                    (nFast = '0'))
        --      report "Error: counts(c) modo normal no cuenta correcto";
        -- ----------------------------------------------------------
        --
        -- ----------------------------------------------------------
        -- en modo rápido si counts(c) es 9, en
        -- fastTicksEntreCambio(c) ticks count(c)
        -- debería estar 0
        -- ----------------------------------------------------------
        -- psl normalOverflow:
        --      assert always ((counts(c) = 9) and
        --                     (nFast = '1') and
        --                     (nRst = '1'))
        --             -> next[normalTicksEntreCambio(c)]
        --                (counts(c) = 0)
        --                abort ((nRst = '0') or
        --                       (nFast = '0'))
        --      report "Error: counts(c) modo normal no hizo overflow";
        -- ----------------------------------------------------------
    end generate;

    process
    begin
        -- recuerdes que los keys son activa baja
        -- reset
        nRst <= '0';
        wait for 100 ns;

        -- no es suficiente a overflow 9999 -> 0000
        -- pero es bastante para mostrar que funciona bien
        -- en modo normal. Y podríamos comprobar los dígitos
        -- altos y el overflow en modo rapido
        -- 10 * 5,000 ticks * 20ns = 1ms
        nRst <= '1';
        nFast <= '1';
        wait for 1100 us;

        -- hacemos una prueba más completo en modo rápido
        -- 10,000 * 5 tics * 20ns = 1ms
        nFast <= '0';
        wait for 1100 us;

        std.env.stop;
    end process;

end architecture sim;
