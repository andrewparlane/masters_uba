library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.all;
use common.type_pkg.all;

entity adc_tb is
end entity adc_tb;

architecture sim of adc_tb is
    component adc is
        port (clk:          in  std_ulogic;
              rst:          in  std_ulogic;
              dInDiff:      in  std_ulogic;
              dout:         out std_ulogic;
              resultado:    out unsignedArray(2 downto 0)(3 downto 0));
    end component adc;


    signal clk:         std_ulogic := '0';
    signal rst:         std_ulogic := '1';

    signal dInDiff:     std_ulogic := '1';
    signal dOut:        std_ulogic;
    signal resultado:   unsignedArray(2 downto 0)(3 downto 0);

    -- 50 MHz
    constant CLK_HZ:        natural := 50 * 1000 * 1000;
    constant CLK_PERIOD:    time := 1 sec / CLK_HZ;
begin

    clk <= not clk after (CLK_PERIOD/2);

    dut:    adc     port map (clk => clk,
                              rst => rst,
                              dInDiff => dInDiff,
                              dOut => dOut,
                              resultado => resultado);

    -- ---------------
    -- pruebas con PSL
    -- ---------------
    -- psl default clock is rising_edge(clk);
    --
    -- psl preubaRst:
    --      assert always rst -> next resultado = ("0000", "0000", "0000")
    --      report "Failure: reset error";
    --
    -- psl pruebaDOut:
    --      assert always ((now > CLK_PERIOD) ->
    --                     dOut = prev(dInDiff))
    --      report "Failure: DOut error";

    process
    begin
        -- Resultado mámimo debería estar 3.30V
        rst <= '1';
        wait for CLK_PERIOD * 5;
        dInDiff <= '1';
        rst <= '0';
        wait for CLK_PERIOD * 35000;
        assert (resultado = (to_unsigned(3, 4),
                             to_unsigned(3, 4),
                             to_unsigned(0, 4)))
                report "resultado " & natural'image(to_integer(resultado(2))) &
                       "." & natural'image(to_integer(resultado(1))) &
                             natural'image(to_integer(resultado(0))) &
                       "V esperando 3.30V";

        -- si dInDiff siempre es cero el resultado debería
        -- estar 0.00V
        rst <= '1';
        wait for CLK_PERIOD * 5;
        dInDiff <= '0';
        rst <= '0';
        wait for CLK_PERIOD * 35000;
        assert (resultado = (to_unsigned(0, 4),
                             to_unsigned(0, 4),
                             to_unsigned(0, 4)))
                report "resultado " & natural'image(to_integer(resultado(2))) &
                       "." & natural'image(to_integer(resultado(1))) &
                             natural'image(to_integer(resultado(0))) &
                       "V esperando 0.00V";

        -- Probamos 1.65V
        rst <= '1';
        wait for CLK_PERIOD * 5;
        dInDiff <= '1';
        rst <= '0';
        wait for CLK_PERIOD * 16500;
        dInDiff <= '0';
        wait for CLK_PERIOD * 17000;
        assert (resultado = (to_unsigned(1, 4),
                             to_unsigned(6, 4),
                             to_unsigned(5, 4)))
                report "resultado " & natural'image(to_integer(resultado(2))) &
                       "." & natural'image(to_integer(resultado(1))) &
                             natural'image(to_integer(resultado(0))) &
                       "V esperando 1.65V";

        -- Y 2.01V
        rst <= '1';
        wait for CLK_PERIOD * 5;
        dInDiff <= '1';
        rst <= '0';
        wait for CLK_PERIOD * 20100;
        dInDiff <= '0';
        wait for CLK_PERIOD * 15000;
        assert (resultado = (to_unsigned(2, 4),
                             to_unsigned(0, 4),
                             to_unsigned(1, 4)))
                report "resultado " & natural'image(to_integer(resultado(2))) &
                       "." & natural'image(to_integer(resultado(1))) &
                             natural'image(to_integer(resultado(0))) &
                       "V esperando 2.01V";

        -- probamos con dInDiff alto 1 tick de cada 4
        rst <= '1';
        wait for CLK_PERIOD * 5;
        rst <= '0';
        for i in 0 to 9000 loop
            dInDiff <= '1';
            wait for CLK_PERIOD;
            dInDiff <= '0';
            wait for CLK_PERIOD * 3;
        end loop;
        assert (resultado = (to_unsigned(0, 4),
                             to_unsigned(8, 4),
                             to_unsigned(2, 4)))
                report "resultado " & natural'image(to_integer(resultado(2))) &
                       "." & natural'image(to_integer(resultado(1))) &
                             natural'image(to_integer(resultado(0))) &
                       "V esperando 0.82V";

        std.env.stop;
    end process;

end architecture sim;
