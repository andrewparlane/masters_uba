library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity contadorN_tb is
end entity contadorN_tb;

architecture synth of contadorN_tb is
    component contadorN
        generic (WIDTH: natural);
        port (clk:  in  std_logic;
              rst:  in  std_logic;
              q:    out std_logic_vector((WIDTH - 1) downto 0));
    end component contadorN;

    constant WIDTH: natural := 5;

    signal clk: std_logic := '0';
    signal rst: std_logic;
    signal q:   std_logic_vector((WIDTH - 1) downto 0);

    signal errores: integer := 0;
begin

    -- clk period = 100ns
    clk <= not clk after 50 ns;

    dut:    contadorN   generic map (WIDTH => WIDTH)
                        port map (clk => clk,
                                  rst => rst,
                                  q => q);
    -- comprobación
    process
        variable last: unsigned((WIDTH - 1) downto 0) := (others => '0');
        variable expected: unsigned((WIDTH - 1) downto 0);
    begin
        wait for 51 ns;
        forever: loop
            -- calcular que expectamos
            -- expected = rst ? 0 : last+1;
            if (rst = '1') then
                expected := (others => '0');
            else
                expected := last + to_unsigned(1, expected'length);
            end if;

            report "q = " & integer'image(to_integer(unsigned(q)));
            -- porque tenemos asyncronous reset
            -- comprobar que immediamente después del
            -- flanco ascendante del reset, el valor es 0
            loop100: for i in 0 to 99 loop

                if (rst = '1') then
                    expected := (others => '0');
                end if;

                last := unsigned(q);
                assert  (q = std_logic_vector(expected))
                        report "q = " & integer'image(to_integer(unsigned(q))) &
                           " esperado " & integer'image(to_integer(expected))
                        severity error;

                if (q /= std_logic_vector(expected)) then
                    errores <= errores + 1;
                end if;

                wait for 1 ns;

            end loop loop100;
        end loop forever;
    end process;

    -- codigo de preuba
    process
    begin
        rst <= '1';
        wait for 500 ns;

        rst <= '0';
        wait for 5000 ns;

        rst <= '1';
        wait for 500 ns;

        rst <= '0';
        wait for 405 ns;

        rst <= '1';
        wait for 95 ns;

        if (errores /= 0) then
            report "FALLA! con " & integer'image(errores) & " errores";
        else
            report "APROBAR!";
        end if;

        std.env.stop;
    end process;
end architecture synth;
