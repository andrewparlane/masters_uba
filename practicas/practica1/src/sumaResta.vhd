-- o = (op = suma) ? (a + b) : (a - b)
-- Nota: a, b, o están unsigned.
library ieee;
use ieee.std_logic_1164.all;

package suma_resta_package is
    type sumaRestaOP is (SUMA, RESTA);
end suma_resta_package;

package body suma_resta_package is
end package body suma_resta_package;

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.suma_resta_package.all;

entity sumaResta is
    generic(WIDTH: integer := 8);
    port(a, b:  in  std_logic_vector((WIDTH - 1) downto 0);
         op:    in  sumaRestaOP;
         o:     out std_logic_vector((WIDTH - 1) downto 0);
         cOut:  out std_logic);
end entity sumaResta;

architecture synth of sumaResta is
    component rippleAdder
        generic (WIDTH: integer);
        port(a, b:  in  std_logic_vector((WIDTH - 1) downto 0);
             cIn:   in  std_logic;
             o:     out std_logic_vector((WIDTH - 1) downto 0);
             cOut:  out std_logic);
    end component;

    component twosComplement
        generic (WIDTH: integer := 8);
        port (a: in  std_logic_vector((WIDTH - 1) downto 0);
              o: out std_logic_vector((WIDTH - 1) downto 0));
    end component twosComplement;

    -- usamos WIDTH+1 bits con el bit más significante por el signo
    signal auxA:                std_logic_vector(WIDTH downto 0);
    signal auxB:                std_logic_vector(WIDTH downto 0);
    signal twosComplementAuxB:  std_logic_vector(WIDTH downto 0);
    signal segundoArgumento:    std_logic_vector(WIDTH downto 0);
    signal auxO:                std_logic_vector(WIDTH downto 0);
begin

    auxA <= std_logic_vector(resize(unsigned(a), auxA'length));
    auxB <= std_logic_vector(resize(unsigned(b), auxB'length));

    -- el segundo argumento está auxB o twosComplementAuxB
    segundoArgumento <= auxB when (OP = SUMA) else twosComplementAuxB;

    -- obtenemos el twosComplement de B
    twos:   twosComplement  generic map (WIDTH => (WIDTH + 1))
                            port map    (a => auxB,
                                         o => twosComplementAuxB);

    add:    rippleAdder     generic map (WIDTH => (WIDTH + 1))
                            port map    (a => auxA,
                                         b => segundoArgumento,
                                         cIn => '0',
                                         o => auxO); --ignoramos cOut

    o <= auxO((WIDTH - 1) downto 0);
    cOut <= auxO(WIDTH);

end architecture synth;
