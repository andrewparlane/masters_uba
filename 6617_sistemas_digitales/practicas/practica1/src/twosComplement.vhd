-- La resulta es el 2's complement del input
library ieee;
use ieee.std_logic_1164.all;

entity twosComplement is
    generic (WIDTH: integer := 8);
    port (a: in  std_ulogic_vector((WIDTH - 1) downto 0);
          o: out std_ulogic_vector((WIDTH - 1) downto 0));
end entity twosComplement;

architecture synth of twosComplement is
    component rippleAdder
        generic(WIDTH: integer := 8);
        port(a, b:  in  std_ulogic_vector((WIDTH - 1) downto 0);
             cIn:   in  std_ulogic;
             o:     out std_ulogic_vector((WIDTH - 1) downto 0);
             cOut:  out std_ulogic);
    end component rippleAdder;

    signal notA: std_ulogic_vector((WIDTH - 1) downto 0);
    signal zero: std_ulogic_vector((WIDTH - 1) downto 0);
begin

    notA <= not A;
    zero <= (others => '0');

    add:    rippleAdder  generic map (WIDTH => WIDTH)
                         port map    (a => notA,
                                      b => zero,
                                      cIn => '1',
                                      o => o); -- ignoramos cOut

end architecture synth;