-- n bit ripple adder
-- hecho con n unidades de fullAdder
library ieee;
use ieee.std_logic_1164.all;

entity rippleAdderN is
    generic(WIDTH: integer := 8);
    port(a, b:  in  std_logic_vector((width - 1) downto 0);
         cIn:   in  std_logic;
         o:     out std_logic_vector((width - 1) downto 0);
         cOut:  out std_logic);
end entity rippleAdderN;

architecture synth of rippleAdderN is
    component fullAdder
        port(a, b:  in  std_logic;
             cIn:   in  std_logic;
             o:     out std_logic;
             cOut:  out std_logic);
    end component;

    -- usamos WIDTH señales de carry
    -- y asignamos cIn a carry(0)
    -- y asignamos carry(WIDTH) a cOut
    -- los otros conectan al siguiente cIn
    signal carry: std_logic_vector(WIDTH downto 0);
begin
    carry(0) <= Cin;

    genloop: for i in 0 to (WIDTH - 1) generate
        fa:     fullAdder  port map(A => A(i),
                                    B => B(i),
                                    cIn => carry(i),
                                    O => O(i),
                                    cOut => carry(i+1));
    end generate genloop;

    cOut <= carry(WIDTH);
end architecture synth;
