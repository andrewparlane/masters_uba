-- full adder de 1 bit
-- logica desde tablas de verdad y konough maps
library ieee;
use ieee.std_logic_1164.all;

entity fullAdder is
    port (a, b: in  std_logic;
          cIn:  in  std_logic;
          o:    out std_logic;
          cOut: out std_logic);
end entity fullAdder;

architecture synth of fullAdder is
begin
    o <= (a xor b) xor cIn;
    cOut <= (cIn and (a or b)) or (a and b);
end architecture synth;
