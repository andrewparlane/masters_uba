-- full adder de 1 bit
library IEEE;
use IEEE.std_logic_1164.all;

entity fullAdder1 is
    port (A, B: in  std_logic;
          Cin:  in  std_logic;
          O:    out std_logic;
          Cout: out std_logic);
end entity fullAdder1;

architecture synth of fullAdder1 is
begin
    O <= (A xor B) xor Cin;
    Cout <= (Cin and (A or B)) or (A and B);
end architecture synth;
