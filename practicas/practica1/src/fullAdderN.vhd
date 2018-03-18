-- n bit full adder
library IEEE;
use IEEE.STD_LOGIC_1164.all;

entity fullAdderN is
    generic(WIDTH: integer := 8);
    port(A, B:  in  STD_LOGIC_VECTOR((WIDTH - 1) downto 0);
         Cin:   in  STD_LOGIC;
         O:     out STD_LOGIC_VECTOR((WIDTH - 1) downto 0);
         Cout:  out STD_LOGIC);
end entity fullAdderN;

architecture synth of fullAdderN is
    component fullAdder1
        port(A, B:  in  STD_LOGIC;
             Cin:   in  STD_LOGIC;
             O:     out STD_LOGIC;
             Cout:  out STD_LOGIC);
    end component;

    -- Use WIDTH carry signals
    -- and assign Cin to carry(0) and assign carry(WIDTH - 1) to Cout
    signal carry: STD_LOGIC_VECTOR(WIDTH downto 0);
begin
    carry(0) <= Cin;

    genloop: for i in 0 to (WIDTH - 1) generate
        fa1:    fullAdder1 port map(A => A(i),
                                    B => B(i),
                                    Cin => carry(i),
                                    O => O(i),
                                    Cout => carry(i+1));
    end generate genloop;

    Cout <= carry(WIDTH);
end architecture synth;
