library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

entity fp_mult is
    generic (TOTAL_BITS:    natural;
             EXPONENT_BITS: natural);
    port (inA:  in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          inB:  in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          outC: out std_ulogic_vector((TOTAL_BITS - 1) downto 0));
end entity fp_mult;

architecture synth of fp_mult is
    package fpPkg
            is new work.fp_helper_pkg
            generic map (TOTAL_BITS => TOTAL_BITS,
                         EXPONENT_BITS => EXPONENT_BITS);

    constant SIGNIFICAND_BITS_IN_PRODUCT: natural
             := ((fpPkg.SIGNIFICAND_BITS + 1) * 2);

    signal fpA:    fpPkg.fpType;
    signal fpB:    fpPkg.fpType;
    signal fpC:    fpPkg.fpType;


    -- EXPONENT_BITS + 1 so we have the carry out bit
    -- we calculate both biased(e1 + e2) and biased(e1 + e2) + 1
    -- then select the correct one based on msbOfProduct
    signal newBiasedExponent:           unsigned((EXPONENT_BITS + 1) downto 0);
    signal sumOfBiasedExponents:        unsigned((EXPONENT_BITS + 1) downto 0);
    signal sumOfBiasedExponentsPlus1:   unsigned((EXPONENT_BITS + 1) downto 0);

    -- The product of the two mantissas
    -- 1.significandA * 1.significandB
    signal product:                     unsigned((SIGNIFICAND_BITS_IN_PRODUCT - 1) downto 0);
    signal msbOfProduct:                std_ulogic;

    -- The new significand depends on the msb of the product
    signal newSignificand:              unsigned((fpPkg.SIGNIFICAND_BITS - 1) downto 0);
    signal newSignificandForMsb0:       unsigned((fpPkg.SIGNIFICAND_BITS - 1) downto 0);
    signal newSignificandForMsb1:       unsigned((fpPkg.SIGNIFICAND_BITS - 1) downto 0);

    -- the new sign depends on the signs of the arguments
    signal newSign:                     std_ulogic;

    -- Flags
    signal overflow:                    std_ulogic;
    signal underflow:                   std_ulogic;
begin

    -- Convert A and B to fpTypes
    fpA <= fpPkg.vect_to_fpType(inA);
    fpB <= fpPkg.vect_to_fpType(inB);

    -- Convert the result to a vector
    outC <= fpPkg.fpType_to_vect(fpC);

    -- Get the new exponent
    -- biased(e1 + e2) = biased(e1) + biased(e2) - BIAS
    -- prepend 00 to all arguments to catch
    -- overflows:
    --   for EXPONENT_BITS = 8
    --   255 + 255 - 127 + 1 is the biggest value for
    --   that we can get = 384 = 01 0111 1110
    -- underflows:
    --   for EXPONENT_BITS = 8
    --   0 + 0 - 127 is the smallest value we can get
    --   = 11 1000 0001
    -- so the Msb represents underflow, and the xor of the
    -- top two bits is overflow
    sumOfBiasedExponents <= (("00" & unsigned(fpA.biasedExponent)) +
                             ("00" & unsigned(fpB.biasedExponent))) -
                            ("00" & to_unsigned(fpPkg.BIAS, EXPONENT_BITS));

    -- If the MSb of the product of the mantissas is 1
    -- we need to add 1 to the sum of the exponents
    sumOfBiasedExponentsPlus1 <= sumOfBiasedExponents +
                                 to_unsigned(1, EXPONENT_BITS + 2);

    -- Pick the correct exponent to use based on
    -- the MSb of the product of the mantissas
    newBiasedExponent <= sumOfBiasedExponents
                         when (msbOfProduct = '0')
                         else sumOfBiasedExponentsPlus1;

    -- check if we overflowed or underflowed
    overflow <= newBiasedExponent(EXPONENT_BITS) xor
                newBiasedExponent(EXPONENT_BITS+1);
    underflow <= newBiasedExponent(EXPONENT_BITS+1);

    -- multiply the mantissas (includes the implicit "1.")
    -- This gives us 2 bits of integer +
    -- SIGNIFICAND_BITS*2 bits of fractional
    product <= ('1' & unsigned(fpA.significand)) *
               ('1' & unsigned(fpB.significand));

    -- Get the MSb of the product.
    msbOfProduct <= product(SIGNIFICAND_BITS_IN_PRODUCT-1);

    -- If the MSb is 1 we use the upper SIGNIFICAND_BITS of the
    -- fractional part of the product.
    newSignificandForMsb1 <= product((SIGNIFICAND_BITS_IN_PRODUCT - 2) downto (fpPkg.SIGNIFICAND_BITS + 1));

    -- If the MSb is 0 we drop the upper bit of the fractional
    -- part of the product and use the next SIGNIFICAND_BITS
    newSignificandForMsb0 <= product((SIGNIFICAND_BITS_IN_PRODUCT - 3) downto fpPkg.SIGNIFICAND_BITS);

    -- Pick the correct significand
    newSignificand <= newSignificandForMsb0
                      when (msbOfProduct = '0')
                      else newSignificandForMsb1;

    -- The new sign is the XOR of the signs of the arguments
    newSign <= fpA.sign xor fpB.sign;

    -- handle the special cases
    -- If either of the arguments is NaN the output should be NaN
    -- If we overflow we should be infinity
    -- if we underflow we should be 0
    --   note: we don't support denormals yet
    process (all)
    begin
        if (fpPkg.is_NaN(fpA) or
            fpPkg.is_NaN(fpB)) then
            fpC <= fpPkg.set_NaN(newSign);
        elsif ((overflow = '1') or
               newBiasedExponent = to_unsigned(fpPkg.EMAX + 1, EXPONENT_BITS+2)) then
            fpC <= fpPkg.set_infinity(newSign);
        elsif ((underflow = '1') or
               newBiasedExponent = to_unsigned(fpPkg.EMIN - 1, EXPONENT_BITS+2)) then
            fpC <= fpPkg.set_zero(newSign);
        else
            fpC.sign <= newSign;
            fpC.biasedExponent <= std_ulogic_vector(newBiasedExponent((EXPONENT_BITS - 1) downto 0));
            fpC.significand <= std_ulogic_vector(newSignificand);
            fpC.representation <= fpPkg.fpRepresentation_NORMAL;
        end if;
    end process;

end architecture synth;
