library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.fp_rounding_pkg.all;

entity fp_mult is
    generic (TOTAL_BITS:    natural;
             EXPONENT_BITS: natural);
    port (inA:  in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          inB:  in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          roundingMode: RoundingMode;
          outC: out std_ulogic_vector((TOTAL_BITS - 1) downto 0));
end entity fp_mult;

architecture synth of fp_mult is
    package fpPkg
            is new work.fp_helper_pkg
            generic map (TOTAL_BITS => TOTAL_BITS,
                         EXPONENT_BITS => EXPONENT_BITS);

    constant SIGNIFICAND_BITS:  natural := fpPkg.SIGNIFICAND_BITS;
    constant MANTISSA_BITS:     natural := SIGNIFICAND_BITS + 1;
    constant PRODUCT_BITS:      natural := MANTISSA_BITS * 2;

    signal fpA:    fpPkg.fpType;
    signal fpB:    fpPkg.fpType;
    signal fpC:    fpPkg.fpType;


    -- EXPONENT_BITS + 1 so we have the carry out bit
    -- we calculate both biased(e1 + e2) and biased(e1 + e2) + 1
    -- then select the correct one based on msbOfProduct
    signal newBiasedExponent:           unsigned((EXPONENT_BITS + 1) downto 0);
    signal sumOfBiasedExponents:        unsigned((EXPONENT_BITS + 1) downto 0);
    signal sumOfBiasedExponentsPlus1:   unsigned((EXPONENT_BITS + 1) downto 0);
    signal useExponentPlus1:            std_ulogic;

    -- The product of the two mantissas
    -- 1.significandA * 1.significandB
    signal product:                     unsigned((PRODUCT_BITS - 1) downto 0);
    signal msbOfProduct:                std_ulogic;

    -- The new significand depends on the msb of the product
    signal mantissaForMsb0:             unsigned((MANTISSA_BITS - 1) downto 0);
    signal mantissaForMsb1:             unsigned((MANTISSA_BITS - 1) downto 0);
    signal mantissaBeforeRounding:      unsigned(MANTISSA_BITS downto 0);
    signal mantissaBeforeRoundingPlus1: unsigned(MANTISSA_BITS downto 0);
    signal mantissaAfterRounding:       unsigned(MANTISSA_BITS downto 0);
    signal finalMantissa:               unsigned((MANTISSA_BITS - 1) downto 0);

    signal useMantissaPlus1:            std_ulogic;

    -- rounding bits
    -- r - is the MSb after the mantissa
    -- s - is the or of all subsequent bits
    -- Since the offset of the new significand into product
    -- varies, r and s differ too
    signal rForMsb0:                    std_ulogic;
    signal rForMsb1:                    std_ulogic;
    signal r:                           std_ulogic;
    signal sForMsb0:                    std_ulogic;
    signal sForMsb1:                    std_ulogic;
    signal s:                           std_ulogic;

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
    -- or the MSB of the mantisaa after rounding is 1 then
    -- we need to add 1 to the sum of the exponents
    sumOfBiasedExponentsPlus1 <= sumOfBiasedExponents +
                                 to_unsigned(1, EXPONENT_BITS + 2);

    -- Pick the correct exponent to use
    newBiasedExponent <= sumOfBiasedExponents
                         when (useExponentPlus1 = '0')
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
    msbOfProduct <= product(PRODUCT_BITS - 1);

    -- If the MSb is 1 then we have:
    -- 1x.xxxxxx but we require the mantissa to be
    -- 1.xxxxxx so we need to divide the mantissa by 2
    -- and add one to the exponent.
    -- This means that the new mantissa is the top MANTISSA_BITS
    -- of product, r is the next bit
    -- and s is the or of all lower bits
    mantissaForMsb1 <= product((PRODUCT_BITS - 1) downto (SIGNIFICAND_BITS + 1));

    rForMsb1 <= product(SIGNIFICAND_BITS);
    sForMsb1 <= '1' when (product((SIGNIFICAND_BITS - 1) downto 0) /= to_unsigned(0, SIGNIFICAND_BITS))
                else '0';

    -- If the MSb is 0 then we have:
    -- 01.xxxxxx which is what we require. so just drop the msb
    -- This means that we ignore the msb, the new mantissa
    -- is the next MANTISSA_BITS, r is the next bit
    -- and s is the or of all lower bits
    mantissaForMsb0 <= product((PRODUCT_BITS - 2) downto SIGNIFICAND_BITS);
    rForMsb0 <= product(SIGNIFICAND_BITS - 1);
    sForMsb0 <= '1' when (product((SIGNIFICAND_BITS - 2) downto 0) /= to_unsigned(0, SIGNIFICAND_BITS - 1))
                else '0';

    -- Pick the correct mantissa, r and s
    mantissaBeforeRounding <= '0' & mantissaForMsb0
                              when (msbOfProduct = '0')
                              else '0' & mantissaForMsb1;

    r <= rForMsb0
         when (msbOfProduct = '0')
         else rForMsb1;

    s <= sForMsb0
         when (msbOfProduct = '0')
         else sForMsb1;

    -- rounding:
    -- If we support rounding then it's possible we'll need to
    -- add 1 to the mantissa.

    mantissaBeforeRoundingPlus1 <= mantissaForMsb1 +
                                   to_unsigned(1, MANTISSA_BITS + 1);


    -- 4 cases:
    -- 1) round towards negative infinity
    --      -11.1 -> -12.0, 11.9 -> 11.0
    -- 2) round towards positive infinity
    --      -11.9 -> -11.0, 11.1 -> 12.0
    -- 3) round towards 0
    --      -11.9 -> -11.0, 11.9 -> 11.0
    -- 4) round to nearest (ties to even)
    --      -11.9 -> -12.0, -11.1 -> -11.0
    --       11.9 ->  12.0,  11.1 ->  11.0
    --       11.5 ->  12.0,  12.5 ->  12.0

    process (all)
    begin
        if (roundingMode = RoundingMode_NEG_INF) then
            -- Only add one if we are negative and (r or s)
            useMantissaPlus1 <= newSign and (r or s);
        elsif (roundingMode = RoundingMode_POS_INF) then
            -- Only add one if we are positive and (r or s)
            useMantissaPlus1 <= (not newSign) and (r or s);
        elsif (roundingMode = RoundingMode_0) then
            -- never add one
            useMantissaPlus1 <= '0';
        else --if (roundingMode = RoundingMode_NEAREST) then
            -- we add one if we are greater than halfway (r and s)
            -- in the half way case (r and (not s)) we tie to even
            -- so add 1 if the lsb of the mantissa is 1 (odd)
            -- so: (r and s) or (r and (not s) and mantissa(0))
            useMantissaPlus1 <= (r and s) or (r and mantissaBeforeRounding(0));
        end if;
    end process;

    mantissaAfterRounding <= mantissaBeforeRoundingPlus1
                             when (useMantissaPlus1)
                             else mantissaBeforeRounding;

    -- now if that overflowed we need to divide by two
    -- and add 1 to the exponent.
    -- note it's impossible for both the product to be 1x.xxx
    -- and the rounded mantissa to be 1x.. because we can't get
    -- 11.1111 from multiplying two numbers.
    -- max is 1.11 * 1.11 = 1.75 * 1.75 = 3.0625 = 11.0001
    finalMantissa <= mantissaAfterRounding(MANTISSA_BITS downto 1)
                     when (mantissaAfterRounding(MANTISSA_BITS) = '1')
                     else mantissaAfterRounding((MANTISSA_BITS - 1) downto 0);

    useExponentPlus1 <= msbOfProduct or mantissaAfterRounding(MANTISSA_BITS);

    -- The new sign is the XOR of the signs of the arguments
    newSign <= fpA.sign xor fpB.sign;

    -- handle the special cases
    -- If either of the arguments is NaN the output should be NaN
    -- 0 * infinity is NaN
    -- If we overflow we should be infinity
    -- if we underflow we should be 0
    --   note: we don't support denormals yet
    process (all)
    begin
        if (fpPkg.is_NaN(fpA) or
            fpPkg.is_NaN(fpB) or
            (fpPkg.is_zero(fpA) and fpPkg.is_infinity(fpB)) or
            (fpPkg.is_zero(fpB) and fpPkg.is_infinity(fpA))) then
            fpC <= fpPkg.set_NaN(newSign);
        elsif ((overflow = '1') or
               (newBiasedExponent = to_unsigned(fpPkg.EMAX + 1, EXPONENT_BITS+2)) or
               fpPkg.is_infinity(fpA) or
               fpPkg.is_infinity(fpB)) then
            fpC <= fpPkg.set_infinity(newSign);
        elsif ((underflow = '1') or
               newBiasedExponent = to_unsigned(fpPkg.EMIN - 1, EXPONENT_BITS+2)) then
            fpC <= fpPkg.set_zero(newSign);
        else
            fpC.sign <= newSign;
            fpC.biasedExponent <= std_ulogic_vector(newBiasedExponent((EXPONENT_BITS - 1) downto 0));
            fpC.significand <= std_ulogic_vector(finalMantissa((SIGNIFICAND_BITS - 1) downto 0));
            fpC.representation <= fpPkg.fpRepresentation_NORMAL;
        end if;
    end process;

end architecture synth;
