library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.fp_rounding_pkg.all;

entity fp_mult is
    generic (TOTAL_BITS:    natural;
             EXPONENT_BITS: natural);
    port (inA:          in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          inB:          in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          roundingMode: in  RoundingMode;
          outC:         out std_ulogic_vector((TOTAL_BITS - 1) downto 0));
end entity fp_mult;

architecture synth of fp_mult is
    package fpPkg
            is new work.fp_helper_pkg
            generic map (TOTAL_BITS => TOTAL_BITS,
                         EXPONENT_BITS => EXPONENT_BITS);

    constant SIGNIFICAND_BITS:  natural := fpPkg.SIGNIFICAND_BITS;
    constant PRODUCT_BITS:      natural := SIGNIFICAND_BITS * 2;

    signal fpA:    fpPkg.fpUnpacked;
    signal fpB:    fpPkg.fpUnpacked;
    signal fpC:    fpPkg.fpUnpacked;


    -- EXPONENT_BITS + 1 so we have the carry out bit
    -- we calculate both biased(e1 + e2) and biased(e1 + e2) + 1
    -- then select the correct one based on msbOfProduct
    signal newBiasedExponent:           signed((EXPONENT_BITS + 1) downto 0);

    -- The product of the two mantissas
    -- 1.significandA * 1.significandB
    signal product:                     unsigned((PRODUCT_BITS - 1) downto 0);
    signal msbOfProduct:                std_ulogic;

    -- The new significand depends on the msb of the product
    -- We use SIGNIFICAND_BITS + 1 for the mantissaAfterRounding
    -- so that we can catch overflow
    signal mantissaBeforeRounding:      unsigned((SIGNIFICAND_BITS - 1) downto 0);
    signal mantissaAfterRounding:       unsigned(SIGNIFICAND_BITS downto 0);
    signal finalMantissa:               unsigned((SIGNIFICAND_BITS - 1) downto 0);

    -- rounding bits
    -- r - is the MSb after the mantissa
    -- s - is the reduction or of all subsequent bits
    signal r:                           std_ulogic;
    signal s:                           std_ulogic;

    -- the new sign depends on the signs of the arguments
    signal newSign:                     std_ulogic;

    -- Flags
    signal overflow:                    boolean;
    signal underflow:                   boolean;
begin

    -----------------------------------------------------------------
    -- Type conversions
    -----------------------------------------------------------------

    -- Convert A and B to fpUnpackeds
    fpA <= fpPkg.unpack(inA);
    fpB <= fpPkg.unpack(inB);

    -- Convert the result to a vector
    outC <= fpPkg.pack(fpC);

    -----------------------------------------------------------------
    -- Add the exponents
    -----------------------------------------------------------------
    process (all)
        -- biased(e1 + e2) = biased(e1) + biased(e2) - BIAS
        -- prepend 00 to all arguments to catch
        -- overflows and underflows.
        --   newBiasedExponent < EMIN -> underflow
        --   newBiasedExponent > EMAX -> overflow
        variable sumOfBiasedExponents: signed((EXPONENT_BITS + 1) downto 0);
    begin
        sumOfBiasedExponents := (("00" & signed(fpA.biasedExponent)) +
                                 ("00" & signed(fpB.biasedExponent))) -
                                (to_signed(fpPkg.BIAS, EXPONENT_BITS + 2));

        -- If the MSb of the product of the mantissas is 1
        -- or the MSB of the mantisaa after rounding is 1 then
        -- we need to add 1 to the sum of the exponents
        if ((msbOfProduct = '1') or
            (mantissaAfterRounding(SIGNIFICAND_BITS) = '1')) then
            newBiasedExponent <= sumOfBiasedExponents +
                                 to_signed(1, EXPONENT_BITS + 2);
        else
            newBiasedExponent <= sumOfBiasedExponents;
        end if;

        -- check if we overflowed or underflowed
        underflow <= (newBiasedExponent < to_signed(fpPkg.EMIN, EXPONENT_BITS + 2));
        overflow  <= (newBiasedExponent > to_signed(fpPkg.EMAX, EXPONENT_BITS + 2));
    end process;

    -----------------------------------------------------------------
    -- Multiply the mantissas
    -----------------------------------------------------------------

    -- multiply the mantissas (includes the implicit "1.")
    -- This gives us 2 bits of integer +
    -- SIGNIFICAND_BITS*2 bits of fractional
    product <= unsigned(fpA.significand) *
               unsigned(fpB.significand);

    -- Get the MSb of the product.
    msbOfProduct <= product(PRODUCT_BITS - 1);

    process (all)
    begin
        if (msbOfProduct = '1') then
            -- The MSb is 1 so we have:
            -- 1x.xxxx but we require the mantissa to be
            -- 1.xxx so we need to shift right by 1
            mantissaBeforeRounding <= product((PRODUCT_BITS - 1)
                                              downto
                                              SIGNIFICAND_BITS);

            -- r is the next bit
            r <= product(SIGNIFICAND_BITS - 1);

            -- and s is the reduction or of all lower bits
            if (product((SIGNIFICAND_BITS - 2) downto 0) =
                to_unsigned(0, SIGNIFICAND_BITS - 1)) then
                s <= '0';
            else
                s <= '1';
            end if;
        else
            -- The MSb is 0 so we have:
            -- 01.xxxxxx which is what we require.
            -- so just drop the msb and use the next
            -- SIGNIFICAND_BITS
            mantissaBeforeRounding <= product((PRODUCT_BITS - 2)
                                              downto
                                              SIGNIFICAND_BITS - 1);

            -- r is the next bit
            r <= product(SIGNIFICAND_BITS - 2);

            -- and s is the reduction or of all lower bits
            if (product((SIGNIFICAND_BITS - 3) downto 0) =
                to_unsigned(0, SIGNIFICAND_BITS - 2)) then
                s <= '0';
            else
                s <= '1';
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- rounding:
    -----------------------------------------------------------------

    process (all)
        variable useMantissaPlus1: std_ulogic;
    begin
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

        if (roundingMode = RoundingMode_NEG_INF) then
            -- Only add one if we are negative and (r or s)
            useMantissaPlus1 := newSign and (r or s);
        elsif (roundingMode = RoundingMode_POS_INF) then
            -- Only add one if we are positive and (r or s)
            useMantissaPlus1 := (not newSign) and (r or s);
        elsif (roundingMode = RoundingMode_0) then
            -- never add one
            useMantissaPlus1 := '0';
        else --if (roundingMode = RoundingMode_NEAREST) then
            -- we add one if we are greater than halfway (r and s)
            -- in the half way case (r and (not s)) we tie to even
            -- so add 1 if the lsb of the mantissa is 1 (odd)
            -- so: (r and s) or (r and (not s) and mantissa(0))
            useMantissaPlus1 := (r and mantissaBeforeRounding(0)) or
                                (r and s);
        end if;

        -- we use SIGNIFICAND_BITS + 1
        -- so we can catch overflows
        if (useMantissaPlus1 = '0') then
            mantissaAfterRounding <= '0' & mantissaBeforeRounding;
        else
            mantissaAfterRounding <= ('0' & mantissaBeforeRounding) +
                                     to_unsigned(1, SIGNIFICAND_BITS +1);
        end if;

        -- now if that overflowed we need to divide by two
        -- note it's impossible for both the product to be 1x.xxx
        -- and the rounded mantissa to be 1x.. because we can't get
        -- 11.1111 from multiplying two numbers.
        -- max is 1.11 * 1.11 = 11.0001
        -- so the only time we overflow is when we get:
        -- 01.1111
        if (mantissaAfterRounding(SIGNIFICAND_BITS) = '1') then
            finalMantissa <= mantissaAfterRounding(SIGNIFICAND_BITS downto 1);
        else
            finalMantissa <= mantissaAfterRounding((SIGNIFICAND_BITS - 1) downto 0);
        end if;
    end process;

    -----------------------------------------------------------------
    -- Sign:
    -----------------------------------------------------------------
    -- The new sign is the XOR of the signs of the arguments
    newSign <= fpA.sign xor fpB.sign;

    -----------------------------------------------------------------
    -- Pick the correct result:
    -----------------------------------------------------------------

    -- If we overflow we should be infinity
    -- if we underflow we should be 0
    -- If either of the arguments is 0 then we should be 0
    --   note: we don't support denormals yet
    process (all)
    begin
        -- If either of the arguments is NaN
        -- or they are 0 * infinity then
        -- the output should be NaN
        if (fpPkg.is_NaN(fpA) or
            fpPkg.is_NaN(fpB) or
            (fpPkg.is_zero(fpA) and fpPkg.is_infinity(fpB)) or
            (fpPkg.is_zero(fpB) and fpPkg.is_infinity(fpA))) then
            fpC <= fpPkg.set_NaN(newSign);

        -- If either of the inputs is infinity then the
        -- result is infinity
        elsif (fpPkg.is_infinity(fpA) or
               fpPkg.is_infinity(fpB)) then
            fpC <= fpPkg.set_infinity(newSign);

        -- if we overflowed then we are either infinity
        -- or max representatable depending on rounding mode
        elsif (overflow) then
            -- If we round away from (newSign) inifinity,
            -- then the value saturates at the max
            -- representatable value = 1.111...111 * 2^EMAX
            -- if we round towards (newSign) infinity then
            -- the value is infinity
            -- if we round to nearest (ties even) then
            -- the max representatable number is odd (ends in 1)
            -- so we round to infinity
            if (roundingMode = RoundingMode_0) then
                fpC <= fpPkg.set_max(newSign);
            elsif ((roundingMode = RoundingMode_NEG_INF) and
                   (newSign = '0')) then
                fpC <= fpPkg.set_max(newSign);
            elsif ((roundingMode = RoundingMode_POS_INF) and
                   (newSign = '1')) then
                fpC <= fpPkg.set_max(newSign);
            else
                fpC <= fpPkg.set_infinity(newSign);
            end if;

        -- If we underflowed or either of the arguments is 0
        -- then the result is zero.
        -- Note: We don't handle denormals yet
        elsif ((underflow) or
               fpPkg.is_zero(fpA) or
               fpPkg.is_zero(fpB)) then
            fpC <= fpPkg.set_zero(newSign);

        -- Finally in all others cases the result is
        -- the calculated one
        else
            fpC.sign <= newSign;
            fpC.biasedExponent <= unsigned(newBiasedExponent((EXPONENT_BITS - 1) downto 0));
            fpC.significand <= finalMantissa((SIGNIFICAND_BITS - 1) downto 0);
            fpC.numType <= fpPkg.fpNumType_NORMAL;
        end if;
    end process;

end architecture synth;
