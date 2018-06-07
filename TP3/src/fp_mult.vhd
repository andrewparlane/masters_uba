library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.fp_type_pkg.all;

entity fp_mult is
    generic (TOTAL_BITS:    natural;
             EXPONENT_BITS: natural);
    port (inA:          in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          inB:          in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          rm:           in  RoundingMode;
          outC:         out std_ulogic_vector((TOTAL_BITS - 1) downto 0));
end entity fp_mult;

architecture synth of fp_mult is
    component fp_round is
        generic (TOTAL_BITS:        natural;
                 EXPONENT_BITS:     natural;
                 SIGNIFICAND_BITS:  natural);
        port (i_sig:    in  unsigned((SIGNIFICAND_BITS - 1) downto 0);
              i_bExp:   in  signed((EXPONENT_BITS + 1) downto 0);
              i_sign:   in  std_ulogic;
              i_r:      in  std_ulogic;
              i_s:      in  std_ulogic;
              i_rm:     in  RoundingMode;
              o_sig:    out unsigned((SIGNIFICAND_BITS - 1) downto 0);
              o_bExp:   out unsigned((EXPONENT_BITS - 1) downto 0);
              o_type:   out fpNumType);
    end component fp_round;

    package fpPkg
            is new work.fp_helper_pkg
            generic map (TOTAL_BITS => TOTAL_BITS,
                         EXPONENT_BITS => EXPONENT_BITS);

    constant SIGNIFICAND_BITS:  natural := fpPkg.SIGNIFICAND_BITS;
    constant PRODUCT_BITS:      natural := SIGNIFICAND_BITS * 2;

    signal fpA:    fpPkg.fpUnpacked;
    signal fpB:    fpPkg.fpUnpacked;
    signal fpC:    fpPkg.fpUnpacked;


    -- EXPONENT_BITS + 2 so we have the carry out bits
    -- we calculate both biased(e1 + e2) and biased(e1 + e2) + 1
    -- then select the correct one based on msbOfProduct
    signal newBiasedExponent:           signed((EXPONENT_BITS + 1) downto 0);
    signal finalBiasedExponent:         unsigned((EXPONENT_BITS - 1) downto 0);

    -- The product of the two significands
    signal product:                     unsigned((PRODUCT_BITS - 1) downto 0);
    signal msbOfProduct:                std_ulogic;

    -- The new significand depends on the msb of the product
    -- We use SIGNIFICAND_BITS + 1 for the
    -- significandAfterRounding so that we can catch overflow
    signal significandBeforeRounding:   unsigned((SIGNIFICAND_BITS - 1) downto 0);
    signal finalSignificand:            unsigned((SIGNIFICAND_BITS - 1) downto 0);

    -- rounding bits
    -- r - is the MSb after the significand
    -- s - is the reduction or of all subsequent bits
    signal r:                           std_ulogic;
    signal s:                           std_ulogic;

    -- the new sign depends on the signs of the arguments
    signal newSign:                     std_ulogic;

    signal resultType:                  fpNumType;

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

        -- If the MSb of the product of the significands is 1
        -- or the MSb of the significand after rounding is 1 then
        -- we need to add 1 to the sum of the exponents
        if (msbOfProduct = '1') then
            newBiasedExponent <= sumOfBiasedExponents +
                                 to_signed(1, EXPONENT_BITS + 2);
        else
            newBiasedExponent <= sumOfBiasedExponents;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Multiply the significands
    -----------------------------------------------------------------

    -- The significand has 1 bit of integer + SIGNIFICAND_BITS-1
    -- of fractional. Therefore the product gives us 2 bits of
    -- integer + (SIGNIFICAND_BITS-1)*2 bits of fractional
    product <= unsigned(fpA.significand) *
               unsigned(fpB.significand);

    -- Get the MSb of the product.
    msbOfProduct <= product(PRODUCT_BITS - 1);

    process (all)
    begin
        if (msbOfProduct = '1') then
            -- The MSb is 1 so we have:
            -- 1x.xxxx but we require the significand to be
            -- 1.xxx so we need to shift right by 1
            significandBeforeRounding <= product((PRODUCT_BITS - 1)
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
            significandBeforeRounding <= product((PRODUCT_BITS - 2)
                                                 downto
                                                 (SIGNIFICAND_BITS - 1));

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
    -- Sign:
    -----------------------------------------------------------------
    -- The new sign is the XOR of the signs of the arguments
    newSign <= fpA.sign xor fpB.sign;

    -----------------------------------------------------------------
    -- rounding:
    -----------------------------------------------------------------
    fpRound: fp_round generic map (TOTAL_BITS       => TOTAL_BITS,
                                   EXPONENT_BITS    => EXPONENT_BITS,
                                   SIGNIFICAND_BITS => SIGNIFICAND_BITS)
                      port map (i_sig   => significandBeforeRounding,
                                i_bExp  => newBiasedExponent,
                                i_sign  => newSign,
                                i_r     => r,
                                i_s     => s,
                                i_rm    => rm,
                                o_sig   => finalSignificand,
                                o_bExp  => finalBiasedExponent,
                                o_type  => resultType);

    -----------------------------------------------------------------
    -- Pick the correct result:
    -----------------------------------------------------------------

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
        -- result is infinity.
        elsif (fpPkg.is_infinity(fpA) or
               fpPkg.is_infinity(fpB)) then
            fpC <= fpPkg.set_infinity(newSign);

        -- If either of the arguments is 0
        -- then the result is zero.
        elsif (fpPkg.is_zero(fpA) or
               fpPkg.is_zero(fpB)) then
            fpC <= fpPkg.set_zero(newSign);

        -- Finally in all others cases the result is
        -- the calculated one
        else
            fpC.sign <= newSign;
            fpC.biasedExponent <= finalBiasedExponent;
            fpC.significand <= finalSignificand;
            fpC.numType <= resultType;
        end if;
    end process;

end architecture synth;
