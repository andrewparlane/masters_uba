library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.utils_pkg.all;

use work.fp_type_pkg.all;
use work.fp_helper_pkg.all;

entity fp_mult is
    generic (TBITS:     natural;
             EBITS:     natural;
             DENORMALS: boolean);
    port (i_clk:    in  std_ulogic;
          i_a:      in  std_ulogic_vector((TBITS - 1) downto 0);
          i_b:      in  std_ulogic_vector((TBITS - 1) downto 0);
          i_rm:     in  RoundingMode;
          o_res:    out std_ulogic_vector((TBITS - 1) downto 0));
end entity fp_mult;

architecture synth of fp_mult is
    component fp_round is
        generic (TBITS:     natural;
                 EBITS:     natural;
                 SBITS:     natural;
                 DENORMALS: boolean);
        port (i_clk:    in  std_ulogic;
              i_sig:    in  unsigned((SBITS - 1) downto 0);
              i_bExp:   in  signed((EBITS + 1) downto 0);
              i_sign:   in  std_ulogic;
              i_r:      in  std_ulogic;
              i_s:      in  std_ulogic;
              i_rm:     in  RoundingMode;
              o_sig:    out unsigned((SBITS - 1) downto 0);
              o_bExp:   out unsigned((EBITS - 1) downto 0);
              o_type:   out fpNumType);
    end component fp_round;

    constant SBITS:     natural := get_sbits(TBITS, EBITS);
    -- number of bits in the product
    constant PBITS:     natural := SBITS * 2;

    signal fpA: fpUnpacked;
    signal fpB: fpUnpacked;
    signal fpC: fpUnpacked;

    -- EBITS + 2 so we have the carry out bits to detect
    -- overflow and underflow
    -- first we just sum them. Then we try and normalize
    -- the product which requires adjusting the exponent
    -- then we round which may require one final adjustment
    signal sumOfBExps:      signed((EBITS + 1) downto 0);
    signal adjustedBExp:    signed((EBITS + 1) downto 0);
    signal finalBExp:       unsigned((EBITS - 1) downto 0);

    -- The product of the two significands
    signal product:         unsigned((PBITS - 1) downto 0);

    -- The new significand is the product. We try and normalize
    -- it. Then we may have to round it.
    signal normalizedSig:   unsigned((SBITS - 1) downto 0);
    signal finalSig:        unsigned((SBITS - 1) downto 0);

    -- rounding bits
    -- r - is the MSb after the significand
    -- s - is the reduction-or of all subsequent bits
    signal r:               std_ulogic;
    signal s:               std_ulogic;

    -- the new sign depends on the signs of the arguments
    signal newSign:         std_ulogic;

    -- The fp_round component tells us if the type of the result.
    signal resultType:      fpNumType;
begin

    -----------------------------------------------------------------
    -- Type conversions
    -----------------------------------------------------------------

    -- Convert A and B to fpUnpackeds
    fpA <= unpack(i_a, TBITS, EBITS);
    fpB <= unpack(i_b, TBITS, EBITS);

    -- Convert the result to a vector
    o_res <= pack(fpC, TBITS, EBITS);

    -----------------------------------------------------------------
    -- Add the exponents
    -----------------------------------------------------------------
    sumOfBExps <= ("00" & signed(get_bExp(fpA, EBITS))) +
                  ("00" & signed(get_bExp(fpB, EBITS))) -
                  to_signed(fpA.bias, EBITS + 2);

    -----------------------------------------------------------------
    -- Multiply the significands
    -----------------------------------------------------------------

    -- The significand has 1 bit of integer + SBITS-1
    -- of fractional. Therefore the product gives us 2 bits of
    -- integer + (SBITS-1)*2 bits of fractional
    product <= unsigned(get_sig(fpA, SBITS)) *
               unsigned(get_sig(fpB, SBITS));

    process (all)
        variable productExt:        unsigned((PBITS + SBITS) downto 0);
        variable bitsToShift:       integer;
        variable maxShift:          integer;
        variable lsb:               integer;
    begin
        if ((to_integer(sumOfBExps) < get_emin) and
            DENORMALS) then

            -- Our current exponent is less than EMIN,
            -- which means we have to shift the result right
            -- to get it back to EMIN (gradual underflow).
            -- If we shift out all the bits of the product
            -- then we end up with an actual underflow
            -- and the result is 0.
            bitsToShift := get_emin - to_integer(sumOfBExps);

            if (bitsToShift > SBITS) then
                -- if we shift by more than SBITS
                -- then the significand is 0
                -- s is the reduction-or of the product.
                -- r is the last bit shifted out, which is
                -- either the MSb of the product, or 0
                normalizedSig <= to_unsigned(0, SBITS);
                if (bitsToShift = (SBITS+1)) then
                    r <= product(PBITS-1);
                else
                    r <= '0';
                end if;

                s <= reduction_or(std_ulogic_vector(product));
            else
                -- The significand is the product, right shifted
                -- by bitsToShift. We store the product in a
                -- variable of size PBITS + SBITS + 1.
                -- So that at the maximum shift of SBITS, all
                -- of the data is still in the reult, so we can
                -- get S and R easily.
                productExt := product & to_unsigned(0, SBITS+1);
                productExt := SHIFT_RIGHT(productExt, bitsToShift);

                -- We currently have ab.cde
                -- so shifting right by one gives us: 0a.bcde
                -- so we don't use the msb of the result.
                -- if the upper bit is PBITS+SBITS-1 and we
                -- want SBITS, then the lsb is PBITS
                normalizedSig <= productExt((PBITS+SBITS-1) downto (PBITS));

                -- r is the next bit
                r <= productExt(PBITS-1);

                -- s is the reduction or of all lower bits
                -- bitsToShift max for us to be here is SBITS
                -- if we shifted
                s <= reduction_or(std_ulogic_vector(productExt((PBITS-2) downto 0)));
            end if;

            -- set the exponent to EMIN. This gets changed to
            -- a 0 when we get packed into the vector
            adjustedBExp <= to_signed(get_emin, EBITS + 2);

        else
            -- either we don't support denormals,
            -- or we didn't have [gradual] underflow

            if (product(PBITS - 1) = '1') then
                -- The MSb is 1 so we have:
                -- 1x.xxxx but we require the significand to be
                -- 1.xxx so we need to shift right by 1
                normalizedSig <= product((PBITS - 1) downto SBITS);

                -- we shifted right, so add 1 to the exponent
                adjustedBExp <= sumOfBExps + to_signed(1, EBITS+2);

                -- r is the next bit
                r <= product(SBITS - 1);

                -- and s is the reduction or of all lower bits
                if (product((SBITS - 2) downto 0) = to_unsigned(0, SBITS - 1)) then
                    s <= '0';
                else
                    s <= '1';
                end if;
            else

                -- we have 0x.xxxx, and want 1.xxxx
                -- so we need to shift left by some amount
                -- (potentially 0)

                if (not DENORMALS) then
                    -- we don't support denormals,
                    -- which means 1.xxx * 1.xxx > 1.0
                    -- (unless one of the args is 0).
                    -- And because we are 0x.xxxx, we know
                    -- tha we are actually: 01.xxxx.
                    -- drop the leading 0 and we are good
                    normalizedSig <= product((PBITS - 2) downto (SBITS-1));
                    -- r is the next bit
                    r <= product(SBITS - 2);
                    -- and s is the reduction or of all lower bits
                    if (product((SBITS - 3) downto 0) = to_unsigned(0, SBITS - 2)) then
                        s <= '0';
                    else
                        s <= '1';
                    end if;

                    -- no need to adjust the exponent
                    adjustedBExp <= sumOfBExps;
                else
                    -- we support denormals, so we need to shift
                    -- left until normalized (ie. msb is 1)
                    -- or we would underflow (adjust = EMIN)
                    maxShift := 1 + to_integer(sumOfBExps) -
                                get_emin;

                    -- if all the bits are 0, then we have
                    -- underflowed and are 0.
                    bitsToShift := -1;
                    for i in 0 to (PBITS - 1) loop
                        if ((product(PBITS - i - 1) = '1') or
                            (i >= maxShift)) then
                            bitsToShift := i;
                            exit;
                        end if;
                    end loop;

                    if (bitsToShift = -1) then
                        -- all bits are 0, result is 0
                        normalizedSig <= to_unsigned(0, SBITS);

                        -- biased exponent is 0
                        adjustedBExp <= to_signed(0, EBITS + 2);

                        -- r is 0, s is 0
                        r <= '0';
                        s <= '0';
                    else
                        -- bitsToShift max = PBITS - 1
                        -- shifting the product by that would
                        -- leave 1 bits of the product.
                        -- We need SBITS + 2 (r and s),
                        -- so if we append (SBITS+1) bits
                        -- of 0s to the product we don't need
                        -- to worry about ranges.
                        productExt := product((PBITS-1) downto 0) &
                                      to_unsigned(0, SBITS+1);

                        productExt := SHIFT_LEFT(productExt, bitsToShift);

                        -- We currently have 0a.bcde000
                        -- so shifting left by one gives us: a.bcde0000
                        -- so we use the msb of the result.
                        -- if the upper bit is PBITS+SBITS and we
                        -- want SBITS, then the lsb is PBITS+1
                        normalizedSig <= productExt((PBITS + SBITS) downto (PBITS+1));

                        -- r is the next bit
                        r <= productExt(PBITS);

                        -- s is the reduction-or of the rest of the bits
                        s <= reduction_or(std_ulogic_vector(productExt((PBITS-1) downto 0)));

                        -- adjust the exponent.
                        -- we shifted left by bitsToShift bits
                        -- but the decimal point was after the second
                        -- bit. So we need to decrement the exponent
                        -- by bitsToShift - 1
                        adjustedBExp <= sumOfBExps -
                                        to_signed(bitsToShift - 1,
                                                  EBITS + 2);
                    end if;
                end if;
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
    fpRound: fp_round generic map (TBITS     => TBITS,
                                   EBITS     => EBITS,
                                   SBITS     => SBITS,
                                   DENORMALS => DENORMALS)
                      port map (i_clk   => i_clk,
                                i_sig   => normalizedSig,
                                i_bExp  => adjustedBExp,
                                i_sign  => newSign,
                                i_r     => r,
                                i_s     => s,
                                i_rm    => i_rm,
                                o_sig   => finalSig,
                                o_bExp  => finalBExp,
                                o_type  => resultType);

    -----------------------------------------------------------------
    -- Pick the correct result:
    -----------------------------------------------------------------

    process (i_clk)
    begin
        if (rising_edge(i_clk)) then
            -- If either of the arguments is NaN
            -- or they are 0 * infinity then
            -- the output should be NaN
            if (is_NaN(fpA) or
                is_NaN(fpB) or
                (is_zero(fpA) and is_infinity(fpB)) or
                (is_zero(fpB) and is_infinity(fpA))) then
                fpC <= set_NaN(newSign, TBITS, EBITS);

            -- If either of the inputs is infinity then the
            -- result is infinity.
            elsif (is_infinity(fpA) or
                   is_infinity(fpB)) then
                fpC <= set_infinity(newSign, TBITS, EBITS);

            -- If either of the arguments is 0
            -- then the result is zero.
            elsif (is_zero(fpA) or
                   is_zero(fpB)) then
                fpC <= set_zero(newSign, TBITS, EBITS);

            -- Finally in all others cases the result is
            -- the calculated one
            else
                fpC.emin    <= get_emin;
                fpC.emax    <= get_emax(EBITS);
                fpC.bias    <= get_bias(EBITS);
                fpC.sign    <= newSign;
                fpC.bExp    <= resize(finalBExp, MAX_EBITS);
                fpC.sig     <= resize(finalSig, MAX_SBITS);
                fpC.numType <= resultType;
            end if;
        end if;
    end process;

end architecture synth;
