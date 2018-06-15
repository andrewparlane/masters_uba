library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

library common;
use common.utils_pkg.all;

use work.fp_helper_pkg.all;

entity fp_add is
    generic (TBITS:     natural;
             EBITS:     natural;
             DENORMALS: boolean);
    port (i_clk:    in  std_ulogic;
          i_a:      in  std_ulogic_vector((TBITS - 1) downto 0);
          i_b:      in  std_ulogic_vector((TBITS - 1) downto 0);
          i_rm:     in  RoundingMode;
          o_res:    out std_ulogic_vector((TBITS - 1) downto 0));
end entity fp_add;

architecture synth of fp_add is

    component fp_round is
        generic (EBITS: natural;
                 SBITS: natural;
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

    constant SBITS:             natural := get_sbits(TBITS, EBITS);
    constant PIPLINE_STAGES:    natural := 6;

    type Pipeline1Result is record
        fpA:    fpUnpacked;
        fpB:    fpUnpacked;
        swap:   boolean;
    end record Pipeline1Result;

    type Pipeline2Result is record
        sig:            unsigned((SBITS - 1) downto 0);
        signsDiffer:    boolean;
    end record Pipeline2Result;

    type Pipeline3Result is record
        sig:    unsigned((SBITS - 1) downto 0);
        g:      std_ulogic;
        r:      std_ulogic;
        s:      std_ulogic;
    end record Pipeline3Result;

    type Pipeline4Result is record
        sum:            unsigned((SBITS - 1) downto 0);
        carry:          std_ulogic;
        sumNegative:    boolean;
    end record Pipeline4Result;

    type Pipeline5Result is record
        sum:  unsigned((SBITS - 1) downto 0);
        -- +2 for overflow / undeflow
        bExp: signed((EBITS + 1) downto 0);
        r:    std_ulogic;
        s:    std_ulogic;
    end record Pipeline5Result;

    -- pipeline stage 6 internal vars
    signal p6Sign:          std_ulogic;
    signal p6Sig:           unsigned((SBITS - 1) downto 0);
    signal p6BExp:          unsigned((EBITS - 1) downto 0);
    signal p6ResultType:    fpNumType;

    type Pipeline1ResultArray is array (1 to (PIPLINE_STAGES - 1))
                              of Pipeline1Result;

    type Pipeline2ResultArray is array (2 to (PIPLINE_STAGES - 1))
                                  of Pipeline2Result;

    type Pipeline3ResultArray is array (3 to (PIPLINE_STAGES - 1))
                                  of Pipeline3Result;

    type Pipeline4ResultArray is array (4 to (PIPLINE_STAGES - 1))
                                  of Pipeline4Result;

    type Pipeline5ResultArray is array (5 to (PIPLINE_STAGES - 1))
                                  of Pipeline5Result;

    signal p1Res:       Pipeline1ResultArray;
    signal p2Res:       Pipeline2ResultArray;
    signal p3Res:       Pipeline3ResultArray;
    signal p4Res:       Pipeline4ResultArray;
    signal p5Res:       Pipeline5ResultArray;

begin

    -----------------------------------------------------------------
    -- Pipeline stage 1
    -----------------------------------------------------------------
    -- 0) Unpack the vector inputs
    -- 1) if (a.exp < b.exp) swap the operands
    -----------------------------------------------------------------

    process (i_clk)
        variable fpA:   fpUnpacked;
        variable fpB:   fpUnpacked;
        variable swap:  boolean;
    begin
        if (rising_edge(i_clk)) then
            fpA := unpack(i_a, TBITS, EBITS);
            fpB := unpack(i_b, TBITS, EBITS);

            -- swap if A is less than B (don't include the sign)
            swap := (i_a((TBITS-2) downto 0) <
                     i_b((TBITS-2) downto 0));

            p1Res(1).swap <= swap;

            if (swap) then
                p1Res(1).fpA <= fpB;
                p1Res(1).fpB <= fpA;
            else
                p1Res(1).fpA <= fpA;
                p1Res(1).fpB <= fpB;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 2
    -----------------------------------------------------------------
    -- 2) if (a.sign /= b.sign)
    --      b.sig = twosComplement(b.sig)
    -----------------------------------------------------------------
    process (i_clk)
        variable signsDiffer: boolean;
    begin
        if (rising_edge(i_clk)) then
            p1Res(2) <= p1Res(1);

            -- check if the signs differ. if fpB is zero
            -- then just say they don't differ
            if (is_zero(p1Res(1).fpB)) then
                signsDiffer := false;
            else
                if (p1Res(1).fpA.sign xor p1Res(1).fpB.sign) then
                    signsDiffer := true;
                else
                    signsDiffer := false;
                end if;
            end if;

            p2Res(2).signsDiffer <= signsDiffer;

            -- if they differ, then get the twos complement
            -- of fpB
            if (signsDiffer) then
                p2Res(2).sig <= unsigned(not get_sig(p1Res(1).fpB, SBITS)) +
                                to_unsigned(1, SBITS);
            else
                p2Res(2).sig <= unsigned(get_sig(p1Res(1).fpB, SBITS));
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 3
    -----------------------------------------------------------------
    -- 3) shift b.sig right by a.exp - b.exp places
    --      shifting in 1s if comp2.
    --      Of the bits shifted out:
    --          g - guard bit, most significant bit
    --          r - rounding bit, next most significant bit
    --          g - sticking bit, rest of the bits orred together
    -----------------------------------------------------------------

    process (i_clk)
        variable bitsToShift:   integer;
        variable fillerBit:     std_ulogic;

        -- we shifte fpB.sig by fpA.exp - fpB.exp.
        -- in the worst case we shift out the entire significand
        -- + 1 bit for guard, and + 1 bit for round
        -- = SBITS+2. So if we create a variable of size
        -- SBITS + SBITS+2. Then when we shift we know exactly
        -- where to look for G and R. S is also easy to check.
        -- We also add 1 bit at the top, so that the arithmetic
        -- shift, shifts that bit repeatedly in. Also it's signed
        -- for the same reason
        variable shifted: signed(((2*SBITS)+2) downto 0);
    begin
        if (rising_edge(i_clk)) then
            p1Res(3) <= p1Res(2);
            p2Res(3) <= p2Res(2);

            -- we shift the significand right by bitsToShift
            bitsToShift := to_integer(unsigned(get_bExp(p1Res(2).fpA, EBITS)) -
                                      unsigned(get_bExp(p1Res(2).fpB, EBITS)));


            -- we shift in fillerBit, which depends on if
            -- we complemented in stage 2 or not.
            if (p2Res(2).signsDiffer) then
                fillerBit := '1';
            else
                fillerBit := '0';
            end if;

            -- take the significand to shift, prepend filler bit
            -- and append SBITS+2 of 0s
            shifted := signed(fillerBit &
                              p2Res(2).sig &
                              to_unsigned(0, SBITS+2));

            -- now shift it right by bitsToShift
            shifted := SHIFT_RIGHT(shifted, bitsToShift);

            -- the resulting significand is in the upper SBITS
            -- after the MSb.
            p3Res(3).sig <= unsigned(shifted(((2*SBITS)+1) downto (SBITS+2)));

            -- g is the guard bit, it's the msb that was
            -- shifted out.
            p3Res(3).g <= shifted(SBITS+1);

            -- r is the rounding bit, it's the second msb that
            -- was shifted out.
            p3Res(3).r <= shifted(SBITS);

            -- s is the sticky bit, it's the reduction or of all
            -- shifted out bits after g and r. 2 cases:
            -- 1) bitsToShift <= SBITS+2,
            --      we haven't shifted out of our variable
            --      so s is the reduction or of the lower SBITS
            -- 2) bitsToShift > SBITS+2
            --      we shifted out all our significand
            --      plus one for g and r. So s is the
            --      reduction or of the significand + fillerBit
            if (bitsToShift <= (SBITS+2)) then
                p3Res(3).s <= reduction_or(std_ulogic_vector(shifted((SBITS-1) downto 0)));
            else
                p3Res(3).s <= reduction_or(std_ulogic_vector(fillerBit & p2Res(2).sig));
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 4
    -----------------------------------------------------------------
    -- 4) Compute the sum fpA.sig + fpB.sig including
    --    carray out. If comp2 and msb of sum is 1 and carray out
    --    is 0, then S = twosComplement(S)
    -----------------------------------------------------------------
    process (i_clk)
        -- +1 for carry out
        variable sum: unsigned(SBITS downto 0);
    begin
        if (rising_edge(i_clk)) then
            p1Res(4) <= p1Res(3);
            p2Res(4) <= p2Res(3);
            p3Res(4) <= p3Res(3);

            sum := ('0' & p3Res(3).sig) +
                   ('0' & get_sig(p1Res(3).fpA, SBITS));

            p4Res(4).carry <= sum(SBITS);

            if ((p2Res(3).signsDiffer) and  -- if the signs of the arguments differ
                (sum(SBITS - 1) = '1') and  -- and the msb of the sum is 1
                (sum(SBITS) = '0')) then    -- and there wasn't a carry out

                -- result is negative, so get twos complement
                p4Res(4).sum <= (not sum((SBITS - 1) downto 0)) +
                                to_unsigned(1, SBITS);
                p4Res(4).sumNegative <= true;
            else

                -- result is positive, carry on
                p4Res(4).sum <= sum((SBITS - 1) downto 0);
                p4Res(4).sumNegative <= false;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 5)
    -----------------------------------------------------------------
    -- 5) shift the result of the sum until it is normalized
    --    and adjust the exponent
    -- 6) Adjust g, r, and s
    -----------------------------------------------------------------

    process (i_clk)
        variable bitsToShift:   integer;
        variable maxShift:      integer;
    begin
        if (rising_edge(i_clk)) then
            p1Res(5) <= p1Res(4);
            p2Res(5) <= p2Res(4);
            p3Res(5) <= p3Res(4);
            p4Res(5) <= p4Res(4);

            -- if the signs of the arguments are the same
            -- (not comp2), and there was a carry out
            if ((not p2Res(4).signsDiffer) and
                (p4Res(4).carry = '1')) then

                -- shift the result right by one
                -- filling in the new upper bit with
                -- the carry bit
                p5Res(5).sum <= p4Res(4).carry &
                                p4Res(4).sum((SBITS - 1) downto 1);

                -- we shifted right by one -> /2
                -- so exponent should be +1
                p5Res(5).bExp <= signed("00" & get_bExp(p1Res(4).fpA, EBITS)) +
                                 to_signed(1, EBITS + 2);

                -- adjust r and s
                p5Res(5).r <= p4Res(4).sum(0);
                p5Res(5).s <= p3Res(4).g or
                              p3Res(4).r or
                              p3Res(4).s;
            else

                -- shift left until normalized (ie. msb is 1)
                -- if we support denormals then we only shift
                -- until biasedExponent is EMIN.
                -- otherwise just shift until we find a 1
                if (DENORMALS) then
                    maxShift := to_integer(signed("00" & get_bExp(p1Res(4).fpA, EBITS))) -
                                           get_emin;
                else
                    -- set maxShift to SBITS
                    -- this should optimize out the extra
                    -- comparison because max i is SBITS - 1
                    maxShift := SBITS;
                end if;

                bitsToShift := -1;
                for i in 0 to (SBITS - 1) loop
                    if ((p4Res(4).sum(SBITS - i - 1) = '1') or
                        (i = maxShift)) then
                        bitsToShift := i;
                        exit;
                    end if;
                end loop;

                if (bitsToShift = -1) then
                    -- all bits are 0, result is 0
                    p5Res(5).sum <= to_unsigned(0, SBITS);
                    -- exponent is 0
                    p5Res(5).bExp <= to_signed(0, EBITS + 2);

                    -- adjust r and s
                    p5Res(5).r <= '0';
                    p5Res(5).s <= '0';
                else

                    -- shift left by bitsToShift
                    -- first bit to shift in is g, then 0s
                    p5Res(5).sum <= SHIFT_LEFT(p4Res(4).sum & p3Res(4).g,
                                               bitsToShift)(SBITS downto 1);

                    -- adjust the exponent.
                    -- we shifted left by bitsToShift bits
                    -- so we need to decrement the exponent by
                    -- bitsToShift
                    p5Res(5).bExp <= signed("00" & get_bExp(p1Res(4).fpA, EBITS)) -
                                     to_signed(bitsToShift, EBITS + 2);

                    -- adjust r and s
                    if (bitsToShift = 0) then
                        p5Res(5).r <= p3Res(4).g;
                        p5Res(5).s <= p3Res(4).r or
                                      p3Res(4).s;
                    elsif (bitsToShift = 1) then
                        p5Res(5).r <= p3Res(4).r;
                        p5Res(5).s <= p3Res(4).s;
                    else
                        p5Res(5).r <= '0';
                        p5Res(5).s <= '0';
                    end if;
                end if;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 6)
    -----------------------------------------------------------------
    -- 7) Rounding
    -- 8) Compute the sign
    -----------------------------------------------------------------

    -- compute the sign
    process (all)
    begin
        if (p2Res(5).signsDiffer) then
            -- the signs of A and B are the same
            -- that's our sign
            p6Sign <= p1Res(5).fpA.sign;
        elsif (p1Res(5).swap) then
            -- If we swapped the arguments, then the
            -- sign is the sign of B, except we stored the
            -- swapped arguments, so use sign of A
            p6Sign <= p1Res(5).fpA.sign;
        elsif (p4Res(5).sumNegative) then
            -- If we complemented the result in step 4
            -- the the sign is the sign of B
            p6Sign <= p1Res(5).fpB.sign;
        else
            -- otherwise we are the sign of A
            p6Sign <= p1Res(5).fpA.sign;
        end if;
    end process;

    fpRound: fp_round generic map (EBITS => EBITS,
                                   SBITS => SBITS,
                                   DENORMALS => DENORMALS)
                      port map (i_clk   => i_clk,
                                i_sig   => p5Res(5).sum,
                                i_bExp  => p5Res(5).bExp,
                                i_sign  => p6Sign,
                                i_r     => p5Res(5).r,
                                i_s     => p5Res(5).s,
                                i_rm    => i_rm,
                                o_sig   => p6Sig,
                                o_bExp  => p6BExp,
                                o_type  => p6ResultType);

    process (i_clk)
        variable fpC: fpUnpacked;
    begin
        if (rising_edge(i_clk)) then

            -- result
            -- If either of the arguments is NaN
            -- the output should be NaN
            if (is_NaN(p1Res(5).fpA) or
                is_NaN(p1Res(5).fpB)) then
                fpC := set_NaN(p6Sign, TBITS, EBITS);

            -- If both of the inputs are zero with
            -- opposite signs then the result is +/- 0
            -- depending on the rounding method.
            -- round towards neg_inf uses -0
            -- the rest use +0
            elsif (is_zero(p1Res(5).fpA) and
                   is_zero(p1Res(5).fpB) and
                   p1Res(5).fpA.sign /= p1Res(5).fpB.sign) then
                if (i_rm = RoundingMode_NEG_INF) then
                    fpC := set_zero('1', TBITS, EBITS);
                else
                    fpC := set_zero('0', TBITS, EBITS);
                end if;

            -- If both of the inputs are infinity with
            -- opposite signs then the result is NaN
            elsif (is_infinity(p1Res(5).fpA) and
                   is_infinity(p1Res(5).fpB) and
                   p2Res(5).signsDiffer) then
                fpC := set_NaN(p6Sign, TBITS, EBITS);

            -- If either of the inputs is infinity then the
            -- result is infinity
            elsif (is_infinity(p1Res(5).fpA) or
                   is_infinity(p1Res(5).fpB)) then
                fpC := set_infinity(p6Sign, TBITS, EBITS);

            -- Finally in all others cases the result is
            -- the calculated one
            else
                fpC.emin    := get_emin;
                fpC.emax    := get_emax(EBITS);
                fpC.bias    := get_bias(EBITS);
                fpC.sign    := p6Sign;
                fpC.bExp    := resize(p6BExp, MAX_EBITS);
                fpC.sig     := resize(p6Sig, MAX_SBITS);
                fpC.numType := p6ResultType;
            end if;

            -- Convert the result to a vector
            o_res <= pack(fpC, TBITS, EBITS);
        end if;
    end process;

end architecture synth;
