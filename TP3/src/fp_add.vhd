library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.fp_type_pkg.all;

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
        generic (TBITS: natural;
                 EBITS: natural;
                 SBITS: natural);
        port (i_sig:    in  unsigned((SBITS - 1) downto 0);
              i_bExp:   in  signed((EBITS + 1) downto 0);
              i_sign:   in  std_ulogic;
              i_r:      in  std_ulogic;
              i_s:      in  std_ulogic;
              i_rm:     in  RoundingMode;
              o_sig:    out unsigned((SBITS - 1) downto 0);
              o_bExp:   out unsigned((EBITS - 1) downto 0);
              o_type:   out fpNumType);
    end component fp_round;

    package fpPkg
            is new work.fp_helper_pkg
            generic map (TBITS => TBITS,
                         EBITS => EBITS);

    constant SBITS:             natural := fpPkg.SBITS;
    constant PIPLINE_STAGES:    natural := 6;

    type Pipeline1Result is record
        fpA:    fpPkg.fpUnpacked;
        fpB:    fpPkg.fpUnpacked;
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
        variable fpA:   fpPkg.fpUnpacked;
        variable fpB:   fpPkg.fpUnpacked;
        variable swap:  boolean;
    begin
        if (rising_edge(i_clk)) then
            fpA := fpPkg.unpack(i_a);
            fpB := fpPkg.unpack(i_b);

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
            if (fpPkg.is_zero(p1Res(1).fpB)) then
                signsDiffer := false;
            else
                signsDiffer := true when (p1Res(1).fpA.sign xor
                                          p1Res(1).fpB.sign)
                               else false;
            end if;

            p2Res(2).signsDiffer <= signsDiffer;

            -- if they differ, then get the twos complement
            -- of fpB
            if (signsDiffer) then
                p2Res(2).sig <= unsigned(not p1Res(1).fpB.sig) +
                                to_unsigned(1, SBITS);
            else
                p2Res(2).sig <= unsigned(p1Res(1).fpB.sig);
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
        variable fillerBits:    std_ulogic;
    begin
        if (rising_edge(i_clk)) then
            p1Res(3) <= p1Res(2);
            p2Res(3) <= p2Res(2);

            bitsToShift := to_integer(unsigned(p1Res(2).fpA.bExp) -
                           unsigned(p1Res(2).fpB.bExp));

            -- we shift the significand right by bitsToShift
            -- which means the range is
            -- (bitsToShift + SBITS - 1) downto
            -- bitsToShift.
            -- Which is made up of two parts:
            --   Upper bits - all 1s or 0s depending of comp2
            --   Lower bits - upper bits of significand
            --      (SBITS - 1) downto bitsToShift

            fillerBits := '1' when p2Res(2).signsDiffer
                          else '0';

            if (bitsToShift < SBITS) then
                -- copy the bits over from the old result
                p3Res(3).sig((SBITS - 1 - bitsToShift) downto 0)
                    <= p2Res(2).sig((SBITS - 1) downto bitsToShift);

                -- if we aren't shifting by 0 bits then there
                -- will be bits to shift in with fillerBits
                if (bitsToShift /= 0) then
                    p3Res(3).sig((SBITS - 1) downto (SBITS - bitsToShift))
                        <= (others => fillerBits);
                end if;
            else
                -- we shifted everything out
                -- so just fill with fillerBits
                p3Res(3).sig((SBITS - 1) downto 0)
                        <= (others => fillerBits);
            end if;

            -- g is the guard bit, it's the msb that was
            -- shifted out. 3 cases:
            -- 1) bitsToShift = 0, no bits shifted out, g = 0
            -- 2) bitsToShift > SBITS, bit shifted out
            --    is a bit that was shifted in (fillerBits)
            -- 3) others, g = oldSignificand(bitsToShift - 1)
            if (bitsToShift = 0) then
                p3Res(3).g <= '0';
            elsif (bitsToShift > SBITS) then
                p3Res(3).g <= fillerBits;
            else
                p3Res(3).g <= p2Res(2).sig(bitsToShift - 1);
            end if;

            -- r is the rounding bit, it's the second msb that
            -- was shifted out. 3 cases:
            -- 1) bitsToShift < 2, r = 0
            -- 2) bitsToShift > (SBITS + 1), r is fillerBits
            -- 3) others, r = oldSignificand(bitsToShift - 2)
            if (bitsToShift < 2) then
                p3Res(3).r <= '0';
            elsif (bitsToShift > (SBITS + 1)) then
                p3Res(3).r <= fillerBits;
            else
                p3Res(3).r <= p2Res(2).sig(bitsToShift - 2);
            end if;

            -- s is the sticky bit, it's the reduction or of all
            -- shifted out bits after g and r. 3 cases:
            -- 1) bitsToShift < 3, s = 0
            -- 2) bitsToShift > (SBITS + 2),
            --    s = (|oldSignificand) | comp2
            -- 3) others, s = |oldSignificand((bitsToShift - 3)
            --                             downto 0)
            if (bitsToShift < 3) then
                p3Res(3).s <= '0';
            elsif (bitsToShift > (SBITS + 2)) then
                p3Res(3).s <= '1' when (unsigned(p2Res(2).sig) /=
                                        to_unsigned(0, SBITS))
                              else fillerBits;
            else
                p3Res(3).s <= '1' when (unsigned(p2Res(2).sig((bitsToShift - 3)downto 0)) /=
                                        to_unsigned(0, bitsToShift - 2))
                              else '0';
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
                   ('0' & p1Res(3).fpA.sig);

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
                p5Res(5).bExp <= signed("00" & p1Res(4).fpA.bExp) +
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
                    maxShift := to_integer(signed("00" & p1Res(4).fpA.bExp)) -
                                           fpPkg.EMIN;
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

                    if (bitsToShift = 0) then
                        p5Res(5).sum <= p4Res(4).sum;
                    elsif (bitsToShift = 1) then
                        -- shifting 1 bit, just shift in g
                        p5Res(5).sum <= p4Res(4).sum((SBITS - 2) downto 0) &
                                        p3Res(4).g;
                    else
                        -- shifting more than 1 bit, shift in g then 0s
                        p5Res(5).sum <= p4Res(4).sum((SBITS - bitsToShift -1) downto 0) &
                                        p3Res(4).g &
                                        to_unsigned(0, (bitsToShift - 1));
                    end if;

                    -- adjust the exponent.
                    -- we shifted left by bitsToShift bits
                    -- so we need to decrement the exponent by
                    -- bitsToShift
                    p5Res(5).bExp <= signed("00" & p1Res(4).fpA.bExp) -
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

    fpRound: fp_round generic map (TBITS => TBITS,
                                   EBITS => EBITS,
                                   SBITS => SBITS)
                      port map (i_sig   => p5Res(5).sum,
                                i_bExp  => p5Res(5).bExp,
                                i_sign  => p6Sign,
                                i_r     => p5Res(5).r,
                                i_s     => p5Res(5).s,
                                i_rm    => i_rm,
                                o_sig   => p6Sig,
                                o_bExp  => p6BExp,
                                o_type  => p6ResultType);

    process (i_clk)
        variable fpC: fpPkg.fpUnpacked;
    begin
        if (rising_edge(i_clk)) then

            -- result
            -- If either of the arguments is NaN
            -- the output should be NaN
            if (fpPkg.is_NaN(p1Res(5).fpA) or
                fpPkg.is_NaN(p1Res(5).fpB)) then
                fpC := fpPkg.set_NaN(p6Sign);

            -- If both of the inputs are zero with
            -- opposite signs then the result is +/- 0
            -- depending on the rounding method.
            -- round towards neg_inf uses -0
            -- the rest use +0
            elsif (fpPkg.is_zero(p1Res(5).fpA) and
                   fpPkg.is_zero(p1Res(5).fpB) and
                   p1Res(5).fpA.sign /= p1Res(5).fpB.sign) then
                if (i_rm = RoundingMode_NEG_INF) then
                    fpC := fpPkg.set_zero('1');
                else
                    fpC := fpPkg.set_zero('0');
                end if;

            -- If both of the inputs are infinity with
            -- opposite signs then the result is NaN
            elsif (fpPkg.is_infinity(p1Res(5).fpA) and
                   fpPkg.is_infinity(p1Res(5).fpB) and
                   p2Res(5).signsDiffer) then
                fpC := fpPkg.set_NaN(p6Sign);

            -- If either of the inputs is infinity then the
            -- result is infinity
            elsif (fpPkg.is_infinity(p1Res(5).fpA) or
                   fpPkg.is_infinity(p1Res(5).fpB)) then
                fpC := fpPkg.set_infinity(p6Sign);

            -- Finally in all others cases the result is
            -- the calculated one
            else
                fpC.sign    := p6Sign;
                fpC.bExp    := p6BExp;
                fpC.sig     := p6Sig;
                fpC.numType := p6ResultType;
            end if;

            -- Convert the result to a vector
            o_res <= fpPkg.pack(fpC);
        end if;
    end process;

end architecture synth;
