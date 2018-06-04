library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.fp_rounding_pkg.all;

entity fp_add is
    generic (TOTAL_BITS:    natural;
             EXPONENT_BITS: natural);
    port (clk:  in  std_ulogic;
          rst:  in  std_ulogic;
          inA:  in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          inB:  in  std_ulogic_vector((TOTAL_BITS - 1) downto 0);
          roundingMode: RoundingMode;
          outC: out std_ulogic_vector((TOTAL_BITS - 1) downto 0));
end entity fp_add;

architecture synth of fp_add is
    package fpPkg
            is new work.fp_helper_pkg
            generic map (TOTAL_BITS => TOTAL_BITS,
                         EXPONENT_BITS => EXPONENT_BITS);

    constant SIGNIFICAND_BITS:  natural := fpPkg.SIGNIFICAND_BITS;
    constant MANTISSA_BITS:     natural := SIGNIFICAND_BITS + 1;

    constant PIPLINE_STAGES:    natural := 6;

    type Pipeline1Result is record
        fpA:    fpPkg.fpType;
        fpB:    fpPkg.fpType;
        swap:   boolean;
    end record Pipeline1Result;

    type Pipeline2Result is record
        mantissa:   unsigned((MANTISSA_BITS - 1) downto 0);
        comp2:      std_ulogic;
    end record Pipeline2Result;

    type Pipeline3Result is record
        shiftedMantissa:    unsigned((MANTISSA_BITS - 1) downto 0);
        g:                  std_ulogic;
        r:                  std_ulogic;
        s:                  std_ulogic;
    end record Pipeline3Result;

    type Pipeline4Result is record
        sum:                unsigned((MANTISSA_BITS - 1) downto 0);
        carryOut:           std_ulogic;
        comp2:              boolean;
    end record Pipeline4Result;

    type Pipeline5Result is record
        normalizedSum:      unsigned((MANTISSA_BITS - 1) downto 0);
        -- +2 for overflow / undeflow
        biasedExponent:     signed((EXPONENT_BITS + 1) downto 0);
        --r:                  std_ulogic;
        --s:                  std_ulogic;
    end record Pipeline5Result;

    -- pipeline stage 1 internal vars
    signal p1FpA:       fpPkg.fpType;
    signal p1FpB:       fpPkg.fpType;

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

    -- 0) Unpack the vector inputs
    p1FpA <= fpPkg.vect_to_fpType(inA);
    p1FpB <= fpPkg.vect_to_fpType(inB);

    process (clk, rst)
    begin
        if (rst = '1') then
            -- do nothing
        elsif (rising_edge(clk)) then
            p1Res(1).swap  <= (p1FpA.biasedExponent <
                               p1FpB.biasedExponent);
            if (p1FpA.biasedExponent < p1FpB.biasedExponent) then
                p1Res(1).fpA <= p1FpB;
                p1Res(1).fpB <= p1FpA;
            else
                p1Res(1).fpA <= p1FpA;
                p1Res(1).fpB <= p1FpB;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 2
    -----------------------------------------------------------------
    -- 2) if (a.sign /= b.sign)
    --      b.significand = twosComplement(b.significand)
    -----------------------------------------------------------------
    process (clk, rst)
    begin
        if (rst = '1') then
            -- do nothing
        elsif (rising_edge(clk)) then
            p1Res(2) <= p1Res(1);

            p2Res(2).comp2 <= p1Res(1).fpA.sign xor p1Res(1).fpB.sign;

            if (p1Res(1).fpA.sign /= p1Res(1).fpB.sign) then
                p2Res(2).mantissa <= unsigned(not fpPkg.get_mantissa(p1Res(1).fpB)) +
                                     to_unsigned(1, MANTISSA_BITS);
            else
                p2Res(2).mantissa <= unsigned(fpPkg.get_mantissa(p1Res(1).fpB));
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 3
    -----------------------------------------------------------------
    -- 3) shift b.mantissa right by a.exp - b.exp places
    --      shifting in 1s if comp2.
    --      Of the bits shifted out:
    --          g - guard bit, most significant bit
    --          r - rounding bit, next most significant bit
    --          g - sticking bit, rest of the bits orred together
    -----------------------------------------------------------------

    process (clk, rst)
        variable bitsToShift: integer;
    begin
        if (rst = '1') then
            -- do nothing
        elsif (rising_edge(clk)) then
            p1Res(3) <= p1Res(2);
            p2Res(3) <= p2Res(2);

            bitsToShift := to_integer(unsigned(p1Res(2).fpA.biasedExponent) -
                            unsigned(p1Res(2).fpB.biasedExponent));

            -- we shift mantissa right by bitsToShift
            -- which means the range is
            -- (bitsToShift + MANTISSA_BITS - 1) downto
            -- bitsToShift.
            -- Which is made up of two parts:
            --   Upper bits - all 1s or 0s depending of comp2
            --   Lower bits - upper bits of mantissa
            --      (MANTISSA_BITS - 1) downto bitsToShift

            if (bitsToShift < MANTISSA_BITS) then
                -- copy the bits over from the old result
                p3Res(3).shiftedMantissa((MANTISSA_BITS - 1 - bitsToShift) downto 0)
                    <= p2Res(2).mantissa((MANTISSA_BITS - 1)
                                         downto bitsToShift);

                -- if we aren't shifting by 0 bits then there
                -- will be bits to shift in with 1s or 0s
                -- depending on comp2
                if (bitsToShift /= 0) then
                    p3Res(3).shiftedMantissa((MANTISSA_BITS - 1) downto (MANTISSA_BITS - bitsToShift))
                        <= (others => p2Res(2).comp2);
                end if;
            else
                -- we shifted everything out
                -- so just fill with 1s or 0s
                p3Res(3).shiftedMantissa((MANTISSA_BITS - 1) downto 0)
                        <= (others => p2Res(2).comp2);
            end if;

            -- g is the guard bit, it's the msb that was
            -- shifted out. 3 cases:
            -- 1) bitsToShift = 0, no bits shifted out, g = 0
            -- 2) bitsToShift > MANTISSA_BITS, bit shifted out
            --    is a bit that was shifted in so a 1 or a 0
            --    depending on comp2
            -- 3) others, g = oldMantissa(bitsToShift - 1)
            if (bitsToShift = 0) then
                p3Res(3).g <= '0';
            elsif (bitsToShift > MANTISSA_BITS) then
                p3Res(3).g <= p2Res(2).comp2;
            else
                p3Res(3).g <= p2Res(2).mantissa(bitsToShift - 1);
            end if;

            -- r is the rounding bit, it's the second msb that
            -- was shifted out. 3 cases:
            -- 1) bitsToShift < 2, r = 0
            -- 2) bitsToShift > (MANTISSA_BITS + 1), r is comp2
            -- 3) others, r = oldMantissa(bitsToShift - 2)
            if (bitsToShift < 2) then
                p3Res(3).r <= '0';
            elsif (bitsToShift > (MANTISSA_BITS + 1)) then
                p3Res(3).r <= p2Res(2).comp2;
            else
                p3Res(3).r <= p2Res(2).mantissa(bitsToShift - 2);
            end if;

            -- s is the sticky bit, it's the reduction or of all
            -- shifted out bits after g and r. 3 cases:
            -- 1) bitsToShift < 3, s = 0
            -- 2) bitsToShift > (MANTISSA_BITS + 2),
            --    s = (|oldMantissa) | comp2
            -- 3) others, s = |oldMantissa((bitsToShift - 3)
            --                             downto 0)
            if (bitsToShift < 3) then
                p3Res(3).s <= '0';
            elsif (bitsToShift > (MANTISSA_BITS + 2)) then
                p3Res(3).s <= '1' when ((unsigned(p2Res(2).mantissa) /=
                                      to_unsigned(0, MANTISSA_BITS)) or
                                     p2Res(2).comp2 /= '0')
                           else '0';
            else
                p3Res(3).s <= '1' when (to_integer(unsigned(p2Res(2).mantissa
                                                ((bitsToShift - 3)
                                                downto 0))) /= 0)
                           else '0';
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 4
    -----------------------------------------------------------------
    -- 4) Compute the sum fpA.mantissa + fpB.mantissa including
    --    carray out. If comp2 and msb of sum is 1 and carray out
    --    is 0, then S = twosComplement(S)
    -----------------------------------------------------------------
    process (clk, rst)
        -- +1 for carry out
        variable sum: unsigned(MANTISSA_BITS downto 0);
    begin
        if (rst = '1') then
            -- do nothing
        elsif (rising_edge(clk)) then
            p1Res(4) <= p1Res(3);
            p2Res(4) <= p2Res(3);
            p3Res(4) <= p3Res(3);

            sum := ('0' & p3Res(3).shiftedMantissa) +
                   ('0' & unsigned(fpPkg.get_mantissa(p1Res(3).fpA)));

            p4Res(4).carryOut <= sum(MANTISSA_BITS);

            if ((p2Res(3).comp2 = '1') and          -- if the signs of the arguments differ
                (sum(MANTISSA_BITS - 1) = '1') and  -- and the msb of the sum is 1
                (sum(MANTISSA_BITS) = '0')) then    -- and there wasn't a carry out
                -- sum is negative, so get twos complement
                p4Res(4).sum <= (not sum((MANTISSA_BITS - 1) downto 0)) +
                                to_unsigned(1, MANTISSA_BITS);
                p4Res(4).comp2 <= true;
            else
                p4Res(4).sum <= sum((MANTISSA_BITS - 1) downto 0);
                p4Res(4).comp2 <= false;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 5)
    -----------------------------------------------------------------
    -- 5) shift the result of the sum until it is normalized
    --    and adjust the exponent
    -----------------------------------------------------------------
    process (clk, rst)
        variable first1:        integer := -1;
        variable bitsToShift:   integer;
    begin
        if (rst = '1') then
            -- do nothing
        elsif (rising_edge(clk)) then
            p1Res(5) <= p1Res(4);
            p2Res(5) <= p2Res(4);
            p3Res(5) <= p3Res(4);
            p4Res(5) <= p4Res(4);

            -- if the signs of the arguments are the same
            -- (not comp2), and there was a carry out
            if ((p2Res(4).comp2 = '0') and
                (p4Res(4).carryOut = '1')) then
                -- shift the result right by one
                -- filling in the new upper bit with carryOut
                p5Res(5).normalizedSum <= p4Res(4).carryOut &
                                          p4Res(4).sum((MANTISSA_BITS - 1)
                                                       downto 1);

                -- we shifted right by one -> /2
                -- so exponent should be +1
                p5Res(5).biasedExponent <= signed("00" & p1Res(4).fpA.biasedExponent) +
                                           to_signed(1, EXPONENT_BITS + 2);

                -- adjust r and s.
                --p5Res(5).r <= p4Res(4).sum(0);
                --p5Res(5).s <= p3Res(4).g or
                --              p3Res(4).r or
                --              p3Res(4).s;

            else

                -- shift left until normalized (ie. msb is 1)
                first1 := -1;
                for i in p4Res(4).sum'range loop
                    if (p4Res(4).sum(i) = '1') then
                        first1 := i;
                        exit;
                    end if;
                end loop;

                if (first1 = -1) then
                    -- all bits are 0, result is 0
                    p5Res(5).normalizedSum <= to_unsigned(0, MANTISSA_BITS);
                    -- exponent is 0
                    p5Res(5).biasedExponent <= to_signed(0, EXPONENT_BITS + 2);
                else
                    bitsToShift := MANTISSA_BITS - first1 - 1;
                    if (bitsToShift = 0) then
                        p5Res(5).normalizedSum <= p4Res(4).sum;
                    elsif (bitsToShift = 1) then
                        -- shifting 1 bit, just shift in g
                        p5Res(5).normalizedSum <= p4Res(4).sum(first1 downto 0) &
                                                  p3Res(4).g;
                    else
                        -- shifting more than 1 bit, shift in g then 0s
                        p5Res(5).normalizedSum <= p4Res(4).sum(first1 downto 0) &
                                                  p3Res(4).g &
                                                  to_unsigned(0, (bitsToShift - 1));
                    end if;

                    -- adjust the exponent.
                    -- we shifted left by bitsToShift bits
                    -- so we need to decrement the exponent by
                    -- bitsToShift
                    p5Res(5).biasedExponent <= signed("00" & p1Res(4).fpA.biasedExponent) -
                                               to_signed(bitsToShift, EXPONENT_BITS + 2);
                end if;
            end if;
        end if;
    end process;

    -----------------------------------------------------------------
    -- Pipeline stage 6)
    -----------------------------------------------------------------
    -- note steps 6 and 7 skipped for now
    -- 8) Compute the sign
    -----------------------------------------------------------------
    process (clk, rst)
        variable fpC:       fpPkg.fpType;
        variable newSign:   std_ulogic;
    begin
        if (rst = '1') then
            -- do nothing
        elsif (rising_edge(clk)) then
            -- compute the sign
            if (p2Res(5).comp2 = '0') then
                -- the signs of A and B are the same
                -- that's our sign
                newSign := p1Res(5).fpA.sign;
            elsif (p1Res(5).swap) then
                -- If we swapped the arguments, then the
                -- sign is the sign of B, except we stored the
                -- swapped arguments, so use sign of A
                newSign := p1Res(5).fpA.sign;
            elsif (p4Res(5).comp2) then
                -- If we complemented the result in step 4
                -- the the sign is the sign of B
                newSign := p1Res(5).fpB.sign;
            else
                -- otherwise we are the sign of A
                newSign := p1Res(5).fpA.sign;
            end if;

            -- result
            -- If either of the arguments is NaN
            -- the output should be NaN
            if (fpPkg.is_NaN(p1Res(5).fpA) or
                fpPkg.is_NaN(p1Res(5).fpB)) then
                fpC := fpPkg.set_NaN(newSign);

            -- If both of the inputs are zero with
            -- opposite signs then the +0
            elsif (fpPkg.is_zero(p1Res(5).fpA) and
                   fpPkg.is_zero(p1Res(5).fpB) and
                   p2Res(5).comp2 = '1') then
                fpC := fpPkg.set_zero('0');

            -- If both of the inputs are infinity with
            -- opposite signs then the result is NaN
            elsif (fpPkg.is_infinity(p1Res(5).fpA) and
                   fpPkg.is_infinity(p1Res(5).fpB) and
                   p2Res(5).comp2 = '1') then
                fpC := fpPkg.set_NaN(newSign);

            -- If either of the inputs is infinity then the
            -- result is infinity
            elsif (fpPkg.is_infinity(p1Res(5).fpA) or
                   fpPkg.is_infinity(p1Res(5).fpB)) then
                fpC := fpPkg.set_infinity(newSign);

            -- if one of the operands is 0 the result is the other
            elsif (fpPkg.is_zero(p1Res(5).fpA)) then
                fpC := p1Res(5).fpB;
            elsif (fpPkg.is_zero(p1Res(5).fpB)) then
                fpC := p1Res(5).fpA;

            -- if we overflowed then we are either infinity
            -- or max representatable depending on rounding mode
            elsif (to_integer(p5Res(5).biasedExponent) > fpPkg.EMAX) then
                -- If we round away from (newSign) inifinity,
                -- then the value saturates at the max
                -- representatable value = 1.111...111 * 2^EMAX
                -- if we round towards (newSign) infinity then
                -- the value is infinity
                -- if we round to nearest (ties even) then
                -- the max representatable number is odd (ends in 1)
                -- so we round to infinity
                if (roundingMode = RoundingMode_0) then
                    fpC := fpPkg.set_max(newSign);
                elsif ((roundingMode = RoundingMode_NEG_INF) and
                       (newSign = '0')) then
                    fpC := fpPkg.set_max(newSign);
                elsif ((roundingMode = RoundingMode_POS_INF) and
                       (newSign = '1')) then
                    fpC := fpPkg.set_max(newSign);
                else
                    fpC := fpPkg.set_infinity(newSign);
                end if;

            -- If we underflowed then the result is zero.
            -- Note: We don't handle denormals yet
            elsif (p5Res(5).biasedExponent < fpPkg.EMIN) then
                fpC := fpPkg.set_zero(newSign);

            -- Finally in all others cases the result is
            -- the calculated one
            else
                fpC.sign            := newSign;
                fpC.biasedExponent  := std_ulogic_vector(p5Res(5).biasedExponent((EXPONENT_BITS - 1) downto 0));
                fpC.significand     := std_ulogic_vector(p5Res(5).normalizedSum((SIGNIFICAND_BITS - 1) downto 0));
                fpC.representation  := fpPkg.fpRepresentation_NORMAL;
            end if;

            -- Convert the result to a vector
            outC <= fpPkg.fpType_to_vect(fpC);
        end if;
    end process;

end architecture synth;
