library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.fp_type_pkg.all;

entity fp_round is
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
end entity fp_round;

architecture synth of fp_round is
    package fpPkg
            is new work.fp_helper_pkg
            generic map (TOTAL_BITS => TOTAL_BITS,
                         EXPONENT_BITS => EXPONENT_BITS);
begin
    process (all)
        variable useSignificandPlus1:   std_ulogic;
        -- +1 for carry outs
        variable sig:   unsigned(SIGNIFICAND_BITS downto 0);
        -- +2 for underflow / overflow
        variable bExp:  signed((EXPONENT_BITS+1) downto 0);
    begin
        -- Rounding, 4 cases:
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

        if (i_rm = RoundingMode_NEG_INF) then
            -- Only add one if we are negative and (i_r or i_s)
            useSignificandPlus1 := i_sign and (i_r or i_s);
        elsif (i_rm = RoundingMode_POS_INF) then
            -- Only add one if we are positive and (i_r or i_s)
            useSignificandPlus1 := (not i_sign) and
                                   (i_r or i_s);
        elsif (i_rm = RoundingMode_0) then
            -- never add one
            useSignificandPlus1 := '0';
        else --if (i_rm = RoundingMode_NEAREST) then
            -- we add one if we are greater than halfway (i_r and i_s)
            -- in the half way case (i_r and (not i_s)) we tie to even
            -- so add 1 if the lsb of the sig is 1 (odd)
            -- so: (i_r and i_s) or (i_r and (not i_s) and sig(0))
            useSignificandPlus1 := (i_r and i_sig(0)) or
                                   (i_r and i_s);
        end if;

        -- we use SIGNIFICAND_BITS + 1
        -- so we can catch overflows
        if (useSignificandPlus1 = '0') then
            sig := '0' & i_sig;
        else
            sig := ('0' & i_sig) +
                   to_unsigned(1, SIGNIFICAND_BITS+1);
        end if;

        -- check for carry out and shift right
        if (sig(SIGNIFICAND_BITS) = '1') then
            -- carry out, shift right by 1
            sig := '0' & sig(SIGNIFICAND_BITS downto 1);
            bExp := i_bExp + to_signed(1, EXPONENT_BITS + 2);
        else
            -- no carry out, so just set the biased exponent
            bExp := i_bExp;
        end if;

        -- check for underflow
        if (bExp < to_signed(fpPkg.EMIN, EXPONENT_BITS+2)) then
            o_sig <= (others => '0');
            o_bExp <= (others => '0');
            o_type <= fpNumType_NORMAL;

        -- check for overflow
        elsif (bExp > to_signed(fpPkg.EMAX, EXPONENT_BITS+2)) then
            -- If we round away from (i_sign) inifinity,
            -- then the value saturates at the max
            -- representatable value = 1.111...111 * 2^EMAX
            -- if we round towards (i_sign) infinity then
            -- the value is infinity
            -- if we round to nearest (ties even) then
            -- the max representatable number is odd (ends in 1)
            -- so we round to infinity
            if (i_rm = RoundingMode_0) then
                -- saturate at max representatable
                o_sig <= (others => '1');
                o_bExp <= to_unsigned(fpPkg.EMAX, EXPONENT_BITS);
                o_type <= fpNumType_NORMAL;
            elsif ((i_rm = RoundingMode_NEG_INF) and
                   (i_sign = '0')) then
                -- saturate at max representatable
                o_sig <= (others => '1');
                o_bExp <= to_unsigned(fpPkg.EMAX, EXPONENT_BITS);
                o_type <= fpNumType_INFINITY;
            elsif ((i_rm = RoundingMode_POS_INF) and
                   (i_sign = '1')) then
                -- saturate at max representatable
                o_sig <= (others => '1');
                o_bExp <= to_unsigned(fpPkg.EMAX, EXPONENT_BITS);
                o_type <= fpNumType_INFINITY;
            else -- (i_rm = RoundingMode_NEAREST) then
                -- infinity
                -- saturate at max representatable
                o_sig <= (others => '0');
                o_bExp <= (others => '1');
                o_type <= fpNumType_NORMAL;
            end if;
        else
            o_sig <= sig((SIGNIFICAND_BITS-1) downto 0);
            o_bExp <= unsigned(bExp((EXPONENT_BITS-1) downto 0));
            o_type <= fpNumType_NORMAL;
        end if;
    end process;
end architecture synth;
