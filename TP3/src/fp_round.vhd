library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.fp_type_pkg.all;

entity fp_round is
    generic (TBITS:     natural;
             EBITS:     natural;
             SBITS:     natural;
             DENORMALS: boolean);
    port (i_sig:    in  unsigned((SBITS - 1) downto 0);
          i_bExp:   in  signed((EBITS + 1) downto 0);
          i_sign:   in  std_ulogic;
          i_r:      in  std_ulogic;
          i_s:      in  std_ulogic;
          i_rm:     in  RoundingMode;
          o_sig:    out unsigned((SBITS - 1) downto 0);
          o_bExp:   out unsigned((EBITS - 1) downto 0);
          o_type:   out fpNumType);
end entity fp_round;

architecture synth of fp_round is
    package fpPkg
            is new work.fp_helper_pkg
            generic map (TBITS => TBITS,
                         EBITS => EBITS);
begin
    process (all)
        variable useSigP1:  std_ulogic;
        -- +1 for carry outs
        variable sig:       unsigned(SBITS downto 0);
        -- +2 for underflow / overflow
        variable bExp:      signed((EBITS+1) downto 0);
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
            useSigP1 := i_sign and (i_r or i_s);

        elsif (i_rm = RoundingMode_POS_INF) then
            -- Only add one if we are positive and (i_r or i_s)
            useSigP1 := (not i_sign) and
                        (i_r or i_s);

        elsif (i_rm = RoundingMode_0) then
            -- never add one
            useSigP1 := '0';

        else -- RoundingMode_NEAREST

            -- we add one if we are greater than halfway (i_r and i_s)
            -- in the half way case (i_r and (not i_s)) we tie to even
            -- so add 1 if the lsb of the sig is 1 (odd)
            -- so: (i_r and i_s) or (i_r and (not i_s) and sig(0))
            useSigP1 := (i_r and i_sig(0)) or
                        (i_r and i_s);

        end if;

        -- we use SBITS + 1, so we can catch overflows
        if (useSigP1 = '0') then
            sig := '0' & i_sig;
        else
            sig := ('0' & i_sig) + to_unsigned(1, SBITS+1);
        end if;

        -- check for carry out
        if (sig(SBITS) = '1') then
            -- carry out, shift right by 1
            sig := '0' & sig(SBITS downto 1);
            bExp := i_bExp + to_signed(1, EBITS + 2);
        else
            -- no carry out, so just set the biased exponent
            bExp := i_bExp;
        end if;

        -- check for underflow
        if (bExp < to_signed(fpPkg.EMIN, EBITS+2)) then
            o_sig <= (others => '0');
            o_bExp <= (others => '0');
            o_type <= fpNumType_ZERO;

        -- check for gradual underflow
        elsif ((bExp = to_signed(fpPkg.EMIN, EBITS+2)) and
               (sig(SBITS-1) = '0')) then
            if ((sig = to_unsigned(0, SBITS+1)) or
                (not DENORMALS)) then
                -- nothing left, so actual underflow
                o_sig <= (others => '0');
                o_bExp <= (others => '0');
                o_type <= fpNumType_ZERO;
            else
                -- denormal
                o_sig <= sig((SBITS-1) downto 0);
                o_bExp <= (others => '0');
                o_type <= fpNumType_DENORMAL;
            end if;

        -- check for overflow
        elsif (bExp > to_signed(fpPkg.EMAX, EBITS+2)) then
            -- If we round away from (i_sign) inifinity,
            -- then the value saturates at the max
            -- representatable value = 1.111...111 * 2^EMAX
            -- if we round towards (i_sign) infinity then
            -- the value is infinity
            -- if we round to nearest (ties even) then
            -- the max representatable number is odd (ends in 1)
            -- so we round to infinity
            if (((i_rm = RoundingMode_0)) or
                ((i_rm = RoundingMode_NEG_INF) and (i_sign = '0')) or
                ((i_rm = RoundingMode_POS_INF) and (i_sign = '1'))) then
                -- saturate at max representatable
                o_sig <= (others => '1');
                o_bExp <= to_unsigned(fpPkg.EMAX, EBITS);
                o_type <= fpNumType_INFINITY;
            else
                -- infinity
                o_sig <= (others => '0');
                o_bExp <= (others => '1');
                o_type <= fpNumType_NORMAL;
            end if;

        -- normal number
        else
            o_sig <= sig((SBITS-1) downto 0);
            o_bExp <= unsigned(bExp((EBITS-1) downto 0));
            o_type <= fpNumType_NORMAL;
        end if;
    end process;
end architecture synth;
