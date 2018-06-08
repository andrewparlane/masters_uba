library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

use work.fp_type_pkg.all;

-- A floating point number is represented in a vector as:
-- sign 1 bit, 0 = +ve, 1 = -ve.
-- exponent E bits
--   The exponent is biased by 2^(E-1) - 1
--   so if E was 4 bits, the bias would be 7
--   The exponent represented for bits xxxx
--   is signed(unsigned(xxxx) - bias)
-- significand S bits
--   The leading bit is hidden and is not contained in the
--   packed data. It is a 1 for normal numbers and a 0 for
--   denormal numbers and 0s

package fp_helper_pkg is

    generic (TOTAL_BITS:    natural := 32;
             EXPONENT_BITS: natural := 8);

    -- TOTAL_BITS = EXPONENT_BITS + (SIGNIFICAND_BITS-1) + SIGN_BIT
    constant SIGNIFICAND_BITS:  natural := TOTAL_BITS -
                                           EXPONENT_BITS;

    -- EMIN = 00..001
    constant EMIN:  natural := 1;

    -- EMAX = 11..110
    constant EMAX:  natural := (2**EXPONENT_BITS) - 2;

    -- BIAS = 011..11
    constant BIAS:  natural := (2**(EXPONENT_BITS - 1)) - 1;

    type fpUnpacked is record
        sign:           std_ulogic;
        biasedExponent: unsigned((EXPONENT_BITS - 1) downto 0);
        significand:    unsigned((SIGNIFICAND_BITS - 1) downto 0);
        numType:        fpNumType;
    end record fpUnpacked;

    function unpack(vect: std_ulogic_vector((TOTAL_BITS - 1) downto 0)) return fpUnpacked;
    function pack(fp: fpUnpacked) return std_ulogic_vector;

    function is_NaN(fp: fpUnpacked) return boolean;
    function is_zero(fp: fpUnpacked) return boolean;
    function is_infinity(fp: fpUnpacked) return boolean;
    function is_denormal(fp: fpUnpacked) return boolean;

    function set_NaN(sign: std_ulogic) return fpUnpacked;
    function set_zero(sign: std_ulogic) return fpUnpacked;
    function set_infinity(sign: std_ulogic) return fpUnpacked;
    function set_max(sign: std_ulogic) return fpUnpacked;

    function get_packed_biased_exponent(fp: fpUnpacked) return unsigned;
    function get_unbiased_exponent(fp: fpUnpacked) return signed;

    function significand_to_string(fp: fpUnpacked) return string;
    function exponent_to_string(fp: fpUnpacked) return string;
    function to_string(fp: fpUnpacked) return string;
end package fp_helper_pkg;

package body fp_helper_pkg is

    function unpack(vect: std_ulogic_vector((TOTAL_BITS - 1) downto 0))
                            return fpUnpacked is
        variable fp:                fpUnpacked;
        variable numType:           fpNumType;
        variable sign:              std_ulogic;
        variable biasedExponent:    unsigned((EXPONENT_BITS - 1) downto 0);
        variable significand:       unsigned((SIGNIFICAND_BITS - 1) downto 0);
    begin

        -- The sign is the MSb
        sign            := vect(TOTAL_BITS - 1);

        -- Then the exponent
        biasedExponent  := unsigned(vect((TOTAL_BITS - 2) downto (SIGNIFICAND_BITS - 1)));

        -- Then all except the implicit hidden bit
        -- of the significand. We add the implicit bit in
        -- as a 1 here. It gets changed to a 0 later,
        -- if we are a denormal or zero.
        significand     := '1' & unsigned(vect((SIGNIFICAND_BITS - 2) downto 0));

        -- parse the type:
        --   biasedExponent = EMIN - 1
        --     significand = 0 -> ZERO
        --     significand /= 0 -> DENORMAL
        --   biasedExponent = EMAX + 1
        --     significand = 0 -> INFINITY
        --     significand /= 0 -> NaN
        --   EMIN <= biasedExponent <= EMAX
        --     NORMAL

        if (to_integer(biasedExponent) = (EMIN - 1)) then
            if (significand((SIGNIFICAND_BITS-2) downto 0) =
                to_unsigned(0, SIGNIFICAND_BITS-1)) then
                numType := fpNumType_ZERO;
                -- store the exponent as 0
                -- biased exponent = BIAS
                --biasedExponent := to_unsigned(BIAS, EXPONENT_BITS);
            else
                numType := fpNumType_DENORMAL;
                -- store the biased exponent as EMIN
                biasedExponent := to_unsigned(EMIN, EXPONENT_BITS);
            end if;
            -- The implicit hidden bit of the significand is '0'
            significand(SIGNIFICAND_BITS-1) := '0';
        elsif (to_integer(biasedExponent) = (EMAX + 1)) then
            if (significand((SIGNIFICAND_BITS-2) downto 0) =
                to_unsigned(0, SIGNIFICAND_BITS-1)) then
                numType := fpNumType_INFINITY;
            else
                numType := fpNumType_NaN;
            end if;
        else
            numType := fpNumType_NORMAL;
        end if;

        fp := (sign => sign,
               biasedExponent => biasedExponent,
               significand => significand,
               numType => numType);

        return fp;
    end function unpack;

    function pack(fp: fpUnpacked) return std_ulogic_vector is
    begin
        return fp.sign &
               std_ulogic_vector(get_packed_biased_exponent(fp)) &
               std_ulogic_vector(fp.significand((SIGNIFICAND_BITS-2) downto 0));
    end function pack;

    function is_NaN(fp: fpUnpacked) return boolean is
    begin
        return fp.numType = fpNumType_NaN;
    end function is_NaN;

    function is_zero(fp: fpUnpacked) return boolean is
    begin
        return fp.numType = fpNumType_ZERO;
    end function is_zero;

    function is_infinity(fp: fpUnpacked) return boolean is
    begin
        return fp.numType = fpNumType_INFINITY;
    end function is_infinity;

    function is_denormal(fp: fpUnpacked) return boolean is
    begin
        return fp.numType = fpNumType_DENORMAL;
    end function is_denormal;

    function set_NaN(sign: std_ulogic) return fpUnpacked is
        variable fp: fpUnpacked;
    begin
        fp := (sign => sign,
               biasedExponent => to_unsigned(EMAX + 1, EXPONENT_BITS),
               significand => "11" & to_unsigned(0, SIGNIFICAND_BITS - 2),
               numType => fpNumType_NaN);
        return fp;
    end function set_NaN;

    function set_zero(sign: std_ulogic) return fpUnpacked is
        variable fp: fpUnpacked;
    begin
        fp := (sign => sign,
               biasedExponent => to_unsigned(BIAS, EXPONENT_BITS),
               significand => to_unsigned(0, SIGNIFICAND_BITS),
               numType => fpNumType_ZERO);
        return fp;
    end function set_zero;

    function set_infinity(sign: std_ulogic) return fpUnpacked is
        variable fp: fpUnpacked;
    begin
        fp := (sign => sign,
               biasedExponent => to_unsigned(EMAX + 1, EXPONENT_BITS),
               significand => '1' & to_unsigned(0, SIGNIFICAND_BITS-1),
               numType => fpNumType_INFINITY);
        return fp;
    end function set_infinity;

    function set_max(sign: std_ulogic) return fpUnpacked is
        variable fp: fpUnpacked;
    begin
        fp := (sign => sign,
               biasedExponent => to_unsigned(EMAX, EXPONENT_BITS),
               significand => to_unsigned((2**SIGNIFICAND_BITS) - 1, SIGNIFICAND_BITS),
               numType => fpNumType_NORMAL);
        return fp;
    end function set_max;

    function get_packed_biased_exponent(fp: fpUnpacked) return unsigned is
    begin
        if ((fp.numType = fpNumType_ZERO) or
            (fp.numType = fpNumType_DENORMAL)) then
            return to_unsigned(0, EXPONENT_BITS);
        else
            return fp.biasedExponent((EXPONENT_BITS-1) downto 0);
        end if;
    end function get_packed_biased_exponent;

    function get_unbiased_exponent(fp: fpUnpacked) return signed is
    begin
        if (fp.numType = fpNumType_ZERO) then
            return to_signed(0, EXPONENT_BITS);
        else
            return signed(fp.biasedExponent) -
                   to_signed(BIAS, EXPONENT_BITS);
        end if;
    end function get_unbiased_exponent;

    function significand_to_string(fp: fpUnpacked) return string is
        -- while (s > 0)
        -- {
        --     s *= 10;
        --     str[idx++] = '0' + (fracParts >> (SIGNIFICAND_BITS-1));
        --     fracParts &= ((1 << SIGNIFICAND_BITS) - 1);
        -- }
        -- the &= limts us to (SIGNIFICAND_BITS-1) each time
        -- then we multiply by 10, so we only need
        -- SIGNIFICAND_BITS + 3
        variable s: unsigned((SIGNIFICAND_BITS + 2) downto 0)
                    := unsigned("0000" & fp.significand((SIGNIFICAND_BITS-2) downto 0));

        -- +2 for 1. or 0.
        variable str: string(1 to (SIGNIFICAND_BITS+2));
        variable idx: natural;
    begin
        if (is_denormal(fp) or is_zero(fp)) then
            str(1 to 1) := "0";
        else
            str(1 to 1) := "1";
        end if;
        str(2 to 2) := ".";

        idx := 3;
        while s /= 0 loop
            s := resize(s * 10, s'length);

            str(idx to idx) := integer'image(to_integer(s((SIGNIFICAND_BITS + 2) downto SIGNIFICAND_BITS-1)));
            idx := idx + 1;

            s((SIGNIFICAND_BITS + 2) downto SIGNIFICAND_BITS-1)
                    := (others => '0');
        end loop;
        return str(1 to idx - 1);
    end function significand_to_string;

    function exponent_to_string(fp: fpUnpacked) return string is
    begin
        return integer'image(to_integer(get_unbiased_exponent(fp)));
    end function exponent_to_string;

    function to_string(fp: fpUnpacked) return string is
        variable signStr: string(1 to 1);
    begin
        signStr := "+" when fp.sign = '0' else "-";

        if (fp.numType = fpNumType_ZERO) then
            return signStr & "0";
        elsif (fp.numType = fpNumType_INFINITY) then
            return signStr & "inf";
        elsif (fp.numType = fpNumType_NaN) then
            return "NaN";
        else
            return signStr &
                   significand_to_string(fp) &
                   " * 2^" &
                   exponent_to_string(fp);
        end if;
    end function to_string;

end package body fp_helper_pkg;
