library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

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

    -- maximums set to support IEE 754 double precision
    constant MAX_TBITS: natural := 64;
    constant MAX_EBITS: natural := 11;
    constant MAX_SBITS: natural := 53;

    type fpNumType is
    (
        fpNumType_NORMAL,
        fpNumType_ZERO,
        fpNumType_DENORMAL,
        fpNumType_NaN,
        fpNumType_INFINITY
    );

    type fpUnpacked is record
        sign:       std_ulogic;
        bExp:       unsigned((MAX_EBITS - 1) downto 0);
        sig:        unsigned((MAX_SBITS - 1) downto 0);
        numType:    fpNumType;

        emin:       natural;
        emax:       natural;
        bias:       natural;
    end record fpUnpacked;

    type RoundingMode is
    (
        RoundingMode_NEG_INF,
        RoundingMode_POS_INF,
        RoundingMode_0,
        RoundingMode_NEAREST
    );

    function unpack(vect:  std_ulogic_vector; tbits: natural; ebits: natural) return fpUnpacked;
    function pack(fp: fpUnpacked; tbits: natural; ebits: natural) return std_ulogic_vector;

    function get_sig(fp: fpUnpacked; sbits: natural) return unsigned;
    function get_bExp(fp: fpUnpacked; ebits: natural) return unsigned;

    function get_sbits(tbits: natural; ebits: natural) return natural;
    function get_emin return natural;
    function get_emax(ebits: natural) return natural;
    function get_bias(ebits: natural) return natural;

    function is_NaN(fp: fpUnpacked) return boolean;
    function is_zero(fp: fpUnpacked) return boolean;
    function is_infinity(fp: fpUnpacked) return boolean;
    function is_denormal(fp: fpUnpacked) return boolean;

    function set_NaN(sign: std_ulogic; tbits: natural; ebits: natural) return fpUnpacked;
    function set_zero(sign: std_ulogic; tbits: natural; ebits: natural) return fpUnpacked;
    function set_infinity(sign: std_ulogic; tbits: natural; ebits: natural) return fpUnpacked;
    function set_max(sign: std_ulogic; tbits: natural; ebits: natural) return fpUnpacked;

    function get_packed_biased_exponent(fp: fpUnpacked; ebits: natural) return unsigned;
    function get_unbiased_exponent(fp: fpUnpacked; ebits: natural) return signed;

    function significand_to_string(fp: fpUnpacked; sbits: natural) return string;
    function exponent_to_string(fp: fpUnpacked; ebits: natural) return string;
    function to_string(fp: fpUnpacked; tbits: natural; ebits: natural) return string;
end package fp_helper_pkg;

package body fp_helper_pkg is

    function unpack(vect:  std_ulogic_vector; tbits: natural; ebits: natural) return fpUnpacked is
        variable fp:        fpUnpacked;
        variable sbits:     natural;
    begin

        -- All these should be constant at compile time
        -- should should be optimized, and not require
        -- any resources.
        sbits    := get_sbits(tbits, ebits);
        fp.emin  := get_emin;
        fp.emax  := get_emax(ebits);
        fp.bias  := get_bias(ebits);

        -- The sign is the MSb
        fp.sign := vect(tbits - 1);

        -- Then the exponent
        fp.bExp := resize(unsigned(vect((tbits - 2)
                                   downto
                                   (sbits - 1))),
                          MAX_EBITS);

        -- Then all except the implicit hidden bit
        -- of the significand. We add the implicit bit in
        -- as a 1 here. It gets changed to a 0 later,
        -- if we are a denormal or zero.
        fp.sig := resize('1' & unsigned(vect((sbits - 2)
                                        downto 0)),
                         MAX_SBITS);

        -- parse the type:
        --   biasedExponent = EMIN - 1
        --     significand = 0 -> ZERO
        --     significand /= 0 -> DENORMAL
        --   biasedExponent = EMAX + 1
        --     significand = 0 -> INFINITY
        --     significand /= 0 -> NaN
        --   EMIN <= biasedExponent <= EMAX
        --     NORMAL

        if (to_integer(fp.bExp) = (fp.emin - 1)) then
            if (fp.sig((sbits-2) downto 0) = to_unsigned(0, sbits-1)) then
                fp.numType := fpNumType_ZERO;
            else
                fp.numType := fpNumType_DENORMAL;
                -- store the biased exponent as EMIN
                fp.bExp := to_unsigned(fp.emin, MAX_EBITS);
            end if;
            -- The implicit hidden bit of the significand is '0'
            fp.sig(sbits-1) := '0';
        elsif (to_integer(fp.bExp) = (fp.emax + 1)) then

            if (fp.sig((sbits-2) downto 0) =
                to_unsigned(0, sbits-1)) then
                fp.numType := fpNumType_INFINITY;
            else
                fp.numType := fpNumType_NaN;
            end if;
        else

            fp.numType := fpNumType_NORMAL;
        end if;

        return fp;
    end function unpack;

    function pack(fp: fpUnpacked; tbits: natural; ebits: natural) return std_ulogic_vector is
    begin
        return fp.sign &
               std_ulogic_vector(get_packed_biased_exponent(fp, ebits)) &
               std_ulogic_vector(fp.sig((get_sbits(tbits, ebits)-2) downto 0));
    end function pack;

    function get_sig(fp: fpUnpacked; sbits: natural) return unsigned is
    begin
        return fp.sig(sbits-1 downto 0);
    end function get_sig;

    function get_bExp(fp: fpUnpacked; ebits: natural) return unsigned is
    begin
        return fp.bExp(ebits-1 downto 0);
    end function get_bExp;

    function get_sbits(tbits: natural; ebits: natural) return natural is
    begin
        -- note this is the number of bits in the actual significand
        -- not in the packed version
        return tbits - ebits;
    end function get_sbits;

    function get_emin return natural is
    begin
        return 1; -- it's always 1
    end function get_emin;

    function get_emax(ebits: natural) return natural is
    begin
        -- EMAX = 11..110
        return (2**ebits) - 2;
    end function get_emax;

    function get_bias(ebits: natural) return natural is
    begin
        -- BIAS = 011..11
        return (2**(ebits - 1)) - 1;
    end function get_bias;

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

    function set_NaN(sign: std_ulogic; tbits: natural; ebits: natural) return fpUnpacked is
        variable fp: fpUnpacked;
    begin
        fp := (emin     => get_emin,
               emax     => get_emax(ebits),
               bias     => get_bias(ebits),
               sign     => sign,
               bExp     => to_unsigned(get_emax(ebits) + 1, MAX_EBITS),
               sig      => resize("11" & to_unsigned(0, get_sbits(tbits, ebits) - 2), MAX_SBITS),
               numType  => fpNumType_NaN);
        return fp;
    end function set_NaN;

    function set_zero(sign: std_ulogic; tbits: natural; ebits: natural) return fpUnpacked is
        variable fp: fpUnpacked;
    begin
        fp := (emin     => get_emin,
               emax     => get_emax(ebits),
               bias     => get_bias(ebits),
               sign     => sign,
               bExp     => to_unsigned(get_bias(ebits), MAX_EBITS),
               sig      => to_unsigned(0, MAX_SBITS),
               numType  => fpNumType_ZERO);
        return fp;
    end function set_zero;

    function set_infinity(sign: std_ulogic; tbits: natural; ebits: natural) return fpUnpacked is
        variable fp: fpUnpacked;
    begin
        fp := (emin     => get_emin,
               emax     => get_emax(ebits),
               bias     => get_bias(ebits),
               sign     => sign,
               bExp     => to_unsigned(get_emax(ebits) + 1, MAX_EBITS),
               sig      => resize('1' & to_unsigned(0, get_sbits(tbits, ebits) - 1), MAX_SBITS),
               numType  => fpNumType_INFINITY);
        return fp;
    end function set_infinity;

    function set_max(sign: std_ulogic; tbits: natural; ebits: natural) return fpUnpacked is
        variable fp: fpUnpacked;
    begin
        fp := (emin     => get_emin,
               emax     => get_emax(ebits),
               bias     => get_bias(ebits),
               sign     => sign,
               bExp     => to_unsigned(get_emax(ebits), MAX_EBITS),
               sig      => to_unsigned((2**get_sbits(tbits, ebits)) - 1, MAX_SBITS),
               numType  => fpNumType_NORMAL);
        return fp;
    end function set_max;

    function get_packed_biased_exponent(fp: fpUnpacked; ebits: natural) return unsigned is
    begin
        if ((fp.numType = fpNumType_ZERO) or
            (fp.numType = fpNumType_DENORMAL)) then
            return to_unsigned(0, ebits);
        else
            return fp.bExp((ebits-1) downto 0);
        end if;
    end function get_packed_biased_exponent;

    function get_unbiased_exponent(fp: fpUnpacked; ebits: natural) return signed is
    begin
        if (fp.numType = fpNumType_ZERO) then
            return to_signed(0, ebits);
        else
            return signed(fp.bExp) -
                   to_signed(fp.bias, ebits);
        end if;
    end function get_unbiased_exponent;

    function significand_to_string(fp: fpUnpacked; sbits: natural) return string is
        -- while (s > 0)
        -- {
        --     s *= 10;
        --     str[idx++] = '0' + (fracParts >> (SBITS-1));
        --     fracParts &= ((1 << SBITS) - 1);
        -- }
        -- the &= limts us to (SBITS-1) each time
        -- then we multiply by 10, so we only need
        -- SBITS + 3
        variable s: unsigned((sbits + 2) downto 0)
                    := unsigned("0000" & fp.sig((sbits-2) downto 0));

        -- +2 for 1. or 0.
        variable str: string(1 to (sbits+2));
        variable idx: natural;
    begin
        if (is_denormal(fp) or is_zero(fp)) then
            str(1 to 1) := "0";
        else
            str(1 to 1) := "1";
        end if;
        str(2 to 2) := ".";

        if (s = 0) then
            str(3 to 3) := "0";
            idx := 4;
        else
            idx := 3;
            while s /= 0 loop
                s := resize(s * 10, s'length);

                str(idx to idx) := integer'image(to_integer(s((sbits + 2) downto sbits-1)));
                idx := idx + 1;

                s((sbits + 2) downto sbits-1)
                        := (others => '0');
            end loop;
        end if;
        return str(1 to idx - 1);
    end function significand_to_string;

    function exponent_to_string(fp: fpUnpacked; ebits: natural) return string is
    begin
        return integer'image(to_integer(get_unbiased_exponent(fp, ebits)));
    end function exponent_to_string;

    function to_string(fp: fpUnpacked; tbits: natural; ebits: natural) return string is
        variable signStr: string(1 to 1);
    begin
        if (fp.sign = '0') then
            signStr := "+";
        else
            signStr := "-";
        end if;

        if (fp.numType = fpNumType_ZERO) then
            return signStr & "0";
        elsif (fp.numType = fpNumType_INFINITY) then
            return signStr & "inf";
        elsif (fp.numType = fpNumType_NaN) then
            return "NaN";
        else
            return signStr &
                   significand_to_string(fp, get_sbits(tbits, ebits)) &
                   " * 2^" &
                   exponent_to_string(fp, ebits);
        end if;
    end function to_string;

end package body fp_helper_pkg;
