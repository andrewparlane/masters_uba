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

package fp_helper_pkg is

    generic (TOTAL_BITS:    natural := 32;
             EXPONENT_BITS: natural := 8);

    constant SIGNIFICAND_BITS:  natural
                                := TOTAL_BITS - EXPONENT_BITS - 1;

    -- EMIN = 00..001
    constant EMIN:  natural := 1;

    -- EMAX = 11..110
    constant EMAX:  natural := (2**EXPONENT_BITS) - 2;

    -- BIAS = 011..11
    constant BIAS:  natural := (2**(EXPONENT_BITS - 1)) - 1;

    type fpRepresentation is
    (
        fpRepresentation_NORMAL,
        fpRepresentation_ZERO,
        fpRepresentation_DENORMAL,
        fpRepresentation_NaN,
        fpRepresentation_INFINITY
    );

    type fpType is record
        sign:             std_ulogic;
        biasedExponent:   std_ulogic_vector((EXPONENT_BITS - 1) downto 0);
        significand:      std_ulogic_vector((SIGNIFICAND_BITS - 1) downto 0);
        representation:   fpRepresentation;
    end record fpType;

    function vect_to_fpType(vect: std_ulogic_vector((TOTAL_BITS - 1) downto 0)) return fpType;
    function fpType_to_vect(fp: fpType) return std_ulogic_vector;

    function is_NaN(fp: fpType) return boolean;
    function is_zero(fp: fpType) return boolean;
    function is_infinity(fp: fpType) return boolean;
    function is_denormal(fp: fpType) return boolean;

    function set_NaN(sign: std_ulogic) return fpType;
    function set_zero(sign: std_ulogic) return fpType;
    function set_infinity(sign: std_ulogic) return fpType;
    function set_max(sign: std_ulogic) return fpType;

    function get_unbiased_exponent(biasedExponent: std_ulogic_vector((EXPONENT_BITS - 1) downto 0)) return signed;

    function significand_to_string(significand: std_ulogic_vector((SIGNIFICAND_BITS - 1) downto 0)) return string;
    function exponent_to_string(biasedExponent: std_ulogic_vector((EXPONENT_BITS - 1) downto 0)) return string;
    function to_string(fp: fpType) return string;
end package fp_helper_pkg;

package body fp_helper_pkg is

    function vect_to_fpType(vect: std_ulogic_vector((TOTAL_BITS - 1) downto 0))
                            return fpType is
        variable fp:                fpType;
        variable representation:    fpRepresentation;
        variable sign:              std_ulogic;
        variable biasedExponent:    std_ulogic_vector((EXPONENT_BITS - 1) downto 0);
        variable significand:       std_ulogic_vector((SIGNIFICAND_BITS - 1) downto 0);
    begin

        sign            := vect(TOTAL_BITS - 1);
        biasedExponent  := vect((TOTAL_BITS - 2) downto SIGNIFICAND_BITS);
        significand     := vect((SIGNIFICAND_BITS - 1) downto 0);

        -- parse the representation:
        --   biasedExponent = EMIN - 1
        --     significand = 0 -> ZERO
        --     significand /= 0 -> DENORMAL
        --   biasedExponent = EMAX + 1
        --     significand = 0 -> INFINITY
        --     significand /= 0 -> NaN
        --   EMIN <= biasedExponent <= EMAX
        --     NORMAL

        if (to_integer(unsigned(biasedExponent)) = (EMIN - 1)) then
            if (significand = (significand'range => '0')) then
                representation := fpRepresentation_ZERO;
            else
                representation := fpRepresentation_DENORMAL;            end if;
        elsif (to_integer(unsigned(biasedExponent)) = (EMAX + 1)) then
            if (significand = (significand'range => '0')) then
                representation := fpRepresentation_INFINITY;
            else
                representation := fpRepresentation_NaN;
            end if;
        else
            representation := fpRepresentation_NORMAL;
        end if;

        fp := (sign => sign,
               biasedExponent => biasedExponent,
               significand => significand,
               representation => representation);

        return fp;
    end function vect_to_fpType;

    function fpType_to_vect(fp: fpType) return std_ulogic_vector is
    begin
        return fp.sign & fp.biasedExponent & fp.significand;
    end function fpType_to_vect;

    function is_NaN(fp: fpType) return boolean is
    begin
        return fp.representation = fpRepresentation_NaN;
    end function is_NaN;

    function is_zero(fp: fpType) return boolean is
    begin
        return fp.representation = fpRepresentation_ZERO;
    end function is_zero;

    function is_infinity(fp: fpType) return boolean is
    begin
        return fp.representation = fpRepresentation_INFINITY;
    end function is_infinity;

    function is_denormal(fp: fpType) return boolean is
    begin
        return fp.representation = fpRepresentation_DENORMAL;
    end function is_denormal;

    function set_NaN(sign: std_ulogic) return fpType is
        variable fp: fpType;
    begin
        fp := (sign => sign,
               biasedExponent => std_ulogic_vector(to_unsigned(EMAX + 1, EXPONENT_BITS)),
               significand => '1' & std_ulogic_vector(to_unsigned(0, SIGNIFICAND_BITS - 1)),
               representation => fpRepresentation_NaN);
        return fp;
    end function set_NaN;

    function set_zero(sign: std_ulogic) return fpType is
        variable fp: fpType;
    begin
        fp := (sign => sign,
               biasedExponent => std_ulogic_vector(to_unsigned(EMIN - 1, EXPONENT_BITS)),
               significand => std_ulogic_vector(to_unsigned(0, SIGNIFICAND_BITS)),
               representation => fpRepresentation_ZERO);
        return fp;
    end function set_zero;

    function set_infinity(sign: std_ulogic) return fpType is
        variable fp: fpType;
    begin
        fp := (sign => sign,
               biasedExponent => std_ulogic_vector(to_unsigned(EMAX + 1, EXPONENT_BITS)),
               significand => std_ulogic_vector(to_unsigned(0, SIGNIFICAND_BITS)),
               representation => fpRepresentation_INFINITY);
        return fp;
    end function set_infinity;

    function set_max(sign: std_ulogic) return fpType is
        variable fp: fpType;
    begin
        fp := (sign => sign,
               biasedExponent => std_ulogic_vector(to_unsigned(EMAX, EXPONENT_BITS)),
               significand => std_ulogic_vector(to_unsigned((2**SIGNIFICAND_BITS) - 1, SIGNIFICAND_BITS)),
               representation => fpRepresentation_NORMAL);
        return fp;
    end function set_max;

    function get_unbiased_exponent(biasedExponent: std_ulogic_vector((EXPONENT_BITS - 1) downto 0)) return signed is
    begin
        return signed("0" & biasedExponent) - BIAS;
    end function get_unbiased_exponent;

    function significand_to_string(significand: std_ulogic_vector((SIGNIFICAND_BITS - 1) downto 0)) return string is
        -- while (s > 0)
        -- {
        --     s *= 10;
        --     str[idx++] = '0' + (fracParts >> SIGNIFICAND_BITS);
        --     fracParts &= ((1 << SIGNIFICAND_BITS) - 1);
        -- }
        -- the &= limts us to SIGNIFICAND_BITS each time
        -- then we multiply by 10, so we only need
        -- SIGNIFICAND_BITS + 4
        variable s: unsigned((SIGNIFICAND_BITS + 3) downto 0)
                    := unsigned("0000" & significand);

        variable str: string(1 to SIGNIFICAND_BITS);
        variable idx: natural := 1;
    begin
        while s /= 0 loop
            s := resize(s * 10, s'length);

            str(idx to idx) := integer'image(to_integer(s((SIGNIFICAND_BITS + 3) downto SIGNIFICAND_BITS)));
            idx := idx + 1;

            s((SIGNIFICAND_BITS + 3) downto SIGNIFICAND_BITS)
                    := (others => '0');
        end loop;
        return str(1 to idx - 1);
    end function significand_to_string;

    function exponent_to_string(biasedExponent: std_ulogic_vector((EXPONENT_BITS - 1) downto 0)) return string is
    begin
        return integer'image(to_integer(get_unbiased_exponent(biasedExponent)));
    end function exponent_to_string;

    function to_string(fp: fpType) return string is
        variable signStr: string(1 to 1);
    begin
        signStr := "+" when fp.sign = '0' else "-";

        case (fp.representation) is
            when fpRepresentation_ZERO =>
                return signStr & "0";

            when fpRepresentation_DENORMAL =>
                return signStr &
                       "0." &
                       significand_to_string(fp.significand) &
                       " * 2^" &
                       exponent_to_string(std_ulogic_vector(to_unsigned(EMIN, EXPONENT_BITS)));

            when fpRepresentation_INFINITY =>
                return signStr & "inf";

            when fpRepresentation_NaN =>
                return "NaN";

            when others =>
                return signStr &
                       "1." &
                       significand_to_string(fp.significand) &
                       " * 2^" &
                       exponent_to_string(fp.biasedExponent);
        end case;
    end function to_string;

end package body fp_helper_pkg;
