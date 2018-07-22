library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package char_rom_pkg is

    type charRomCharacter is
        (' ',  -- 0
         '!',  -- 1
         '"',  -- 2
         '#',  -- 3
         '$',  -- 4
         '%',  -- 5
         '&',  -- 6
         ''',  -- 7
         '(',  -- 8
         ')',  -- 9
         '*',  -- 10
         '+',  -- 11
         ',',  -- 12
         '-',  -- 13
         '.',  -- 14
         '/',  -- 15
         '0',  -- 16
         '1',  -- 17
         '2',  -- 18
         '3',  -- 19
         '4',  -- 20
         '5',  -- 21
         '6',  -- 22
         '7',  -- 23
         '8',  -- 24
         '9',  -- 25
         ':',  -- 26
         ';',  -- 27
         '<',  -- 28
         '=',  -- 29
         '>',  -- 30
         '?',  -- 31
         '@',  -- 32
         'A',  -- 33
         'B',  -- 34
         'C',  -- 35
         'D',  -- 36
         'E',  -- 37
         'F',  -- 38
         'G',  -- 39
         'H',  -- 40
         'I',  -- 41
         'J',  -- 42
         'K',  -- 43
         'L',  -- 44
         'M',  -- 45
         'N',  -- 46
         'O',  -- 47
         'P',  -- 48
         'Q',  -- 49
         'R',  -- 50
         'S',  -- 51
         'T',  -- 52
         'U',  -- 53
         'V',  -- 54
         'W',  -- 55
         'X',  -- 56
         'Y',  -- 57
         'Z',  -- 58
         '[',  -- 59
         '\',  -- 60
         ']',  -- 61
         '^',  -- 62
         '_',  -- 63
         '`',  -- 64
         'a',  -- 65
         'b',  -- 66
         'c',  -- 67
         'd',  -- 68
         'e',  -- 69
         'f',  -- 70
         'g',  -- 71
         'h',  -- 72
         'i',  -- 73
         'j',  -- 74
         'k',  -- 75
         'l',  -- 76
         'm',  -- 77
         'n',  -- 78
         'o',  -- 79
         'p',  -- 80
         'q',  -- 81
         'r',  -- 82
         's',  -- 83
         't',  -- 84
         'u',  -- 85
         'v',  -- 86
         'w',  -- 87
         'x',  -- 88
         'y',  -- 89
         'z',  -- 90
         '{',  -- 91
         '|',  -- 92
         '}',  -- 93
         '~'); -- 94

    function bcdToCharacter (bcd: unsigned(3 downto 0)) return charRomCharacter;

end package char_rom_pkg;

package body char_rom_pkg is

    function bcdToCharacter (bcd: unsigned(3 downto 0)) return charRomCharacter is
    begin
        case to_integer(bcd) is
            when 0 => return '0';
            when 1 => return '1';
            when 2 => return '2';
            when 3 => return '3';
            when 4 => return '4';
            when 5 => return '5';
            when 6 => return '6';
            when 7 => return '7';
            when 8 => return '8';
            when 9 => return '9';
            when others => return ' ';
        end case;
    end function bcdToCharacter;

end package body char_rom_pkg;
