#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>

// The max value produced after the cordic is if a co-ordinate
// was max x,y,z. During the rotation it was rotated just into
// one value (x, y or z) with the others zero. Then there is
// the cordic gain of ~1.65^3 to take into account

// We want to display this on a screen at 640*480
// so lets require the final results to span a max range of 451
// or -225.0 to 225.0. Which is a multiplier of 225 from
// the initial -1.0 to 1.0.

// Once you remove the cordic gain from this you get ~50
// which is the length of the vector. Which is equal to:
// sqrt(x^2 + y^2 + z^2) or:
// sqrt(MAX^2 + MAX^2 + MAX^2) = 50
// MAX = ~29
#define MAX_VALUE       (29)

// Qn.m - we require n+m = 16 bits, and want as much precision
// as possible. since we need -29 to 29 as the integer part
// which is 6 bits, we send the data as Q6.10
#define QM              (10)

const char *COORD_PATH = "coords.txt";
const char *OUT_PATH = "out.bin";

uint16_t getFixed(double val)
{
    // the values in the file are between -1.0 and 1.0
    // We want values between -MAX_VALUE and MAX_VALUE
    // so multiply by MAX_VALUE
    val *= MAX_VALUE;

    // we want to get the value in Qn.m format
    // so multiply by 2^QM and then add 0.5 (for rounding)
    val = (val * (pow(2.0, QM))) + 0.5;
    uint16_t fix = (uint16_t)val;

    return fix;
}

void main(void)
{
    FILE *coordFile = fopen(COORD_PATH, "r");
    if (!coordFile)
    {
        printf("Failed to open %s\n", COORD_PATH);
        return;
    }

    FILE *outFile = fopen(OUT_PATH, "wb");
    if (!coordFile)
    {
        printf("Failed to open %s\n", OUT_PATH);
        return;
    }

    uint16_t lines;
    while (1)
    {
        double x,y,z;
        if (fscanf(coordFile, "%lf\t%lf\t%lf", &x, &y, &z) != 3)
        {
            printf("Found %u lines (coordinates)\n", lines);
            break;
        }
        lines++;
    }

    // go back to the beginning of the input file
    fseek(coordFile, 0, SEEK_SET);
    // Write the number of lines to the output file
    // as 16 bits little endien
    fwrite(&lines, 2, 1, outFile);

    while (1)
    {
        double x,y,z;
        if (fscanf(coordFile, "%lf\t%lf\t%lf", &x, &y, &z) != 3)
        {
            printf("done\n");
            break;
        }

        uint16_t xfix = getFixed(x);
        uint16_t yfix = getFixed(y);
        uint16_t zfix = getFixed(z);

        fwrite(&xfix, 2, 1, outFile);
        fwrite(&yfix, 2, 1, outFile);
        fwrite(&zfix, 2, 1, outFile);
    }

    fclose(outFile);
    fclose(coordFile);
}