#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <libgen.h>
#include <getopt.h>
#include <ctype.h>
#include <string.h>
#include <time.h>
#include <fenv.h>
#include <math.h>

#define MAJOR_VERSION   (0)
#define MINOR_VERSION   (1)

//#define DEBUG

// Qn.m - we require n+m = 32 bits
#define QM              (23)

// Max value (before cordics) is between -MAX.0 and +MAX.0
// so that after the cordics the max value should be ~225.0
#define MAX_VALUE       (29)

// num steps in the cordic
#define NUM_STEPS       (10)

static const struct option _gLongOptions[] =
{
    {"help",                no_argument,        0,          'h' },
    {"version",             no_argument,        0,          'V' },
    {"num_tests",           required_argument,  0,          'n' },
    {"3d",                  no_argument,        0,          '3' },
    {"report_max",          no_argument,        0,          'r' },
    {"output",              required_argument,  0,          'o' },
    {0,                     0,                  0,           0  }
};

typedef enum
{
    ArgumentType_ZERO = 0,
    ArgumentType_MIN,
    ArgumentType_MAX,
    ArgumentType_NORMAL,

    NUM_ARGUMENT_TYPES
} ArgumentType;

// How likely is each argument type?
static const uint32_t ARG_TYPE_ZERO_WEIGHT      = 1;
static const uint32_t ARG_TYPE_MIN_WEIGHT       = 1;
static const uint32_t ARG_TYPE_MAX_WEIGHT       = 1;
static const uint32_t ARG_TYPE_NORMAL_WEIGHT    = 50;

static uint32_t _gARG_TYPE_ZERO_IF_LESS_THAN;
static uint32_t _gARG_TYPE_MIN_IF_LESS_THAN;
static uint32_t _gARG_TYPE_MAX_IF_LESS_THAN;
static uint32_t _gARG_TYPE_NORMAL_IF_LESS_THAN;

static void usage(FILE *stream, const char *ourName)
{
    fprintf(stream,
           "Usage:\n"
           "  %s -h\n"
           "  %1$s -V\n"
           "  %1$s [options]\n"
           "Options:\n"
           "  -h, --help                Prints usage information.\n"
           "  -V, --version             Prints version information.\n"
           "  -n, --num_tests NUM       Number of tests to output.\n"
           "  -3, --3d                  Generate a 3D cordic test file.\n"
           "  -r, --report_max          Write the max calculated value to stdout.\n"
           "  -o, --output              Path to output file.\n"
           "\n"
           "Examples:\n"
           "  %1$s -n 10000 -3 -o -\n"
           "\n",
           ourName);
}

static uint32_t rand32()
{
    // rand() is only guaranteed to be 15 bits
    // so repeat 4 times
    return ((rand() & 0xff) <<  0) |
           ((rand() & 0xff) <<  8) |
           ((rand() & 0xff) << 16) |
           ((rand() & 0xff) << 24);
}

static ArgumentType generateArgType()
{
    ArgumentType argType;
    uint32_t argTypeRand = rand32() % _gARG_TYPE_NORMAL_IF_LESS_THAN;

    if (argTypeRand < _gARG_TYPE_ZERO_IF_LESS_THAN)
    {
        argType = ArgumentType_ZERO;
    }
    else if (argTypeRand < _gARG_TYPE_MIN_IF_LESS_THAN)
    {
        argType = ArgumentType_MIN;
    }
    else if (argTypeRand < _gARG_TYPE_MAX_IF_LESS_THAN)
    {
        argType = ArgumentType_MAX;
    }
    else
    {
        argType = ArgumentType_NORMAL;
    }

    return argType;
}

static int32_t generateArgument()
{
    // first what type of argument are we
    ArgumentType argType = generateArgType();

    int32_t arg;

    switch (argType)
    {
        case ArgumentType_ZERO:
        {
            arg = 0;
            break;
        }
        case ArgumentType_MIN:
        {
            arg = (-(MAX_VALUE)) << QM;
            break;
        }
        case ArgumentType_MAX:
        {
            arg = (MAX_VALUE) << QM;
            break;
        }
        case ArgumentType_NORMAL:
        {
            arg = (int32_t)(rand32() % ((((2 * (MAX_VALUE))+1) << QM)+1)) -
                  ((MAX_VALUE) << QM);
            break;
        }
    }

    return arg;
}

static uint32_t generateAngle()
{
    uint32_t arg = rand32() % (360 << QM);

    return arg;
}

int32_t getInverseTan(double v)
{
    double rads = atan(v);
    double degs = (rads * 180.0) / M_PI;

    degs = (degs * (pow(2.0, QM))) + 0.5;
    int32_t res = degs;
    return res;
}

void cordic2d(int32_t x, int32_t y, uint32_t alpha, int32_t *rotatedX, int32_t *rotatedY)
{
    // convert the angle to: -90.0 <= angle < 90.0
    int32_t z;
    if (alpha > (270 << QM))
    {
        z = (int32_t)alpha - (360 << QM);
    }
    else if (alpha > (90 << QM))
    {
        z = (int32_t)alpha - (180 << QM);
        x = -x;
        y = -y;
    }
    else
    {
        z = (int32_t)alpha;
    }

#ifdef DEBUG
    printf("start: %f, %f, %f\n",
           ((double)x) / pow(2.0, QM),
           ((double)y) / pow(2.0, QM),
           ((double)z) / pow(2.0, QM));
#endif

    for (int i = 0; i < NUM_STEPS; i++)
    {
        int32_t d = (z < 0) ? -1 : 1;

        int32_t newX = x - ((d*y) >> i);
        int32_t newY = y + ((d*x) >> i);
        z = z - d*getInverseTan(pow(2.0, -i));

        x = newX;
        y = newY;

#ifdef DEBUG
        printf("step %d: %f %f %f\n", i,
               ((double)x) / pow(2.0, QM),
               ((double)y) / pow(2.0, QM),
               ((double)z) / pow(2.0, QM));
#endif
    }

#ifdef DEBUG
    printf("results: %u %u %u\n", x, y, z);
#endif

    *rotatedX = x;
    *rotatedY = y;
}

int32_t applyCordicGain(int32_t val)
{
    static int32_t gain = 0;
    static double g;

    if (gain == 0)
    {
        g = 1.0;
        for (int i = 0; i < NUM_STEPS; i++)
        {
            g = g * sqrt(1.0 + pow(2.0, -2.0*i));
        }

        gain = (g * pow(2.0, QM)) + 0.5;
    }

#ifdef DEBUG
    printf("cordic gain: %f - %u\n", g, gain);
#endif
    int64_t tmp = (int64_t)gain * (int64_t)val;
    tmp >>= QM;

    return (int32_t)tmp;
}

void cordic3d(int32_t x, int32_t y, int32_t z,
              uint32_t alpha, uint32_t beta, uint32_t gamma,
              int32_t *rotatedX, int32_t *rotatedY, int32_t *rotatedZ)
{
#ifdef DEBUG
    printf("CORDIC XY\n");
#endif

    cordic2d(x, y, alpha, &x, &y);
    z = applyCordicGain(z);

#ifdef DEBUG
    printf("z with gain %u\n", z);

    printf("\nCORDIC YZ\n");
#endif

    cordic2d(y, z, beta, &y, &z);
    x = applyCordicGain(x);

#ifdef DEBUG
    printf("x with gain %u\n", x);

    printf("\nCORDIC ZX\n");
#endif

    cordic2d(z, x, gamma, &z, &x);
    y = applyCordicGain(y);

#ifdef DEBUG
    printf("y with gain %u\n", y);

    printf("\n\n");
#endif

    *rotatedX = x;
    *rotatedY = y;
    *rotatedZ = z;
}

static void generateTests(FILE *f, uint32_t num_tests, bool threeD, bool report_max)
{
    int32_t maxValueCalculated = 0;
    bool maxValWasNeg = false;

    for (uint32_t i = 0; i < num_tests; i++)
    {
        int32_t x      = generateArgument();
        int32_t y      = generateArgument();
        int32_t z      = generateArgument();
        uint32_t alpha  = generateAngle();
        uint32_t beta   = generateAngle();
        uint32_t gamma  = generateAngle();

        if (threeD)
        {
            int32_t rotatedX;
            int32_t rotatedY;
            int32_t rotatedZ;
            cordic3d(x, y, z, alpha, beta, gamma,
                     &rotatedX, &rotatedY, &rotatedZ);

            fprintf(f, "%u %u %u %u %u %u %u %u %u\n",
                    x, y, z, alpha, beta, gamma,
                    rotatedX, rotatedY, rotatedZ);


            if (abs(rotatedX) > maxValueCalculated)
            {
                maxValueCalculated = abs(rotatedX);
                maxValWasNeg = (rotatedX < 0);
            }
            if (abs(rotatedY) > maxValueCalculated)
            {
                maxValueCalculated = abs(rotatedY);
                maxValWasNeg = (rotatedY < 0);
            }
            if (abs(rotatedZ) > maxValueCalculated)
            {
                maxValueCalculated = abs(rotatedZ);
                maxValWasNeg = (rotatedZ < 0);
            }
        }
        else
        {
            int32_t rotatedX;
            int32_t rotatedY;
            cordic2d(x, y, alpha, &rotatedX, &rotatedY);

            fprintf(f, "%u %u %u %u %u\n",
                    x, y, alpha,
                    rotatedX, rotatedY);

            if (abs(rotatedX) > maxValueCalculated)
            {
                maxValueCalculated = abs(rotatedX);
                maxValWasNeg = (rotatedX < 0);
            }
            if (abs(rotatedY) > maxValueCalculated)
            {
                maxValueCalculated = abs(rotatedY);
                maxValWasNeg = (rotatedY < 0);
            }
        }
    }

    maxValueCalculated = maxValWasNeg ? -maxValueCalculated
                                      : maxValueCalculated;

    if (report_max)
    {
        printf("Max value calculated %u %f\n", maxValueCalculated,
              ((double)maxValueCalculated) / pow(2.0, QM));
    }
}

int main(int argc, char **argv)
{
    // Use argv[0] as the name of this application
    const char *ourName = basename(argv[0]);

    // number of test cases to generate.
    uint32_t num_tests = 5000;

    // 2d or 3d
    bool threeD = false;

    // report_max
    bool report_max = false;

    // if no output file is passed or - is pased, use stdout
    const char *outputFile = NULL;

    // initialise random number generator
    time_t t;
    srand((unsigned) time(&t));

    // clear errors
    opterr = 0;

    // parse options
    while (1)
    {
        int option_index = 0;
        int c = getopt_long(argc, argv, "hV3rn:o:", _gLongOptions, &option_index);

        if (c == -1)
        {
            // No more args
            break;
        }

        switch (c)
        {
            case 'h':
            {
                usage(stdout, ourName);
                // exit now
                return 0;
            }
            case 'V':
            {
                printf("%s: Version %u.%u\n", ourName, MAJOR_VERSION, MINOR_VERSION);
                // exit now
                return 0;
            }
            case 'n':
            {
                // number of test cases
                num_tests = strtoul(optarg, NULL, 10);
                if (num_tests == 0)
                {
                    fprintf(stderr, "The argument for '-n' must be an integer > 0.\n\n");
                    usage(stderr, ourName);
                    return 1;
                }
                break;
            }
            case '3':
            {
                threeD = true;
                break;
            }
            case 'r':
            {
                report_max = true;
                break;
            }
            case 'o':
            {
                // if the optarg is "-" it means stdout
                // in that case leave outputFile as NULL
                if (strcmp(optarg, "-") != 0)
                {
                    outputFile = optarg;
                }
                break;
            }
            case '?':
            {
                if ((optopt == 'o') ||
                    (optopt == 'n'))
                {
                    fprintf(stderr, "Option '-%c' requires an argument.\n\n", optopt);
                }
                else if (isprint(optopt))
                {
                    fprintf (stderr, "Unknown option '-%c'.\n\n", optopt);
                }
                else
                {
                    // Just show the usage()
                    fprintf(stderr, "???\n");
                }
                usage(stderr, ourName);
                return 1;
            }
            case 0:
            {
                // long option that doesn't have matching short
                // option, just ignore here.
                break;
            }
            default:
            {
                usage(stderr, ourName);
                return 1;
            }
        }
    }

    if (optind != argc)
    {
        fprintf(stderr, "Too many arguments passed\n\n");
        usage(stderr, ourName);
        return 1;
    }

    // set up weightings
    _gARG_TYPE_ZERO_IF_LESS_THAN      = ARG_TYPE_ZERO_WEIGHT;
    _gARG_TYPE_MIN_IF_LESS_THAN       = _gARG_TYPE_ZERO_IF_LESS_THAN + ARG_TYPE_MIN_WEIGHT;
    _gARG_TYPE_MAX_IF_LESS_THAN       = _gARG_TYPE_MIN_IF_LESS_THAN + ARG_TYPE_MAX_WEIGHT;
    _gARG_TYPE_NORMAL_IF_LESS_THAN    = _gARG_TYPE_MAX_IF_LESS_THAN + ARG_TYPE_NORMAL_WEIGHT;

    // open the output file
    FILE *f = stdout;
    if (outputFile != NULL)
    {
        f = fopen(outputFile, "w");
        if (f == NULL)
        {
            fprintf(stderr, "Failed to open %s for writing\n", outputFile);
            return 2;
        }
    }

    generateTests(f, num_tests, threeD, report_max);

    if (outputFile != NULL)
    {
        fclose(f);
    }

    return 0;
}
