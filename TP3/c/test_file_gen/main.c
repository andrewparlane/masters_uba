#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <libgen.h>
#include <getopt.h>
#include <ctype.h>
#include <string.h>
#include <time.h>

#define MAJOR_VERSION   (0)
#define MINOR_VERSION   (1)

//#define DEBUG

#define SIGN_MASK           (0x80000000)
#define EXPONENT_MASK       (0x7F800000)
#define SIGNIFICAND_MASK    (~((EXPONENT_MASK) | (SIGN_MASK)))

#warning TODO add options for operation type
#warning TODO add options for size
#warning TODO add options for rounding mode
// see fesetround()

static const struct option _gLongOptions[] =
{
    {"help",        no_argument,        0, 'h' },
    {"version",     no_argument,        0, 'V' },
    {"num_tests",   required_argument,  0, 'n' },
    {"no_denormal", no_argument,        0, 'd' },
    {"output",      required_argument,  0, 'o' },
    {0,             0,                  0,  0  }
};

typedef enum
{
    ArgumentType_ZERO = 0,
    ArgumentType_NaN,
    ArgumentType_INF,
    ArgumentType_DENORMAL,
    ArgumentType_NORMAL,

    NUM_ARGUMENT_TYPES
} ArgumentType;


// How likely is each argument type?
static const uint32_t ARG_TYPE_ZERO_WEIGHT      = 1;
static const uint32_t ARG_TYPE_NaN_WEIGHT       = 1;
static const uint32_t ARG_TYPE_INF_WEIGHT       = 1;
static const uint32_t ARG_TYPE_DENORMAL_WEIGHT  = 2;
static const uint32_t ARG_TYPE_NORMAL_WEIGHT    = 5;

static uint32_t _gARG_TYPE_ZERO_IF_LESS_THAN;
static uint32_t _gARG_TYPE_NaN_IF_LESS_THAN;
static uint32_t _gARG_TYPE_INF_IF_LESS_THAN;
static uint32_t _gARG_TYPE_DENORMAL_IF_LESS_THAN;
static uint32_t _gARG_TYPE_NORMAL_IF_LESS_THAN;

static bool     _gNoDenormals = false;

static void usage(FILE *stream, const char *ourName)
{
    fprintf(stream,
           "Usage:\n"
           "  %1$s -h\n"
           "  %1$s -V\n"
           "  %1$s [options]\n"
           "Options:\n"
           "  -h, --help Prints usage information.\n"
           "  -V, --version Prints version information.\n"
           "  -n, --num_tests Number of tests to output.\n"
           "  -d, --no_denormal Don't include denormals.\n"
           "  -o, --output Path to output file.\n"
           "\n"
           "Examples:\n"
           "  %1$s -n 10000 -o -\n"
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

#ifdef DEBUG
static const char *getArgString(ArgumentType argType)
{
    switch (argType)
    {
        case ArgumentType_ZERO:         return "zero";
        case ArgumentType_NaN:          return "NaN";
        case ArgumentType_INF:          return "infinity";
        case ArgumentType_DENORMAL:     return "denormal";
        case ArgumentType_NORMAL:       return "normal";
        default:                        return "unknown";
    }
}
#endif

static uint32_t generateArgument()
{
    // first what type of argument are we
    uint32_t argTypeRand = rand32() % _gARG_TYPE_NORMAL_IF_LESS_THAN;
    ArgumentType argType;
    if (argTypeRand < _gARG_TYPE_ZERO_IF_LESS_THAN)
    {
        argType = ArgumentType_ZERO;
    }
    else if (argTypeRand < _gARG_TYPE_NaN_IF_LESS_THAN)
    {
        argType = ArgumentType_NaN;
    }
    else if (argTypeRand < _gARG_TYPE_INF_IF_LESS_THAN)
    {
        argType = ArgumentType_INF;
    }
    else if (argTypeRand < _gARG_TYPE_DENORMAL_IF_LESS_THAN)
    {
        argType = ArgumentType_DENORMAL;
    }
    else
    {
        argType = ArgumentType_NORMAL;
    }

#ifdef DEBUG
    printf("Generating argument of type %s\n", getArgString(argType));
#endif

    // now generate a new random uint32_t
    // to randomize all the bits
    uint32_t arg = rand32();

    // next we make sure it's the correct argument type
    switch (argType)
    {
        case ArgumentType_ZERO:
        {
            // zero is all zeros except the sign bit
            arg &= SIGN_MASK;
            break;
        }
        case ArgumentType_NaN:
        {
            // NaN is exponent all 1s, significand != 0
            arg |= EXPONENT_MASK;

            // generate random significands until it's none 0
            while ((arg & SIGNIFICAND_MASK) == 0)
            {
                arg |= (rand32() & SIGNIFICAND_MASK);
            }
            break;
        }
        case ArgumentType_INF:
        {
            // inf is exponent all 1s, significand 0
            arg |= EXPONENT_MASK;
            arg &= ~SIGNIFICAND_MASK;
            break;
        }
        case ArgumentType_DENORMAL:
        {
            // denormal is exponent 0, significand not 0
            arg &= ~EXPONENT_MASK;

            // generate random significands until it's none 0
            while ((arg & SIGNIFICAND_MASK) == 0)
            {
                arg |= (rand32() & SIGNIFICAND_MASK);
            }
            break;
        }
        case ArgumentType_NORMAL:
        {
            // normal is exponent != 0 and exponent != 1

            // generate random exponents until it's none 0
            // and none all 1s
            while (((arg & EXPONENT_MASK) == 0) ||
                   ((arg & EXPONENT_MASK) == EXPONENT_MASK))
            {
                arg &= ~EXPONENT_MASK;
                arg |= (rand32() & EXPONENT_MASK);
            }
            break;
        }
    }

    return arg;
}

int main(int argc, char **argv)
{
    // Use argv[0] as the name of this application
    const char *ourName = basename(argv[0]);

    // number of test cases to generate.
    uint32_t num_tests = 5000;

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
        int c = getopt_long(argc, argv, "hVn:o:", _gLongOptions, &option_index);

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
            case 'd':
            {
                // don't output tests with denormals
                _gNoDenormals = true;
                break;
            }
            case 'n':
            {
                // number of test cases
                num_tests = strtoul(optarg, NULL, 10);
                if (num_tests == 0)
                {
                    fprintf(stderr, "The argument for '-n' must be an integer > 0.\n\n", optopt);
                    usage(stderr, ourName);
                    return 1;
                }
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
                }
                usage(stderr, ourName);
                return 1;
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
    _gARG_TYPE_NaN_IF_LESS_THAN       = _gARG_TYPE_ZERO_IF_LESS_THAN + ARG_TYPE_NaN_WEIGHT;
    _gARG_TYPE_INF_IF_LESS_THAN       = _gARG_TYPE_NaN_IF_LESS_THAN + ARG_TYPE_INF_WEIGHT;
    if (_gNoDenormals)
    {
        _gARG_TYPE_DENORMAL_IF_LESS_THAN  = 0;
        _gARG_TYPE_NORMAL_IF_LESS_THAN    = _gARG_TYPE_INF_IF_LESS_THAN + ARG_TYPE_NORMAL_WEIGHT;
    }
    else
    {
        _gARG_TYPE_DENORMAL_IF_LESS_THAN  = _gARG_TYPE_INF_IF_LESS_THAN + ARG_TYPE_DENORMAL_WEIGHT;
        _gARG_TYPE_NORMAL_IF_LESS_THAN    = _gARG_TYPE_DENORMAL_IF_LESS_THAN + ARG_TYPE_NORMAL_WEIGHT;
    }

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

    for (uint32_t i = 0; i < num_tests; i++)
    {
        uint32_t intArg1 = generateArgument();
        uint32_t intArg2 = generateArgument();

        float floatArg1 = *(float *)&intArg1;
        float floatArg2 = *(float *)&intArg2;

        float floatRes = floatArg1 * floatArg2;
        uint32_t intRes = *(uint32_t *)&floatRes;

        if (_gNoDenormals &&
            ((intRes & EXPONENT_MASK) == 0) &&
            ((intRes & SIGNIFICAND_MASK) != 0))
        {
            // denormal and we don't support denormals
            i--;
            continue;
        }

#ifdef DEBUG
        printf("%G * %G = %G\n", floatArg1, floatArg2, floatRes);
#endif

        fprintf(f, "%u %u %u\n", intArg1, intArg2, intRes);
    }

    if (outputFile != NULL)
    {
        fclose(f);
    }

    return 0;
}
