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

#define MAJOR_VERSION   (0)
#define MINOR_VERSION   (1)

//#define DEBUG

#define SIGN_MASK_32B           (0x80000000)
#define EXPONENT_MASK_32B       (0x7F800000)
#define SIGNIFICAND_MASK_32B    (~((EXPONENT_MASK_32B) | (SIGN_MASK_32B)))

#define SIGN_MASK_64B           (0x8000000000000000)
#define EXPONENT_MASK_64B       (0x7FF0000000000000)
#define SIGNIFICAND_MASK_64B    (~((EXPONENT_MASK_64B) | (SIGN_MASK_64B)))

static int _gDouble = 0;
static const struct option _gLongOptions[] =
{
    {"help",                no_argument,        0,          'h' },
    {"version",             no_argument,        0,          'V' },
    {"num_tests",           required_argument,  0,          'n' },
    {"no_denormal",         no_argument,        0,          'd' },
    {"rounding_mode",       required_argument,  0,          'r' },
    {"double_precision",    no_argument,        &_gDouble,   1  },
    {"op_add",              no_argument,        0,          'a' },
    {"op_subtract",         no_argument,        0,          's' },
    {"op_multiply",         no_argument,        0,          'm' },
    {"output",              required_argument,  0,          'o' },
    {0,                     0,                  0,           0  }
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

typedef enum
{
    RoundingMode_ZERO = 0,
    RoundingMode_NEG_INF = 1,
    RoundingMode_POS_INF = 2,
    RoundingMode_NEAREST = 3,

    NUM_ROUNDING_MODES
} RoundingMode;

typedef enum
{
    Operation_MULTIPLY = 0,
    Operation_ADD,
    Operation_SUBTRACT
} Operation;


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
           "  %s -h\n"
           "  %1$s -V\n"
           "  %1$s [options]\n"
           "Options:\n"
           "  -h, --help                Prints usage information.\n"
           "  -V, --version             Prints version information.\n"
           "  -n, --num_tests NUM       Number of tests to output.\n"
           "  -d, --no_denormal         Don't include denormals.\n"
           "      --double_precision    Use double precision (64 bits total, 11 bits exponent)\n"
           "  -m, --op_multiply         Generate test cases for multiplication (default)\n"
           "  -a, --op_add              Generate test cases for addition\n"
           "  -s, --op_subtract         Generate test cases for subtraction\n"
           "  -r, --rounding_mode MODE  Set the rounding mode.\n"
           "                                MODE = %u round towards zero (truncate).\n"
           "                                MODE = %u round towards negative infinity.\n"
           "                                MODE = %u round towards positive infinity.\n"
           "                                MODE = %u round to nearest, ties even (default).\n"
           "  -o, --output              Path to output file.\n"
           "\n"
           "Examples:\n"
           "  %1$s -n 10000 -d -r 0 -o -\n"
           "\n",
           ourName,
           RoundingMode_ZERO,
           RoundingMode_NEG_INF,
           RoundingMode_POS_INF,
           RoundingMode_NEAREST);
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

static uint64_t rand64()
{
    // rand() is only guaranteed to be 15 bits
    // so just call rand32 twice
    return (((uint64_t)rand32()) <<  0) |
           (((uint64_t)rand32()) <<  32);
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

static const char *getOperationString(Operation op)
{
    switch (op)
    {
        case Operation_ADD:         return "+";
        case Operation_SUBTRACT:    return "-";
        case Operation_MULTIPLY:    return "*";
        default:                    return "unknown";
    }
}
#endif

static const char *getRoundingModeString(RoundingMode roundingMode)
{
    switch (roundingMode)
    {
        case RoundingMode_ZERO:     return "zero";
        case RoundingMode_NEG_INF:  return "negative infinity";
        case RoundingMode_POS_INF:  return "positive infinity";
        case RoundingMode_NEAREST:  return "nearest";
        default:                    return "unknown";
    }
}

static ArgumentType generateArgType()
{
    ArgumentType argType;
    uint32_t argTypeRand = rand32() % _gARG_TYPE_NORMAL_IF_LESS_THAN;

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

    return argType;
}

static uint32_t generate32BitArgument()
{
    // first what type of argument are we
    ArgumentType argType = generateArgType();

    // now generate a new random uint32_t
    // to randomize all the bits
    uint32_t arg = rand32();

    // next we make sure it's the correct argument type
    switch (argType)
    {
        case ArgumentType_ZERO:
        {
            // zero is all zeros except the sign bit
            arg &= SIGN_MASK_32B;
            break;
        }
        case ArgumentType_NaN:
        {
            // NaN is exponent all 1s, significand != 0
            arg |= EXPONENT_MASK_32B;

            // generate random significands until it's none 0
            while ((arg & SIGNIFICAND_MASK_32B) == 0)
            {
                arg |= (rand32() & SIGNIFICAND_MASK_32B);
            }
            break;
        }
        case ArgumentType_INF:
        {
            // inf is exponent all 1s, significand 0
            arg |= EXPONENT_MASK_32B;
            arg &= ~SIGNIFICAND_MASK_32B;
            break;
        }
        case ArgumentType_DENORMAL:
        {
            // denormal is exponent 0, significand not 0
            arg &= ~EXPONENT_MASK_32B;

            // generate random significands until it's none 0
            while ((arg & SIGNIFICAND_MASK_32B) == 0)
            {
                arg |= (rand32() & SIGNIFICAND_MASK_32B);
            }
            break;
        }
        case ArgumentType_NORMAL:
        {
            // normal is exponent != 0 and exponent != 1

            // generate random exponents until it's none 0
            // and none all 1s
            while (((arg & EXPONENT_MASK_32B) == 0) ||
                   ((arg & EXPONENT_MASK_32B) == EXPONENT_MASK_32B))
            {
                arg &= ~EXPONENT_MASK_32B;
                arg |= (rand32() & EXPONENT_MASK_32B);
            }
            break;
        }
    }

    return arg;
}

static uint64_t generate64BitArgument()
{
    // first what type of argument are we
    ArgumentType argType = generateArgType();

    // now generate a new random uint64_t
    // to randomize all the bits
    uint64_t arg = rand64();

    // next we make sure it's the correct argument type
    switch (argType)
    {
        case ArgumentType_ZERO:
        {
            // zero is all zeros except the sign bit
            arg &= SIGN_MASK_64B;
            break;
        }
        case ArgumentType_NaN:
        {
            // NaN is exponent all 1s, significand != 0
            arg |= EXPONENT_MASK_64B;

            // generate random significands until it's none 0
            while ((arg & SIGNIFICAND_MASK_64B) == 0)
            {
                arg |= (rand64() & SIGNIFICAND_MASK_64B);
            }
            break;
        }
        case ArgumentType_INF:
        {
            // inf is exponent all 1s, significand 0
            arg |= EXPONENT_MASK_64B;
            arg &= ~SIGNIFICAND_MASK_64B;
            break;
        }
        case ArgumentType_DENORMAL:
        {
            // denormal is exponent 0, significand not 0
            arg &= ~EXPONENT_MASK_64B;

            // generate random significands until it's none 0
            while ((arg & SIGNIFICAND_MASK_64B) == 0)
            {
                arg |= (rand64() & SIGNIFICAND_MASK_64B);
            }
            break;
        }
        case ArgumentType_NORMAL:
        {
            // normal is exponent != 0 and exponent != 1

            // generate random exponents until it's none 0
            // and none all 1s
            while (((arg & EXPONENT_MASK_64B) == 0) ||
                   ((arg & EXPONENT_MASK_64B) == EXPONENT_MASK_64B))
            {
                arg &= ~EXPONENT_MASK_64B;
                arg |= (rand64() & EXPONENT_MASK_64B);
            }
            break;
        }
    }

    return arg;
}

static void generateSinglePrecision(FILE *f, Operation op, uint32_t num_tests)
{
    for (uint32_t i = 0; i < num_tests; i++)
    {
        uint32_t intArg1 = generate32BitArgument();
        uint32_t intArg2 = generate32BitArgument();

        float floatArg1 = *(float *)&intArg1;
        float floatArg2 = *(float *)&intArg2;

        float floatRes;
        switch (op)
        {
            case Operation_ADD:
            {
                floatRes = floatArg1 + floatArg2;
                break;
            }
            case Operation_SUBTRACT:
            {
                floatRes = floatArg1 - floatArg2;
                break;
            }
            case Operation_MULTIPLY:
            default:
            {
                floatRes = floatArg1 * floatArg2;
                break;
            }
        }

        uint32_t intRes = *(uint32_t *)&floatRes;

        if (_gNoDenormals &&
            ((intRes & EXPONENT_MASK_32B) == 0) &&
            ((intRes & SIGNIFICAND_MASK_32B) != 0))
        {
            // denormal and we don't support denormals
            i--;
            continue;
        }

#ifdef DEBUG
        printf("%G %s %G = %G\n", floatArg1, getOperationString(op), floatArg2, floatRes);
#endif

        fprintf(f, "%u %u %u\n", intArg1, intArg2, intRes);
    }
}

static void generateDoublePrecision(FILE *f, Operation op, uint32_t num_tests)
{
    for (uint32_t i = 0; i < num_tests; i++)
    {
        uint64_t intArg1 = generate64BitArgument();
        uint64_t intArg2 = generate64BitArgument();

        double doubleArg1 = *(double *)&intArg1;
        double doubleArg2 = *(double *)&intArg2;

        double doubleRes;
        switch (op)
        {
            case Operation_ADD:
            {
                doubleRes = doubleArg1 + doubleArg2;
                break;
            }
            case Operation_SUBTRACT:
            {
                doubleRes = doubleArg1 - doubleArg2;
                break;
            }
            case Operation_MULTIPLY:
            default:
            {
                doubleRes = doubleArg1 * doubleArg2;
                break;
            }
        }

        uint64_t intRes = *(uint64_t *)&doubleRes;

        if (_gNoDenormals &&
            ((intRes & EXPONENT_MASK_64B) == 0) &&
            ((intRes & SIGNIFICAND_MASK_64B) != 0))
        {
            // denormal and we don't support denormals
            i--;
            continue;
        }

#ifdef DEBUG
        printf("%G %s %G = %G\n", doubleArg1, getOperationString(op), doubleArg2, doubleRes);
#endif

        fprintf(f, "%llu %llu %llu\n", intArg1, intArg2, intRes);
    }
}

int main(int argc, char **argv)
{
    // Use argv[0] as the name of this application
    const char *ourName = basename(argv[0]);

    // number of test cases to generate.
    uint32_t num_tests = 5000;

    // rounding mode to use
    // default is nearest
    RoundingMode roundingMode = RoundingMode_NEAREST;

    // Operation
    Operation op = Operation_MULTIPLY;
    uint numOpFlags = 0;

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
        int c = getopt_long(argc, argv, "hVmasdn:r:o:", _gLongOptions, &option_index);

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
                    fprintf(stderr, "The argument for '-n' must be an integer > 0.\n\n");
                    usage(stderr, ourName);
                    return 1;
                }
                break;
            }
            case 'm':
            {
                op = Operation_MULTIPLY;
                numOpFlags++;
                break;
            }
            case 'a':
            {
                op = Operation_ADD;
                numOpFlags++;
                break;
            }
            case 's':
            {
                op = Operation_SUBTRACT;
                numOpFlags++;
                break;
            }
            case 'r':
            {
                // rounding mode
                roundingMode = strtoul(optarg, NULL, 10);
                if ((roundingMode < 0) ||
                    (roundingMode >= NUM_ROUNDING_MODES))
                {
                    fprintf(stderr, "The argument for '-r' must be an integer between 0 and %u.\n\n", NUM_ROUNDING_MODES - 1);
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
                    (optopt == 'n') ||
                    (optopt == 'r'))
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

    if (numOpFlags > 1)
    {
        fprintf(stderr, "Only one of -a, -s, and -m may be selected\n");
        usage(stderr, ourName);
        return 1;
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

    // set up the rounding mode
    int round;
    switch (roundingMode)
    {
        case RoundingMode_ZERO:     round = FE_TOWARDZERO;  break;
        case RoundingMode_NEG_INF:  round = FE_DOWNWARD;    break;
        case RoundingMode_POS_INF:  round = FE_UPWARD;      break;
        case RoundingMode_NEAREST:
        default:                    round = FE_TONEAREST;   break;
    }
    if (fesetround(round) != 0)
    {
        fprintf(stderr, "Failed to set rounding mode to %s\n", getRoundingModeString(roundingMode));
        return 3;
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

    if (_gDouble)
    {
        generateDoublePrecision(f, op, num_tests);
    }
    else
    {
        generateSinglePrecision(f, op, num_tests);
    }

    if (outputFile != NULL)
    {
        fclose(f);
    }

    return 0;
}
