#include <stdio.h>
#include <unistd.h>
#include <stdbool.h>
#include <libgen.h>
#include <getopt.h>
#include <ctype.h>

#define MAJOR_VERSION   0
#define MINOR_VERSION   1

static const struct option long_options[] =
{
    {"help",        no_argument, 0, 'h' },
    {"version",     no_argument, 0, 'V' },
    {"lines",       no_argument, 0, 'l' },
    {"words",       no_argument, 0, 'w' },
    {"characters",  no_argument, 0, 'c' },
    {0,         0,               0,  0  }
};

static void usage(const char *nombre)
{
    printf("Usage:\n"
           "  %s -h\n"
           "  %s -V\n"
           "  %s [options]... [file]...\n"
           "Options:\n"
           "  -V, --version     Print version and quit.\n"
           "  -h, --help        Print this information.\n"
           "  -l, --lines       Print number of lines in file.\n"
           "  -w, --words       Print number of words in file.\n"
           "  -c, --characters  Print number of characters in file.\n"
           "  -i, --input       Path to input file.\n\n",
           nombre, nombre, nombre);
    // necesitamos usar nombre, nombre, nombre
    // porque no soportamos %1$s
}

static bool parseFile(const char *archivo, bool cFlag, bool wFlag, bool lFlag)
{
    printf("parsing %s with -%s%s%s\n",
           archivo,
           lFlag ? "l" : "",
           wFlag ? "w" : "",
           cFlag ? "c" : "");

    return true;
}

static bool parseStdin(bool cFlag, bool wFlag, bool lFlag)
{
    printf("parsing stdin with -%s%s%s\n",
           lFlag ? "l" : "",
           wFlag ? "w" : "",
           cFlag ? "c" : "");

    return true;
}

int main(int argc, char **argv)
{
    // usamos argv[0] como el nombre del aplicación
    // pero solo queremos el archivo, no la ruta
    const char *nuestroNombre = basename(argv[0]);

    bool lFlag = false;
    bool wFlag = false;
    bool cFlag = false;
    const char *iValue = NULL;

    // clear errors
    opterr = 0;

    // parse short options
    while (1)
    {
        // obtener el siguinete argumento
        int option_index = 0;
        int c = getopt_long(argc, argv, "hVlwci:", long_options, &option_index);

        if (c == -1)
        {
            // no hay más
            break;
        }

        switch (c)
        {
            case 'h':
            {
                usage(nuestroNombre);
                // no siguimos desupes de -h
                return 0;
            }
            case 'V':
            {
                printf("%s: Version %u.%u\n", nuestroNombre, MAJOR_VERSION, MINOR_VERSION);
                // no siguimos desupes de -V
                return 0;
            }
            case 'l':
            {
                lFlag = true;
                break;
            }
            case 'w':
            {
                wFlag = true;
                break;
            }
            case 'c':
            {
                cFlag = true;
                break;
            }
            case 'i':
            {
                iValue = optarg;
                break;
            }
            case '?':
            {
                if (optopt == 'i')
                {
                    fprintf(stderr, "Option '-%c' requires an argument.\n\n", optopt);
                }
                else if (isprint(optopt))
                {
                    // es un argumento, pero no es uno que esperamos
                    fprintf (stderr, "Unknown option '-%c'.\n\n", optopt);
                }
                else
                {
                    // solo mostra el usage
                }
                usage(nuestroNombre);
                return 1;
            }
            default:
            {
                // porque estámos aquí?
                usage(nuestroNombre);
                return 1;
            }
        }
    }

    // si ningún de -l -w o -c está especificado usamos todos
    if (!lFlag && !wFlag && !cFlag)
    {
        lFlag = true;
        wFlag = true;
        cFlag = true;
    }

    bool err = false;

    // si no hay archivos especificado usamos de stdin
    if (iValue == NULL && (optind >= argc))
    {
        parseStdin(cFlag, wFlag, lFlag);
    }
    else
    {
        // primero el archivo especificado con -i (si hay uno)
        if (iValue != NULL)
        {
            if (!parseFile(iValue, cFlag, wFlag, lFlag))
            {
                // outptus su propio mensaje de error
                err = true;
            }
        }

        // después cada argumento que no es un opción
        int index;
        for (index = optind; index < argc; index++)
        {
            if (!parseFile(argv[index], cFlag, wFlag, lFlag))
            {
                // outptus su propio mensaje de error
                err = true;
            }
        }
    }

    // return 0 si no había errores, o 1 si había
    return err ? 1 : 0;
}

