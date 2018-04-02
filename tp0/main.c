#include <stdio.h>
#include <unistd.h>
#include <stdbool.h>
#include <libgen.h>
#include <getopt.h>
#include <ctype.h>
#include <stdint.h>

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

static bool obtenerCharacter(FILE *stream, bool *whitespace, bool *newline)
{
    *whitespace = false;
    *newline = false;
    while (1)
    {
        int c = fgetc(stream);
        if (c == EOF)
        {
            return false;
        }

        uint8_t bytesMas;
        // 0xxx_xxxx => 1 byte
        // 110x_xxxx => 2 bytes
        // 1110_xxxx => 3 bytes
        // 1111_0xxx => 4 bytes
        // 1111_1xxx => inválido
        if (c < 128) // ascii
        {
            *whitespace = isspace(c);
            *newline = (c == '\n');
            return true;
        }
        else if (c < 0xE0)
        {
            bytesMas = 1;
        }
        else if (c < 0xF0)
        {
            bytesMas = 2;
        }
        else
        {
            bytesMas = 3;
        }

        int i;
        for (i = 0; i < bytesMas; i++)
        {
            c = fgetc(stream);
            if (c == EOF)
            {
                // inválido, no contamos
                return false;
            }
            // TODO whitespace en UTF8?
        }

        return true;
    }
}

static void parseStream(FILE *stream, uint32_t *chars, uint32_t *palabras, uint32_t *lineas)
{
    *chars = 0;
    *palabras = 0;
    *lineas = 0;
    bool ultimoEstuvoWhitespace = true;

    while (1)
    {
        bool whitespace;
        bool newline;
        if (!obtenerCharacter(stream, &whitespace, &newline))
        {
            // termina la palabra corriente
            if (!ultimoEstuvoWhitespace )
            {
                (*palabras)++;
            }
            break;
        }

        (*chars)++;

        if (whitespace && !ultimoEstuvoWhitespace)
        {
            (*palabras)++;
            ultimoEstuvoWhitespace = true;
        }
        if (!whitespace)
        {
            ultimoEstuvoWhitespace = false;
        }

        if (newline)
        {
            (*lineas)++;
        }
    }
}

void output(bool cFlag, bool wFlag, bool lFlag, uint32_t caracteres, uint32_t palabras, uint32_t lineas, const char *archivo)
{
    bool outputPrevio = false;
    if (lFlag)
    {
        printf("%s%u", outputPrevio ? "\t" : "", lineas);
        outputPrevio = true;
    }
    if (wFlag)
    {
        printf("%s%u", outputPrevio ? "\t" : "", palabras);
        outputPrevio = true;
    }
    if (cFlag)
    {
        printf("%s%u", outputPrevio ? "\t" : "", caracteres);
        outputPrevio = true;
    }
    if (archivo != NULL)
    {
        printf("%s%s", outputPrevio ? "\t" : "", archivo);
    }
    printf("\n");
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
    uint32_t totalLineas = 0;
    uint32_t totalPalabras = 0;
    uint32_t totalcaracteres = 0;
    uint32_t totalArchivos = 0;

    // si no hay archivos especificado usamos de stdin
    if (iValue == NULL && (optind >= argc))
    {
        parseStream(stdin, &totalcaracteres, &totalPalabras, &totalLineas);
        totalArchivos = 1;

        output(cFlag, wFlag, lFlag, totalcaracteres, totalPalabras, totalLineas, NULL);
    }
    else
    {
        // primero el archivo especificado con -i (si hay uno)
        if (iValue != NULL)
        {
            FILE *stream = fopen(iValue, "rb");
            if (stream == NULL)
            {
                fprintf(stderr, "%s: %s: No such file or directory\n", nuestroNombre, iValue);
                err = true;
            }
            else
            {
                uint32_t chars;
                uint32_t palabras;
                uint32_t lineas;
                parseStream(stream, &chars, &palabras, &lineas);
                fclose(stream);
                output(cFlag, wFlag, lFlag, chars, palabras, lineas, iValue);

                totalcaracteres    += chars;
                totalPalabras       += palabras;
                totalLineas         += lineas;
            }

            // conta el archivo si existe o no
            totalArchivos++;
        }

        // después cada argumento que no es un opción
        int index;
        for (index = optind; index < argc; index++)
        {
            FILE *stream = fopen(argv[index], "rb");
            if (stream == NULL)
            {
                fprintf(stderr, "%s: %s: No such file or directory\n", nuestroNombre, argv[index]);
                err = true;
            }
            else
            {
                uint32_t chars;
                uint32_t palabras;
                uint32_t lineas;
                parseStream(stream, &chars, &palabras, &lineas);
                fclose(stream);
                output(cFlag, wFlag, lFlag, chars, palabras, lineas, argv[index]);

                totalcaracteres    += chars;
                totalPalabras       += palabras;
                totalLineas         += lineas;
            }

            // conta el archivo si existe o no
            totalArchivos++;
        }
    }

    if (totalArchivos > 1)
    {
        output(cFlag, wFlag, lFlag, totalcaracteres, totalPalabras, totalLineas, "total");
    }

    // return 0 si no había errores, o 1 si había
    return err ? 1 : 0;
}

