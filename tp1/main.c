#include <stdio.h>
#include <stdlib.h>
#include <libgen.h>
#include <getopt.h>
#include <ctype.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>

#define MAJOR_VERSION   0
#define MINOR_VERSION   1

// declaración adelante
// transponer es en transponer.c o transponer.s
extern int transponer(unsigned int filas,
                      unsigned int columnas,
                      long long *entrada,
                      long long *salida);

static const struct option long_options[] =
{
    {"help",    no_argument,        0, 'h' },
    {"version", no_argument,        0, 'V' },
    {"output",  required_argument,  0, 'o' },
    {0,         0,                  0,  0  }
};

static void usage(FILE *stream, const char *nuestroNombre)
{
    fprintf(stream,
           "Usage:\n"
           "  %s -h\n"
           "  %s -V\n"
           "  %s [options] filename\n"
           "Options:\n"
           "  -h, --help Prints usage information.\n"
           "  -V, --version Prints version information.\n"
           "  -o, --output Path to output file.\n"
           "\n"
           "Examples:\n"
           "  %s -o - mymatrix\n",
           nuestroNombre, nuestroNombre, nuestroNombre, nuestroNombre);
    // necesitamos usar nuestroNombre, nuestroNombre, nuestroNombre, nuestroNombre
    // porque no soportamos %1$s
}

// lea carácter por carácter deshaciendo whitespace
// hasta encuentra [0-9-]. Después comenzar a leer números
// [0-9]. Para cuando obtenemos EOF, \n, \r, ' ', \t.
// Es un error si encontramos algún otro carácter.
// devolver no 0 si hay un error
// *OK = 1 -> hay un integer valido en *ll
// *eof = 1 -> no hay más a leer
// *newLine = 1 -> encontramos nueva línea
bool leerLongLong(FILE *f, long long *ll, bool *OK, bool *eof, bool *newLine)
{
    *OK = false;
    *eof = false;
    *newLine = false;

    // soportamos signed 64 bits:
    // máx = 0x7FFF_FFFF_FFFF_FFFF =  9223372036854775807
    // min = 0x8000_0000_0000_0000 = -9223372036854775808
    // así max input legal es 20 cáracters +1 por NULL terminator
#define MAX_CHARS 20
    char buff[MAX_CHARS + 1];
    uint idx = 0;

    bool comenzandoLeerInt = false;
    while (1)
    {
        int res = fgetc(f);
        if (res == EOF)
        {
            *eof = true;
            // si tenemos algo en buff, convertimos ahora
            if (*OK)
            {
                buff[idx] = '\0';
                *ll = strtoll(buff, NULL, 10);
                if (errno != 0)
                {
                    fprintf(stderr, "Failed to convert %s to long long, error: %s\n", buff, strerror(errno));
                    return false;
                }
                return true;
            }
            else if (comenzandoLeerInt)
            {
                // solo podríamos estar aquí si leamos
                // un '-' y después nada, eso es un error
                fprintf(stderr, "Found invalid entry \"-\"\n");
                return false;
            }
            else
            {
                // eof but no error
                return true;
            }
        }

        char c = (char)res;
        if (c == '\r' || c == '\n')
        {
            *newLine = true;
        }

        if (!comenzandoLeerInt)
        {
            // Todavía no cemenzamos a leer el int
            if (c == ' ' || c == '\t')
            {
                // ignoramos
                continue;
            }
            else if (*newLine)
            {
                // nuevo línea, terminamos.
                return true;
            }
            else if (c >= '0' && c <= '9')
            {
                // válido
                buff[idx++] = c;
                comenzandoLeerInt = true;
                *OK = true;
            }
            else if (c == '-')
            {
                // también válido pero el int todavía no es OK
                // porque necesitamos un número después de un -
                buff[idx++] = c;
                comenzandoLeerInt = true;
            }
            else
            {
                // error
                fprintf(stderr, "Found invalid character %c\n", c);
                return false;
            }
        }
        else
        {
            // ya estamos leyendo data
            if (c == ' ' || c == '\t' ||
                *newLine)
            {
                // terminamos
                if (*OK)
                {
                    buff[idx] = '\0';
                    *ll = strtoll(buff, NULL, 10);
                    if (errno != 0)
                    {
                        fprintf(stderr, "Failed to convert %s to long long, error: %s\n", buff, strerror(errno));
                        return false;
                    }
                    return true;
                }
                else
                {
                    // solo podríamos estar aquí si leamos
                    // un '-' y después nada, eso es un error
                    fprintf(stderr, "Found invalid entry \"-\"\n");
                    return false;
                }
            }
            else if (c == '-')
            {
                // un - aquí no es válido porque estámos en el medio
                // de un int.
                fprintf(stderr, "Found \"-\" in the middle of an integer\n");
                return false;
            }
            else if (c >= '0' && c <= '9')
            {
                // válido
                if (idx >= MAX_CHARS)
                {
                    fprintf(stderr, "Integer read was too large to fit into a long long\n");
                    return false;
                }
                buff[idx++] = c;
                *OK = true;
            }
            else
            {
                // error
                fprintf(stderr, "Found invalid character %c\n", c);
                return false;
            }
        }
    }
}

bool leerLinea(FILE *f, long long *data, uint columnasEsperados, bool *eof)
{
    uint32_t count = 0;
    while (1)
    {
        bool OK;
        bool newLine;
        long long ll;
        if (!leerLongLong(f, &ll, &OK, eof, &newLine))
        {
            // error
            return false;
        }

        if (OK)
        {
            // leamos un integer
            if (count >= columnasEsperados)
            {
                // error - quisimos columnasEsperados integers
                // pero ya encontramos más.
                fprintf(stderr, "Too many entries on line. Expecting %u\n", columnasEsperados);
                return false;
            }

            data[count] = ll;
            count++;
        }

        if (*eof)
        {
            if (count != columnasEsperados)
            {
                // error - quisimos columnasEsperados integers
                // pero solo leamos count antes de eof
                fprintf(stderr, "Not enough entries on line. Expecting %u, found %u\n", columnasEsperados, count);
                return false;
            }
            else
            {
                return true;
            }
        }

        if (newLine)
        {
            if (count == 0) // permitimos newLines antes de data comenzando
            {
                continue;
            }
            else if (count != columnasEsperados)
            {
                // error - quisimos columnasEsperados integers
                // pero solo leamos count antes de newLine.
                fprintf(stderr, "Not enough entries on line. Expecting %u, found %u\n", columnasEsperados, count);
                return false;
            }
            else
            {
                return true;
            }
        }
    }
    return true;
}

long long *leerEntrada(const char *archivo, uint *filas, uint *columnas)
{
    FILE *f = fopen(archivo, "r");
    if (f == NULL)
    {
        fprintf(stderr, "%s: No such file or directory\n", archivo);
        return NULL;
    }

    long long primerLinea[2];

    bool eof;
    if (!leerLinea(f, primerLinea, 2, &eof))
    {
        fclose(f);
        return NULL;
    }

    long long *llFilas = &primerLinea[0];
    long long *llColumnas = &primerLinea[1];

    // Validar filas y columnas
    // no pueden ser menor de cero
    // ni mas grande de 0xFFFFFFFF
    if (*llFilas < 0 || *llColumnas < 0 ||
        *llFilas > 0xFFFFFFFF ||
        *llColumnas > 0xFFFFFFFF)
    {
        fprintf(stderr, "Invalid number of rows / columns\n");
        fclose(f);
        return NULL;
    }

    *filas = *(uint *)llFilas;
    *columnas = *(uint *)llColumnas;

    // numero de elementos = filas * columnas
    // cada uno es un long long, así:
    long long *entrada = malloc(*filas * *columnas * sizeof(long long));
    if (entrada == NULL)
    {
        fprintf(stderr, "Failed to malloc %u bytes\n", (unsigned int)(*filas * *columnas * sizeof(long long)));
        fclose(f);
        return NULL;
    }

    uint i;
    for (i = 0; i < *filas; i++)
    {
        if (!leerLinea(f, &entrada[i * *columnas], *columnas, &eof))
        {
            fclose(f);
            free(entrada);
            return NULL;
        }
    }

    // debería estar todo, comprobar que no hay más data
    while (!eof)
    {
        if (!leerLinea(f, NULL, 0, &eof))
        {
            fclose(f);
            free(entrada);
            return NULL;
        }
    }

    fclose(f);
    return entrada;
}

bool escribirSalida(const char *archivo, uint filas, uint columnas, long long *salida)
{
    FILE *f;

    if (archivo == NULL)
    {
        // stdout
        f = stdout;
    }
    else
    {
        // archivo
        f = fopen(archivo, "w");
        if (f == NULL)
        {
            fprintf(stderr, "Failed to open %s for writing\n", archivo);
            return NULL;
        }
    }

    fprintf(f, "%u %u\n", filas, columnas);
    uint i;
    for (i = 0; i < filas; i++)
    {
        uint c;
        for (c = 0; c < columnas; c++)
        {
            fprintf(f, "%lld ", salida[(i * columnas) + c]);
        }
        fprintf(f, "\n");
    }

    if (archivo != NULL)
    {
        fclose(f);
    }

    return true;
}

int main(int argc, char **argv)
{
    // usamos argv[0] como el nombre del aplicación
    // pero solo queremos el archivo, no la ruta
    const char *nuestroNombre = basename(argv[0]);

    // escribir la salida a un archivo si veamos -o (y el argumento no es -)
    const char *oArchivo = NULL;

    // clear errors
    opterr = 0;

    // parse short options
    while (1)
    {
        // obtener el siguinete argumento
        int option_index = 0;
        int c = getopt_long(argc, argv, "hVo:", long_options, &option_index);

        if (c == -1)
        {
            // no hay más
            break;
        }

        switch (c)
        {
            case 'h':
            {
                usage(stdout, nuestroNombre);
                // no siguimos desupes de -h
                return 0;
            }
            case 'V':
            {
                printf("%s: Version %u.%u\n", nuestroNombre, MAJOR_VERSION, MINOR_VERSION);
                // no siguimos desupes de -V
                return 0;
            }
            case 'o':
            {
                // si veamos "-o -" la salida es stdout
                // si no, la salida es el archivo en optarg
                if (strcmp(optarg, "-") != 0)
                {
                    oArchivo = optarg;
                }
                break;
            }
            case '?':
            {
                if (optopt == 'o')
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
                usage(stderr, nuestroNombre);
                return 1;
            }
            default:
            {
                // porque estámos aquí?
                usage(stderr, nuestroNombre);
                return 1;
            }
        }
    }

    if (optind == argc)
    {
        fprintf(stderr, "filename is required\n\n");
        usage(stderr, nuestroNombre);
        return 1;
    }

    if ((optind + 1) != argc)
    {
        fprintf(stderr, "Too many arguments\n\n");
        usage(stderr, nuestroNombre);
        return 1;
    }

    // leer archivo
    uint filas;
    uint columnas;
    long long *entrada = leerEntrada(argv[optind], &filas, &columnas);
    if (entrada == NULL)
    {
        // falla, leerArchivo escribí el error
        return 1;
    }

    // malloc la salida
    long long *salida = malloc(filas * columnas * sizeof(long long));
    if (salida == NULL)
    {
        fprintf(stderr, "Failed to allocate %u bytes for output\n", (unsigned int)(filas * columnas * sizeof(long long)));
        free(entrada);
        return 1;
    }

    // transponer
    if (transponer(filas, columnas, entrada, salida) != 0)
    {
        fprintf(stderr, "Failed to transpose the matrix\n");
        free(entrada);
        free(salida);
        return 1;
    }

    // escribir el resultado
    // nota que intercambiamos columnas y filas
    bool res = escribirSalida(oArchivo, columnas, filas, salida);
    free(entrada);
    free(salida);

    return res ? 0 : 1;
}
