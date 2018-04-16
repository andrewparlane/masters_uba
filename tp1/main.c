#include <stdio.h>
#include <stdlib.h>
#include <libgen.h>
#include <getopt.h>
#include <ctype.h>
#include <string.h>

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

int leerLinea(long long *data, unsigned int columnasEsperados)
{
#warning TODO
    return 0;
}

long long *leerEntrada(const char *archivo, unsigned int *filas, unsigned int *columnas)
{
    FILE *f = fopen(archivo, "r");
    if (f == NULL)
    {
        fprintf(stderr, "%s: No such file or directory\n", archivo);
        return NULL;
    }

    long long primerLinea[2];

    if (!leerLinea(primerLinea, 2))
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

    *filas = *(unsigned int *)llFilas;
    *columnas = *(unsigned int *)llColumnas;

    // numero de elementos = filas * columnas
    // cada uno es un long long, así:
    long long *entrada = malloc(*filas * *columnas * sizeof(long long));
    if (entrada == NULL)
    {
        fprintf(stderr, "Failed to malloc %u bytes\n", (unsigned int)(*filas * *columnas * sizeof(long long)));
        fclose(f);
        return NULL;
    }

    unsigned int i;
    for (i = 0; i < *filas; i++)
    if (!leerLinea(&entrada[i * *columnas], *columnas))
    {
        fclose(f);
        free(entrada);
        return NULL;
    }

    fclose(f);
    return entrada;
}

int escribirSalida(const char *archivo, long long *salida)
{
#warning TODO

    if (archivo == NULL)
    {
        // stdout
    }
    else
    {
        // archivo
    }

    return 0;
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
    unsigned int filas;
    unsigned int columnas;
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

    int res = escribirSalida(oArchivo, salida);
    free(entrada);
    free(salida);

    return res ? 0 : 1;
}
