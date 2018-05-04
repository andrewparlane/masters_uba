#include <stdio.h>
#include <stdlib.h>
#include <libgen.h>
#include <getopt.h>
#include <ctype.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>

#define MAJOR_VERSION   0
#define MINOR_VERSION   1

// Parámetros que puedes cambiar
#define TAMANO_DE_BLOQUE    (32)
#define TAMANO_DE_MEMORIA   (4096)
#define TAMANO_DE_CACHE     (1024)
#define NUMERO_DE_VIAS      (2)

// Valores calculados
#define BLOQUES_EN_MP       ((TAMANO_DE_MEMORIA)/(TAMANO_DE_BLOQUE))
#define LINEAS_EN_CACHE     ((TAMANO_DE_CACHE)/(TAMANO_DE_BLOQUE))
#define LINEAS_EN_UNA_VIA   ((LINEAS_EN_CACHE)/(NUMERO_DE_VIAS))

typedef enum
{
    Comando_R = 0,
    Comando_W,
    Comando_MR,
} Comando;

typedef struct
{
    uint8_t data[TAMANO_DE_BLOQUE];
} Bloque;

typedef struct
{
    Bloque data;

    uint32_t tag;
    bool valido;

    // cuando usamos esta linea en esta via
    // escribimos ultimoUso = 0
    // cada vez que accessemos esta linea pero en otra via
    // incrementamos ultimoUso.
    // Así cuando necesitamos reemplazar el bloque LRU
    // reemplazamos el bloque con el ultimoUso más alto
    uint32_t ultimoUso;
} LineaDeCache;

typedef struct
{
    LineaDeCache linea[LINEAS_EN_UNA_VIA];
} ViaDeCache;

typedef struct
{
    ViaDeCache via[NUMERO_DE_VIAS];
} Cache;

static const struct option _gLongOptions[] =
{
    {"help",    no_argument,        0, 'h' },
    {"version", no_argument,        0, 'V' },
    {0,         0,                  0,  0  }
};

static Bloque   _gMemoriaPrincipal[BLOQUES_EN_MP];
static Cache    _gCache;

static uint32_t _gAccessosTotal;
static uint32_t _gMisses;

// declaraciones adelante
static void actualizaUltimoUso(uint32_t linea, uint32_t viaUsado);

// ------------------------------------------------------------------
// Funciones obligatorio por el TP
// no cambias los nombres, argumentos
// o tipo de resultados
// ------------------------------------------------------------------

static void init()
{
    _gAccessosTotal = 0;
    _gMisses = 0;

    for (uint32_t via = 0; via < NUMERO_DE_VIAS; via++)
    {
        for (uint32_t linea = 0; linea < LINEAS_EN_UNA_VIA; linea++)
        {
            _gCache.via[via].linea[linea].valido = false;
            _gCache.via[via].linea[linea].ultimoUso = 0;
        }
    }
}

static unsigned char read_byte(int address)
{
    _gAccessosTotal++;
#warning TODO read_byte
    uint32_t indice;
    uint32_t tag;
    uint32_t via;

    actualizaUltimoUso(indice, via);
    return 0;
}

static int write_byte(int address, unsigned char value)
{
    _gAccessosTotal++;
#warning TODO write_byte
    uint32_t indice;
    uint32_t tag;
    uint32_t via;

    actualizaUltimoUso(indice, via);
    return 0;
}

static unsigned int get_miss_rate()
{
    if (_gAccessosTotal == 0)
    {
        // _gMisses / 0
        // _gMisses debería estar 0 también
        // así decimos 0%
        return 0;
    }
    else
    {
        double porcentaje = ((double)_gMisses * 100.0l) / (double)_gAccessosTotal;
        return (unsigned int)round(porcentaje);
    }
}

// ------------------------------------------------------------------
// Final de funciones obligatorio por el TP
// ------------------------------------------------------------------

static void usage(FILE *stream, const char *nuestroNombre)
{
    fprintf(stream,
           "Usage:\n"
           "  %s -h\n"
           "  %s -V\n"
           "  %s filename\n"
           "Options:\n"
           "  -h, --help Prints usage information.\n"
           "  -V, --version Prints version information.\n"
           "\n\n",
           nuestroNombre, nuestroNombre, nuestroNombre);
    // necesitamos usar nuestroNombre, nuestroNombre, nuestroNombre
    // porque no soportamos %1$s
}

static void actualizaUltimoUso(uint32_t linea, uint32_t viaUsado)
{
    for (uint32_t v = 0; v < NUMERO_DE_VIAS; v++)
    {
        if (v == viaUsado)
        {
            _gCache.via[v].linea[linea].ultimoUso = 0;
        }
        else
        {
            _gCache.via[v].linea[linea].ultimoUso++;
        }
    }
}

static int leerArchivo(const char *archivo)
{
    FILE *f = fopen(archivo, "r");
    if (f == NULL)
    {
        fprintf(stderr, "%s: No such file or directory\n", archivo);
        return 1;
    }

    while (1)
    {
#warning TODO leer línea para el comando
        Comando cmd;


        if (cmd == Comando_MR)
        {
            uint32_t mr = get_miss_rate();
            printf("Miss Rate: %u%%\n", mr);
        }
        else
        {
#warning TODO leer línea para la direcion
            uint32_t direcion;


            if (cmd == Comando_R)
            {
                read_byte(direcion);
            }
            else
            {
#warning TODO leer línea para el valor
                uint8_t valor;


                write_byte(direcion, valor);
            }
        }

        break;
    }

    fclose(f);

    return 0;
}

int main(int argc, char **argv)
{
    // usamos argv[0] como el nombre del aplicación
    // pero solo queremos el archivo, no la ruta
    const char *nuestroNombre = basename(argv[0]);

    // clear errors
    opterr = 0;

    // parse short options
    while (1)
    {
        // obtener el siguiente argumento
        int option_index = 0;
        int c = getopt_long(argc, argv, "hV", _gLongOptions, &option_index);

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
                // no seguimos despues de -h
                return 0;
            }
            case 'V':
            {
                printf("%s: Version %u.%u\n", nuestroNombre, MAJOR_VERSION, MINOR_VERSION);
                // no seguimos despues de -V
                return 0;
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
                    // solo muestra el usage
                }
                usage(stderr, nuestroNombre);
                return 1;
            }
            default:
            {
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

    init();

    return leerArchivo(argv[optind]);
}
