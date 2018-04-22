#include <stdio.h>
#include <stdint.h>

int transponer(unsigned int filas, unsigned int columnas, long long *entrada, long long *salida)
{
    uint f;
    for (f = 0; f < filas; f++)
    {
        uint c;
        for (c = 0; c < columnas; c++)
        {
            salida[(c * filas) + f] = entrada[(f * columnas) + c];
        }
    }

    return 0;
}
