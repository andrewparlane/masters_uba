#include <mips/regdef.h>

    .text
    .align  2
    .globl  transponer
    .ent    transponer

# int transponer(unsigned int filas,
#                unsigned int columnas,
#                long long *entrada,
#                long long *salida)

transponer:
    subu    sp, sp, 8
    sw      gp, 0(sp)
    sw      $fp, 4(sp)

    move    v0, zero

    lw      gp, 0(sp)
    lw      $fp, 4(sp)
    addu    sp, sp, 8
    jr      ra

    .end transponer
