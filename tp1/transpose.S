    #   +---------------+   |------------MAIN------------
    # 52    |       |   \
    #   +---------------+   |
    # 48    |   ra  |   |
    #   +---------------+   |   SRA MAIN
    # 44    |   fp  |   |
    #   +---------------+   |
    # 40    |   gp  |   /
    #   +---------------+
    # 36    |   c   |   \
    #   +---------------+   |
    # 32 |option_index| |
    #   +---------------+   |   LTA MAIN
    # 28   |oArchivo|   |
    #   +---------------+   |
    # 24 |nuestroNombre|/
    #   +---------------+
    # 20    |   a3  |   \
    #   +---------------+   |
    # 16    |   a2  |   |
    #   +---------------+   |   ABA MAIN
    # 12    |   a1  |   |
    #   +---------------+   |
    # 08    |   a0  |   /
    #   +---------------+   |----------TRANSPONER----------
    # 04    |   fp  |   \
    #   +---------------+   |   SRA TRANSPONER
    # 00    |   gp  |   /
    #   +---------------+   |


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
    sw      gp,  0(sp)
    sw      $fp, 4(sp)
    sw      a0,  8(sp)
    sw      a1, 12(sp)
    sw      a2, 16(sp)
    sw      a3, 20(sp)

    # a0 = filas
    # a1 = columnas
    # a2 = &entrada[0]
    # a3 = &salida[0]

    move    v0, zero            # siempre devolvemos 0 no hay errores posibles

    beqz    a0, fin             # if (filas == 0) return 0;
    beqz    a1, fin             # if (columnas == 0) return 0;

    move    t0, zero            # uint f = 0;

filaLoop:                       # do {
    move    t1, zero            #   uint c = 0;

columnaLoop:                    #   do {
    ld      t2, 0(a2)           #     (t2,t3) = *entrada;
    addu    a2, a2, 8           #     entrada++;

    mul     t4, t1, a0          #     t4 = (c * filas);
    addu    t4, t4, t0          #     t4 += f;
    mul     t4, t4, 8           #     t4 = offset en salida
    addu    t4, t4, a3          #     t4 = &salida[(c * filas) + f]
    sd      t2, 0(t4)           #     salida[(c * filas) + f] = (t2,t3)

    addu    t1, t1, 1           #     c++;
    bne     t1, a1, columnaLoop #   } while (c != columnas)

    addu    t0, t0, 1           #   f++;
    bne     t0, a0, filaLoop    # } while (f != filas)

fin:
    lw      gp, 0(sp)
    lw      $fp, 4(sp)
    addu    sp, sp, 8
    jr      ra

    .end transponer
