#include "pin_mux.h"
#include "clock_config.h"
#include "fsl_debug_console.h"

#include <stdio.h>

#define MSG DbgConsole_Printf

void main(void)
{
    BOARD_InitBootPins();
    BOARD_InitBootClocks();
    DbgConsole_Init(((uint32_t)(UART0)),
                    115200,
                    (DEBUG_CONSOLE_DEVICE_TYPE_UART),
                    CLOCK_GetCoreSysClkFreq());

    MSG("Hello world\n");
    while (1);
}
