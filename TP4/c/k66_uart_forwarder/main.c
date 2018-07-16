#include "pin_mux.h"
#include "clock_config.h"
#include "fsl_uart.h"

#include <stdio.h>

const char *WELCOME_MSG = "K66 UART Forwarder\n" \
                          "Waiting for data\n";

void main(void)
{
    BOARD_InitBootPins();
    BOARD_InitBootClocks();

    // set up the debug uart channel
    uart_config_t config;
    UART_GetDefaultConfig(&config);
    config.enableTx = true;
    config.enableRx = true;
    status_t res = UART_Init(UART0, &config, CLOCK_GetCoreSysClkFreq());
    if (res != kStatus_Success)
    {
        while (1);
    }

    res = UART_Init(UART1, &config, CLOCK_GetCoreSysClkFreq());
    if (res != kStatus_Success)
    {
        while (1);
    }

    UART_WriteBlocking(UART0, WELCOME_MSG, strlen(WELCOME_MSG));

    while (1)
    {
        // read char and then send it over UART1
        uint8_t c;
        res = UART_ReadBlocking(UART0, &c, 1);
        UART_WriteBlocking(UART1, &c, 1);
    }
}
