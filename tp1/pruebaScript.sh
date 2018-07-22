#!/bin/sh

# Argumentos:
#  $1 applicación
#  $2 entrada en pruebas/ sin la ruta
#  $3 código de salida esperada

./$1 -o salida pruebas/$2 > stdout 2> stderr
export RES_CODE=$?
if [ $RES_CODE -eq $3 ]; then
    if [ $RES_CODE -ne 0 ]; then
        echo "  OK";
    else
        diff -w salida pruebas/esperados/$2 > /dev/null;
        if [ $? -eq 0 ]; then
            echo "  OK";
        else
            echo "  Transpuesta no es como esperada";
        fi
    fi
else
    echo "  Código de salida no es esperado";
fi
