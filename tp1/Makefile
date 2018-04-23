C_TARGET = tp1_c
ASM_TARGET = tp1_asm

MACHINE = $(shell uname -m)

LIBS =
CC = gcc
C_FLAGS = -Wall -g
ASM_FLAGS = -Wall -g

default: $(C_TARGET)
all: default

C_OBJECTS = main.c.o \
		    transpose.c.o

ASM_OBJECTS = main.c.o \
			  transpose.S.o

HEADERS = $(wildcard *.h)

ifeq ($(MACHINE), pmax)

define HACE_PRUEBA_ASM
	@echo Probando código ASM con pruebas/$(strip $(1))
	@./pruebaScript.sh $(ASM_TARGET) $(strip $(1)) $(2)
endef

else

define HACE_PRUEBA_ASM
	@#Hace nada porque no estamos pmax
endef

endif

# Macro con dos argumentos
#  1) El nombre de archivo a probar en pruebas/
#  2) Código de salida esperado
#
# Si el código de salida es igual al esperada,
# combrobamos la salida con un archivo que
# tiene el mismo nombre del input en resultados/

define HACE_PRUEBA

	@echo Probando código C con pruebas/$(strip $(1))
	@# Primero con salida a un archivo
	@./pruebaScript.sh $(C_TARGET) $(strip $(1)) $(2)
	$(call HACE_PRUEBA_ASM, $(1), $(2))
endef


%.c.o: %.c $(HEADERS)
	$(CC) $(C_FLAGS) -c $< -o $@

%.S.o: %.S $(HEADERS)
	$(CC) $(ASM_FLAGS) -c $< -o $@

$(C_TARGET): $(C_OBJECTS)
	$(CC) $(C_OBJECTS) $(C_FLAGS) $(LIBS) -o $@

$(ASM_TARGET): $(ASM_OBJECTS)
	$(CC) $(ASM_OBJECTS) $(ASM_FLAGS) $(LIBS) -o $@

C: $(C_TARGET)

ifeq ($(MACHINE), pmax)

ASM: $(ASM_TARGET)

else

ASM:

endif

c: C

asm: ASM

prueba: C ASM
	@# Primero el básico
	-$(call HACE_PRUEBA, matrix1, 0)
	@# Con finales de líneas diferentes
	-$(call HACE_PRUEBA, matrix_crlf, 0)
	-$(call HACE_PRUEBA, matrix_cr_only, 0)
	-$(call HACE_PRUEBA, matrix_lf_only, 0)
	@# Espacio blanco extra
	-$(call HACE_PRUEBA, matrix_filas_blancas, 0)
	-$(call HACE_PRUEBA, matrix_tabs, 0)
	@# Numeros negativos o grandes, pero en el rango de signed long long
	-$(call HACE_PRUEBA, matrix_negativo, 0)
	-$(call HACE_PRUEBA, matrix_long_long, 0)
	@# Inválidos
	-$(call HACE_PRUEBA, matrix2, 1)
	-$(call HACE_PRUEBA, matrix3, 1)
	-$(call HACE_PRUEBA, matrix_filas_negativos, 1)
	-$(call HACE_PRUEBA, matrix_demasiado_columnos, 1)
	-$(call HACE_PRUEBA, matrix_demasiado_filas, 1)
	-$(call HACE_PRUEBA, matrix_demasiado_largo_int, 1)
	-$(call HACE_PRUEBA, matrix_demasiado_largo_int2, 1)
	-$(call HACE_PRUEBA, matrix_demasiado_negativo_int, 1)
	-$(call HACE_PRUEBA, matrix_demasiado_negativo_int2, 1)
	-$(call HACE_PRUEBA, matrix_no_suficiente_filas, 1)

clean:
	-rm -f *.o
	-rm -f $(C_TARGET)
	-rm -f $(ASM_TARGET)
	-rm -f salida stdout stderr

.PHONY: default all C c ASM asm clean
