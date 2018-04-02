TARGET = tp0

MACHINE = $(shell uname -m)

LIBS =
CC = gcc
CFLAGS = -Wall
SOLO_ASM_FLAGS = -O0 -S

# solo podríamos usar mrnames en MIPS
ifeq ($(MACHINE),pmax)
	SOLO_ASM_FLAGS += -mrnames
endif

define HACE_PRUEBA
	$(1) wc $(2) $(4) >> wc_out 2>&1
	$(1) ./$(TARGET) $(3) $(4) >> tp0_out 2>&1
endef

default: $(TARGET)
all: default

OBJECTS = $(patsubst %.c, %.o, $(wildcard *.c))
ASSEMBLER = $(patsubst %.c, %.s, $(wildcard *.c))
HEADERS = $(wildcard *.h)

%.o: %.c $(HEADERS)
	$(CC) $(CFLAGS) -c $< -o $@

%.s: %.c $(HEADERS)
	$(CC) $(CFLAGS) $(SOLO_ASM_FLAGS) -c $<

$(TARGET): $(OBJECTS)
	$(CC) $(OBJECTS) -Wall $(LIBS) -o $@

asm: $(ASSEMBLER)

prueba: $(TARGET)
	-rm -f wc_out tp0_out
	# archivos normales
	-$(call HACE_PRUEBA, , -lwm, -i, pruebas/cyclopedia.txt)
	-$(call HACE_PRUEBA, , -lwm, -lwc, pruebas/beowulf.txt)
	-$(call HACE_PRUEBA, , -lwm, , pruebas/elquijote.txt)
	# solo lineas
	-$(call HACE_PRUEBA, , -l, -l, pruebas/cyclopedia.txt)
	-$(call HACE_PRUEBA, , -l, -li, pruebas/beowulf.txt)
	-$(call HACE_PRUEBA, , -l, -l, pruebas/elquijote.txt)
	# solo palabras
	-$(call HACE_PRUEBA, , -w, -w, pruebas/cyclopedia.txt)
	-$(call HACE_PRUEBA, , -w, -w, pruebas/beowulf.txt)
	-$(call HACE_PRUEBA, , -w, -wi, pruebas/elquijote.txt)
	# solo carácters
	-$(call HACE_PRUEBA, , -m, -c, pruebas/cyclopedia.txt)
	-$(call HACE_PRUEBA, , -m, -c, pruebas/beowulf.txt)
	-$(call HACE_PRUEBA, , -m, -c, pruebas/elquijote.txt)
	# múltiples archivos
	-$(call HACE_PRUEBA, , -lwm, -i, pruebas/cyclopedia.txt pruebas/beowulf.txt pruebas/elquijote.txt)
	-$(call HACE_PRUEBA, , -lwm, , pruebas/cyclopedia.txt pruebas/beowulf.txt pruebas/elquijote.txt)
	# wildcard
	-$(call HACE_PRUEBA, , -lwm, , pruebas/*.txt)
	# archivos que no existe
	-$(call HACE_PRUEBA, , -lwm, , pruebas/esto/archivo/no.existe)
	-$(call HACE_PRUEBA, , -lwm, , pruebas/esto/archivo/no.existe este.tampoco)
	# archivos / rutas con carácters especiales
	-$(call HACE_PRUEBA, , -lwm, , pruebas/abc\ def)
	-$(call HACE_PRUEBA, , -lwm, , pruebas/\"\")
	-$(call HACE_PRUEBA, , -lwm, , "pruebas/alice.txt")
	-$(call HACE_PRUEBA, , -lwm, , pruebas/álíçé.txt)
	# archivos binarios
	-$(call HACE_PRUEBA, , -lwm, , $(TARGET))
	# archivos con codificaciones differentest
	# desde: https://github.com/stain/encoding-test-files
	-$(call HACE_PRUEBA, , -lwm, , pruebas/encoding-test-files/*.txt)
	# stdin
	-$(call HACE_PRUEBA, cat pruebas/*.txt |, -lwm, -lwc)
	-$(call HACE_PRUEBA, cat pruebas/*.txt |, -lwm, )
	# newlines
	-$(call HACE_PRUEBA, cat pruebas/newlines.txt |, -lwm, -lwc)
	@# Estoy poniendo esto aqui para estar cerca las otras pruebas
	@# Estos están pruebas que no puedo automizar
	# TODO manualmente
	# Archivos infinitos
	# ./tp0 /dev/zero
	# stdin desde usario
	# ./tp0

clean:
	-rm -f *.o
	-rm -f *.s
	-rm -f $(TARGET)
	-rm -f wc_out tp0_out

.PHONY: default all asm prueba clean
