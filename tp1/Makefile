C_TARGET = tp1_c
ASM_TARGET = tp1_asm

MACHINE = $(shell uname -m)

LIBS =
CC = gcc
C_FLAGS = -Wall
ASM_FLAGS = -Wall

default: $(C_TARGET)
all: default

C_OBJECTS = main.c.o \
		    transpose.c.o

ASM_OBJECTS = main.c.o \
			  transpose.S.o

HEADERS = $(wildcard *.h)

%.c.o: %.c $(HEADERS)
	$(CC) $(C_FLAGS) -c $< -o $@

%.S.o: %.S $(HEADERS)
	$(CC) $(ASM_FLAGS) -c $< -o $@

$(C_TARGET): $(C_OBJECTS)
	$(CC) $(C_OBJECTS) $(C_FLAGS) $(LIBS) -o $@

$(ASM_TARGET): $(ASM_OBJECTS)
	$(CC) $(ASM_OBJECTS) $(ASM_FLAGS) $(LIBS) -o $@

C: $(C_TARGET)

ASM: $(ASM_TARGET)

c: C

asm: ASM

clean:
	-rm -f *.o
	-rm -f $(C_TARGET)
	-rm -f $(ASM_TARGET)

.PHONY: default all C c ASM asm clean
