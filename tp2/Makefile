TARGET = tp2

LIBS =
CC = gcc
CFLAGS = -Wall -g

default: $(TARGET)
all: default

OBJECTS = main.o

%.o: %.c
	$(CC) $(C_FLAGS) -c $< -o $@

$(TARGET): $(OBJECTS)
	$(CC) $(OBJECTS) $(CFLAGS) $(LIBS) -o $@

clean:
	-rm -f *.o
	-rm -f $(CTARGET)

.PHONY: default all clean
