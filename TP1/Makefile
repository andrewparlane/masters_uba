# ----------------------------------------------------------------------------------
# Requirements:
#	QuestaSim - We use vcom and vsim.
#	Each test bench must contain an instantiation called dut.
#	Each test bench must call std.env.stop when it's finished testing.
# ----------------------------------------------------------------------------------

# set the default target to be all. Otherwise it's the first target it finds
.DEFAULT_GOAL := all

# Which library do we want to put our work in
VLIB_NAME		= work

# Directories
SIM_DIR			= sim
SRC_DIR			= src

# src files
SRCS	= $(wildcard $(SRC_DIR)/*.vhd)

# Extra arguments beyond the defaults in helper.mk
VCOM_FLAGS		=
VSIM_FLAGS		=

# Now include our helper.mk which has all the rules we need
# to create our library, compile and simulate our test benches
include ../herramientas/helper.mk

# default rule is to create the library, and compile all the components
all: srcs

contador: srcs
	@$(call VSIM_CMD, contador_tb)

tp1: srcs
	@$(call VSIM_CMD, tp1_tb)

# delete the library and all compiled files
clean: helper_clean

.PHONY: clean all contador tp1
