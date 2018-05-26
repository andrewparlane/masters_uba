# ----------------------------------------------------------------------------------
# Requirements:
#	QuestaSim - We use vcom and vsim.
#	Each test bench must contain an instantiation called dut.
#	Each test bench must call std.env.stop when it's finished testing.
# ----------------------------------------------------------------------------------

ifndef WLF
# set the default target to be all. Otherwise it's the first target it finds
.DEFAULT_GOAL := all
else
.DEFAULT_GOAL := view
endif

# Directories
SIM_DIR			= sim
WAVES_DIR		= $(SIM_DIR)/waves
SRC_DIR			= src
#/cygdrive/c/altera/13.0sp1/quartus/eda/sim_lib
TB_SRC_DIR		= $(SRC_DIR)/tb
COMMON_DIR		= ../common
QUARTUS_DIR		= C:\\altera/13.0sp1/quartus

# Common Lib name
# Add the following to your .vhd files that need
# to use something from the common/ directory
# 	library common;
#	use common.all;
COMMON_LIB		= common

# src files
SRCS	= $(wildcard $(SRC_DIR)/*.vhd)
# tb files
TB_SRCS	= $(wildcard $(TB_SRC_DIR)/*.vhd) \
		  $(wildcard $(TB_SRC_DIR)/*.sv)

# Extra arguments beyond the defaults in helper.mk
VCOM_FLAGS		=
VSIM_FLAGS		=

# Now include our helper.mk which has all the rules we need
# to create our library, compile and simulate our test benches
include ../herramientas/helper.mk

common:
	@# Build all the sources, but not the testbenches
	@make -C $(COMMON_DIR) srcs
	@# Add the common lib to our modelsim.ini
	@$(call MAP_VLIB_CMD, $(COMMON_DIR), $(COMMON_LIB))

# default rule is to create the library, and compile all the components
all: common srcs tb_srcs

.PHONY: common all

fp_decode: all
	@$(call VSIM_CMD, fp_decode_tb)

# delete the library and all compiled files
clean: helper_clean
	$(call DEL_VLIB_CMD, $(COMMON_LIB))

distclean: clean
	make -C $(COMMON_DIR) clean

.PHONY: clean distclean
