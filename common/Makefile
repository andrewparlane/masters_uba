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
TB_SRC_DIR		= $(SRC_DIR)/tb

# src files
SRCS	= $(SRC_DIR)/type_pkg.vhd \
		  $(wildcard $(SRC_DIR)/*.vhd)
# tb files
TB_SRCS	= $(wildcard $(TB_SRC_DIR)/*.vhd)

# Extra arguments beyond the defaults in helper.mk
VCOM_FLAGS		=
VSIM_FLAGS		=

# Now include our helper.mk which has all the rules we need
# to create our library, compile and simulate our test benches
include ../herramientas/helper.mk

# default rule is to create the library, and compile all the components
all: srcs tb_srcs

contador: srcs tb_srcs
	@$(call VSIM_CMD, contador_tb)

view_contador:
	@$(call VSIM_VIEW_WAVES_TLM, contador_tb, $(VSIM_DUT_WAVES))

# delete the library and all compiled files
clean: helper_clean

distclean: clean

.PHONY: clean distclean all contador view_contador
