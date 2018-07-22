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
		  $(wildcard $(SRC_DIR)/*.vhd) \
		  $(wildcard $(SRC_DIR)/vga/*.vhd)

# tb files
TB_SRCS	= $(wildcard $(TB_SRC_DIR)/*.vhd) \
		  $(wildcard $(TB_SRC_DIR)/*.sv) \
		  $(wildcard $(TB_SRC_DIR)/vga/*.vhd) \
		  $(wildcard $(TB_SRC_DIR)/vga/*.sv)

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

.PHONY: contador view_contador

vga: all
	@$(call VSIM_CMD, vga_tb)

view_vga:
	@$(call VSIM_VIEW_WAVES_TLM, vga_tb, $(VSIM_DUT_WAVES))

.PHONY: vga view_vga

adv7123: all
	@$(call VSIM_CMD, adv7123_tb)

view_adv7123:
	@$(call VSIM_VIEW_WAVES_TLM, adv7123_tb, $(VSIM_DUT_WAVES))

adv7123_2: all
	@$(call VSIM_CMD, adv7123_tb2)

view_adv7123_2:
	@$(call VSIM_VIEW_WAVES_TLM, adv7123_tb2, $(VSIM_DUT_WAVES))

.PHONY: adv7123 adv7123_2 view_adv7123 view_adv7123_2

# delete the library and all compiled files
clean: helper_clean

distclean: clean

.PHONY: clean distclean all
