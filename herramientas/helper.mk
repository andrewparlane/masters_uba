# Some common macros and variables for use with compiling VHDL
# using vcom which is packaged as part of QuestaSim
#-----------------------------------------------------------------------------------

# we use the bash shell, so we can use process substitution
SHELL			:= /bin/bash

# Most questasim tools require the path to the modelsim.ini file
# We have ours in the $(SIM_DIR)
MODELSIM_FLAG 	= -modelsimini $(SIM_DIR)/modelsim.ini

# ----------------------------------------------------------------------------------
# colourization
# ----------------------------------------------------------------------------------
# this consists of the following colour definitions
# and three macros used to parse the stderr and stdout of commands
# ----------------------------------------------------------------------------------

# colours
COLOUR_NONE		= \x1b[0m
COLOUR_RED		= \x1b[31;01m
COLOUR_BLUE		= \x1b[34;01m
COLOUR_GREEN 	= \x1b[32;01m
COLOUR_ORANGE	= \x1b[33;01m

# Macro to generate SED command to colourize output:
#	Takes two arguments:
#		1) pattern to match
#		2) colour to highlight (only highlights the matched pattern, not the whole line)
GENERATE_COLOURIZE_SED = -e $$'s/$(1)/$(2)\\1$(COLOUR_NONE)/'

# SED command to do all colour substitutions
# 	This is just a list of sed expressions generated using the GENERATE_COLOURIZE_SED macro
# 	It adds the $(MORE_COLOURS) var at the end, which can be used in individual makefiles
# 	to add more colourization. IE. if you want to colourize lines with Importing in them
# 	Additionally you can override COLOURIZE_SED_ALL to replace all colourization options
COLOURIZE_SED_ALL ?= sed -r $(call GENERATE_COLOURIZE_SED,(Error:|UVM_ERROR|UVM_FATAL|Fatal:|FATAL ERROR|Error|Failure|FALLA!),$(COLOUR_RED)) \
							$(call GENERATE_COLOURIZE_SED,(Warning:|Note:|UVM_WARNING),$(COLOUR_ORANGE)) \
							$(call GENERATE_COLOURIZE_SED,(UVM_INFO),$(COLOUR_BLUE)) \
							$(call GENERATE_COLOURIZE_SED,(APROBAR!),$(COLOUR_GREEN)) \
							$(MORE_COLOURS)

# Actual macro that colourizes
#	Takes one argument:
#		1) The command to run.
#	We run in () so that the set -o pipefail doesn't persist past this call
#	set -o pipefail makes sure our exit code is correct (ie. if vcom returns error 1, we want the entire command to return error 1)
#	We pass stderr into the above COLOURIZE_SED_ALL sed command, and then redirect it back to stderr
#	Finally we pipe it in to the COLOURIZE_SED_ALL again, which makes it also run on stdout
COLOURIZE = (set -o pipefail; $(1) 2> >($(COLOURIZE_SED_ALL) >&2) | $(COLOURIZE_SED_ALL))

# ----------------------------------------------------------------------------------
# Library
# ----------------------------------------------------------------------------------
# create the questaSim library if it's not already there
# ----------------------------------------------------------------------------------

VLIB_DIR 	= $(SIM_DIR)/$(VLIB_NAME)

$(VLIB_DIR):
	vlib $(VLIB_DIR)
	vmap $(MODELSIM_FLAG) $(VLIB_NAME) $(VLIB_DIR)
	@echo -e "$(COLOUR_GREEN)Created the $(VLIB_DIR) library mapped to $(VLIB_NAME)$(COLOUR_NONE)\n"

# ----------------------------------------------------------------------------------
# Compilation
# ----------------------------------------------------------------------------------
# When we compile a file using vcom, we create a flag file
# which can be used as a dependency for each .vhd file.
# As make can compare the timestamps of the source file and the
# flag file. In older versions of questaSim vcom created a
# unique file per package/interface/module automaticaly
# however in the later versions it does not.
# ----------------------------------------------------------------------------------

# directory where we store the flags
FLAGS_DIR	= $(VLIB_DIR)/flags

# List of flags from list of sources
FLAGS 		= $(patsubst $(SRC_DIR)/%.vhd, $(FLAGS_DIR)/%.flag, $(SRCS))
TB_FLAGS 	= $(patsubst $(TB_SRC_DIR)/%.vhd, $(FLAGS_DIR)/%.flag, $(TB_SRCS))

VCOM_FLAGS 			:= $(MODELSIM_FLAG) \
					   -work $(VLIB_NAME)

# Flags to use with modules we will synthesise (IE not testbenches)
NON_TB_VCOM_FLAGS	:= -check_synthesis

$(FLAGS): $(FLAGS_DIR)/%.flag : $(SRC_DIR)/%.vhd
	@echo -e "$(COLOUR_BLUE)compiling $< because of changes in: $? $(COLOUR_NONE)\n"
	@$(call COLOURIZE ,vcom $(VCOM_FLAGS) $(NON_TB_VCOM_FLAGS) $<)
	@mkdir -p $(FLAGS_DIR)
	@touch $@

$(TB_FLAGS): $(FLAGS_DIR)/%.flag : $(TB_SRC_DIR)/%.vhd
	@echo -e "$(COLOUR_BLUE)compiling $< because of changes in: $? $(COLOUR_NONE)\n"
	@$(call COLOURIZE ,vcom $(VCOM_FLAGS) $<)
	@mkdir -p $(FLAGS_DIR)
	@touch $@

srcs: $(VLIB_DIR) $(FLAGS)
	@echo -e "$(COLOUR_GREEN)Compiled all sources.$(COLOUR_NONE)\n"

# ----------------------------------------------------------------------------------
# Simulation
# ----------------------------------------------------------------------------------
#
# ----------------------------------------------------------------------------------

# VSIM args to log waves
# Use DEBUG=1 to log all waves
# otherwise it just logs the waves in the top level module
ifeq ($(DEBUG),1)
ADD_DEBUG_WAVES				=	add wave -r /*
else
ADD_DEBUG_WAVES				=	add wave dut/*
endif

# commands to run once vsim starts
# run for max of 5s
VSIM_DO_CMDS				=	log -r /*; \
								$(ADD_DEBUG_WAVES); \
								run 5 sec; \
								assertion report -recursive *; \
								quit -f

# flags to pass to VSIM_CMD
VSIM_FLAGS					:=	$(MODELSIM_FLAG) \
								-sv_seed random

# the run the test command.
#	Takes one arguments:
#		1) Top level module name
define VSIM_CMD
	@echo -e "$(COLOUR_GREEN)Running simulation of $(1).$(COLOUR_NONE)\n"
	$(call COLOURIZE, \
		vsim $(VSIM_FLAGS) \
			 -wlf $(1).wlf \
			 -do "$(VSIM_DO_CMDS)" \
			 $(1))
endef

# A generic rule to open questasim and show us the saved waves
view:
	@if [ -z $(WLF)"" ]; then \
		echo -e "$(COLOUR_RED)usage: make WLF=abc.wlf view$(COLOUR_NONE)\n"; \
	elif [ ! -e $(WLF) ]; then \
		echo -e "$(COLOUR_RED)$(WLF) does not exist. $(COLOUR_NONE)\n"; \
	else \
		questasim $(MODELSIM_FLAG) -do "vsim -view $(WLF); $(ADD_DEBUG_WAVES)"; \
	fi

# ----------------------------------------------------------------------------------
# Cleaning
# ----------------------------------------------------------------------------------

helper_clean:
	-rm -rf $(VLIB_DIR)

# ----------------------------------------------------------------------------------
# PHONY
# ----------------------------------------------------------------------------------

.PHONY: helper_clean srcs view_saved_waves
