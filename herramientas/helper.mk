# Some common macros and variables for use with compiling VHDL
# using vcom which is packaged as part of QuestaSim
#-----------------------------------------------------------------------------------

# we use the bash shell, so we can use process substitution
SHELL			:= /bin/bash

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
# end colourization
# ----------------------------------------------------------------------------------

# When we compile a file using vcom, we create a flag file
# which can be used as a dependency for each .vhd file.
# As make can compare the timestamps of the source file and the
# flag file. In older versions of questaSim vcom created a
# unique file per package/interface/module automaticaly
# however in the later versions it does not.

# directory where we store the flags
FLAGS_DIR	= $(VLIB_DIR)/flags/

# Macro to turn source file path into the flag file path
#	Takes one argument:
#		1) source file path
src2obj		= $(addsuffix .flag, $(addprefix $(FLAGS_DIR), $(basename $(notdir $(1)))))

# macro to create a target for a given source file
# it takes two arguments:
# 1) the path and name of the source file
# 2) any dependencies
# It then creates a traget on the relevant flag file
# with a dependency on the source file, and any other passed in dependencies
# If compilation is successfull we create the flag file
define create_target_for

$$(info create_target_for called on $(1))
$$(info creating target $(call src2obj, $(1)))
$$(info with dependencies $(VLIB_DIR) $(1) $(2))
$$(info )
$(call src2obj, $(1)): $(1) $(2)
	@echo -e "$(COLOUR_BLUE)compiling $(1) because of changes in: $$? $(COLOUR_NONE)\n"
	@# double dollar here, so the call gets executed at run time, not at eval time
	@$$(call COLOURIZE ,vcom $(VCOM_FLAGS) $(1))
	@# if the compile was successfull touch our flag file
	@mkdir -p $(FLAGS_DIR)
	@touch $(call src2obj, $(1))

endef
