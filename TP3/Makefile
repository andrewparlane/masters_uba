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
PKG_SRC_DIR		= $(SRC_DIR)/pkg
TB_SRC_DIR		= $(SRC_DIR)/tb
COMMON_DIR		= ../common
QUARTUS_DIR		= C:\\altera/13.0sp1/quartus

TEST_DIR		= test_files
MULT_TEST_DIR	= $(TEST_DIR)/multiplicacion
FP_GEN_PATH		= c/test_file_gen

# Common Lib name
# Add the following to your .vhd files that need
# to use something from the common/ directory
# 	library common;
#	use common.all;
COMMON_LIB		= common

# src files
SRCS	= $(wildcard $(PKG_SRC_DIR)/*.vhd) \
		  $(wildcard $(SRC_DIR)/*.vhd)
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

test_file_gen:
	@make -C $(FP_GEN_PATH)

# default rule is to create the library, and compile all the components
all: common srcs tb_srcs

.PHONY: common test_file_gen all

fp_decode: all
	@$(call VSIM_CMD, fp_decode_tb)

.PHONY: fp_decode

# A macro to run FP multiplication tests
#	Takes three arguments:
#		1) TOTAL_BITS
#		2) EXPONENT_BITS
#		3) test/file/path.txt
#		4) ROUNDING_MODE
#		5) NO_ASSERT_ON_ZERO_NEG_ZERO
define FP_MULT_TEST
	@$(call VSIM_CMD, fp_mult_tb, -gTOTAL_BITS=$(1) -gEXPONENT_BITS=$(2) -gTEST_FILE=$(3) -gROUNDING_MODE=$(4) -gNO_ASSERT_ON_ZERO_NEG_ZERO=$(5))
endef

FP_MULT_TP_TESTS = fp_mult_23_6 \
                   fp_mult_24_6 \
                   fp_mult_25_7 \
                   fp_mult_26_7 \
                   fp_mult_30_8 \
                   fp_mult_32_8

fp_mult_23_6: all
	# 23 bits total, 6 exponent
	@$(call FP_MULT_TEST,23,6,$(MULT_TEST_DIR)/test_mul_float_23_6.txt,RoundingMode_0,true)

fp_mult_24_6: all
	# 24 bits total, 6 exponent
	@$(call FP_MULT_TEST,24,6,$(MULT_TEST_DIR)/test_mul_float_24_6.txt,RoundingMode_0,true)

fp_mult_25_7: all
	# 25 bits total, 7 exponent
	@$(call FP_MULT_TEST,25,7,$(MULT_TEST_DIR)/test_mul_float_25_7.txt,RoundingMode_0,true)

fp_mult_26_7: all
	# 26 bits total, 7 exponent
	@$(call FP_MULT_TEST,26,7,$(MULT_TEST_DIR)/test_mul_float_26_7.txt,RoundingMode_0,true)

fp_mult_30_8: all
	# 30 bits total, 8 exponent
	@$(call FP_MULT_TEST,30,8,$(MULT_TEST_DIR)/test_mul_float_30_8.txt,RoundingMode_0,true)

fp_mult_32_8: all
	# 32 bits total, 8 exponent
	@$(call FP_MULT_TEST,32,8,$(MULT_TEST_DIR)/test_mul_float_32_8.txt,RoundingMode_0,true)

fp_mult_tp_all: $(FP_MULT_TP_TESTS)

FP_MULT_C_TESTS = fp_mult_c_round_zero \
				  fp_mult_c_round_down \
				  fp_mult_c_round_up \
				  fp_mult_c_round_nearest

fp_mult_c_round_zero: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen --no_denormal -r 0 -n 100000 -o $(FP_GEN_PATH)/out.txt
	@$(call FP_MULT_TEST,32,8,$(FP_GEN_PATH)/out.txt,RoundingMode_0,false)

fp_mult_c_round_down: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen --no_denormal -r 1 -n 100000 -o $(FP_GEN_PATH)/out.txt
	@$(call FP_MULT_TEST,32,8,$(FP_GEN_PATH)/out.txt,RoundingMode_NEG_INF,false)

fp_mult_c_round_up: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen --no_denormal -r 2 -n 100000 -o $(FP_GEN_PATH)/out.txt
	@$(call FP_MULT_TEST,32,8,$(FP_GEN_PATH)/out.txt,RoundingMode_POS_INF,false)

fp_mult_c_round_nearest: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen --no_denormal -r 3 -n 100000 -o $(FP_GEN_PATH)/out.txt
	@$(call FP_MULT_TEST,32,8,$(FP_GEN_PATH)/out.txt,RoundingMode_NEAREST,false)

fp_mult_c_all: $(FP_MULT_C_TESTS)

.PHONY: $(FP_MULT_TESTS) fp_mult_tp_all $(FP_MULT_C_TESTS) fp_mult_c_all

# delete the library and all compiled files
clean: helper_clean
	$(call DEL_VLIB_CMD, $(COMMON_LIB))

distclean: clean
	make -C $(COMMON_DIR) clean

.PHONY: clean distclean
