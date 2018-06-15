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
SUM_TEST_DIR	= $(TEST_DIR)/suma
SUB_TEST_DIR	= $(TEST_DIR)/resta
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

# Coverage files
MULT_COVERAGE_FILE_32B	= $(SIM_DIR)/mult_coverage_32b.ucdb
MULT_COVERAGE_FILE_64B	= $(SIM_DIR)/mult_coverage_64b.ucdb
ADD_COVERAGE_FILE_32B	= $(SIM_DIR)/add_coverage_32b.ucdb
ADD_COVERAGE_FILE_64B	= $(SIM_DIR)/add_coverage_64b.ucdb

ifndef NUM_C_TESTS
NUM_C_TESTS		= 100000
endif

ifdef DOUBLE
C_DOUBLE_FLAG		= --double_precision
NUM_C_TOTAL_BITS	= 64
NUM_C_EXP_BITS		= 11
MULT_COVERAGE_FILE  = $(MULT_COVERAGE_FILE_64B)
ADD_COVERAGE_FILE   = $(ADD_COVERAGE_FILE_64B)
else
C_DOUBLE_FLAG		=
NUM_C_TOTAL_BITS	= 32
NUM_C_EXP_BITS		= 8
MULT_COVERAGE_FILE  = $(MULT_COVERAGE_FILE_32B)
ADD_COVERAGE_FILE   = $(ADD_COVERAGE_FILE_32B)
endif


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
#	Takes six arguments:
#		1) TOTAL_BITS
#		2) EXPONENT_BITS
#		3) test/file/path.txt
#		4) ROUNDING_MODE
#		5) NO_ASSERT_ON_ZERO_NEG_ZERO
#		6) DENORMALS
define FP_MULT_TEST
	@$(call VSIM_CMD, fp_mult_tb, -gTOTAL_BITS=$(1) -gEXPONENT_BITS=$(2) -gTEST_FILE=$(3) -gROUNDING_MODE=$(4) -gNO_ASSERT_ON_ZERO_NEG_ZERO=$(5) -gDENORMALS=$(6), $(MULT_COVERAGE_FILE))
endef

# A macro to run FP addition tests
#	Takes six arguments:
#		1) TOTAL_BITS
#		2) EXPONENT_BITS
#		3) test/file/path.txt
#		4) ROUNDING_MODE
#		5) NO_ASSERT_ON_ZERO_NEG_ZERO
#		6) DENORMALS
define FP_SUM_TEST
	@$(call VSIM_CMD, fp_add_tb, -gTOTAL_BITS=$(1) -gEXPONENT_BITS=$(2) -gTEST_FILE=$(3) -gROUNDING_MODE=$(4) -gNO_ASSERT_ON_ZERO_NEG_ZERO=$(5) -gSUBTRACT=false -gDENORMALS=$(6), $(ADD_COVERAGE_FILE))
endef

# A macro to run FP subtraction tests
#	Takes six arguments:
#		1) TOTAL_BITS
#		2) EXPONENT_BITS
#		3) test/file/path.txt
#		4) ROUNDING_MODE
#		5) NO_ASSERT_ON_ZERO_NEG_ZERO
#		6) DENORMALS
define FP_SUB_TEST
	@$(call VSIM_CMD, fp_add_tb, -gTOTAL_BITS=$(1) -gEXPONENT_BITS=$(2) -gTEST_FILE=$(3) -gROUNDING_MODE=$(4) -gNO_ASSERT_ON_ZERO_NEG_ZERO=$(5) -gSUBTRACT=true -gDENORMALS=$(6), $(ADD_COVERAGE_FILE))
endef

FP_MULT_TP_TESTS = fp_mult_23_6 \
                   fp_mult_24_6 \
                   fp_mult_25_7 \
                   fp_mult_26_7 \
                   fp_mult_30_8 \
                   fp_mult_32_8

fp_mult_23_6: all
	# 23 bits total, 6 exponent
	@$(call FP_MULT_TEST,23,6,$(MULT_TEST_DIR)/test_mul_float_23_6.txt,RoundingMode_0,true,false)

fp_mult_24_6: all
	# 24 bits total, 6 exponent
	@$(call FP_MULT_TEST,24,6,$(MULT_TEST_DIR)/test_mul_float_24_6.txt,RoundingMode_0,true,false)

fp_mult_25_7: all
	# 25 bits total, 7 exponent
	@$(call FP_MULT_TEST,25,7,$(MULT_TEST_DIR)/test_mul_float_25_7.txt,RoundingMode_0,true,false)

fp_mult_26_7: all
	# 26 bits total, 7 exponent
	@$(call FP_MULT_TEST,26,7,$(MULT_TEST_DIR)/test_mul_float_26_7.txt,RoundingMode_0,true,false)

fp_mult_30_8: all
	# 30 bits total, 8 exponent
	@$(call FP_MULT_TEST,30,8,$(MULT_TEST_DIR)/test_mul_float_30_8.txt,RoundingMode_0,true,false)

fp_mult_32_8: all
	# 32 bits total, 8 exponent
	@$(call FP_MULT_TEST,32,8,$(MULT_TEST_DIR)/test_mul_float_32_8.txt,RoundingMode_0,true,false)

fp_mult_tp_all: $(FP_MULT_TP_TESTS)

FP_MULT_C_TESTS = fp_mult_c_round_zero \
				  fp_mult_c_round_down \
				  fp_mult_c_round_up \
				  fp_mult_c_round_nearest

fp_mult_c_round_zero: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -m -r 0 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_MULT_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_0,false,true)

fp_mult_c_round_down: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -m -r 1 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_MULT_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_NEG_INF,false,true)

fp_mult_c_round_up: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -m -r 2 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_MULT_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_POS_INF,false,true)

fp_mult_c_round_nearest: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -m -r 3 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_MULT_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_NEAREST,false,true)

fp_mult_c_all: $(FP_MULT_C_TESTS)

.PHONY: $(FP_MULT_TESTS) fp_mult_tp_all $(FP_MULT_C_TESTS) fp_mult_c_all

fp_mult_c_32b_report:
	@$(call COVERAGE_REPORT, $(MULT_COVERAGE_FILE_32B))

fp_mult_c_64b_report:
	@$(call COVERAGE_REPORT, $(MULT_COVERAGE_FILE_64B))

fp_add_c_32b_report:
	@$(call COVERAGE_REPORT, $(ADD_COVERAGE_FILE_32B))

fp_add_c_64b_report:
	@$(call COVERAGE_REPORT, $(ADD_COVERAGE_FILE_64B))

.PHONY: fp_mult_c_32b_report fp_mult_c_64b_report fp_add_c_32b_report fp_add_c_64b_report

FP_SUM_TP_TESTS = fp_sum_23_6 \
                  fp_sum_24_6 \
                  fp_sum_25_7 \
                  fp_sum_26_7 \
                  fp_sum_30_8 \
                  fp_sum_32_8

fp_sum_23_6: all
	# 23 bits total, 6 exponent
	@$(call FP_SUM_TEST,23,6,$(SUM_TEST_DIR)/test_sum_float_23_6.txt,RoundingMode_0,true,false)

fp_sum_24_6: all
	# 24 bits total, 6 exponent
	@$(call FP_SUM_TEST,24,6,$(SUM_TEST_DIR)/test_sum_float_24_6.txt,RoundingMode_0,true,false)

fp_sum_25_7: all
	# 25 bits total, 7 exponent
	@$(call FP_SUM_TEST,25,7,$(SUM_TEST_DIR)/test_sum_float_25_7.txt,RoundingMode_0,true,false)

fp_sum_26_7: all
	# 26 bits total, 7 exponent
	@$(call FP_SUM_TEST,26,7,$(SUM_TEST_DIR)/test_sum_float_26_7.txt,RoundingMode_0,true,false)

fp_sum_30_8: all
	# 30 bits total, 8 exponent
	@$(call FP_SUM_TEST,30,8,$(SUM_TEST_DIR)/test_sum_float_30_8.txt,RoundingMode_0,true,false)

fp_sum_32_8: all
	# 32 bits total, 8 exponent
	@$(call FP_SUM_TEST,32,8,$(SUM_TEST_DIR)/test_sum_float_32_8.txt,RoundingMode_0,true,false)

fp_sum_tp_all: $(FP_SUM_TP_TESTS)

FP_SUM_C_TESTS = fp_sum_c_round_zero \
				  fp_sum_c_round_down \
				  fp_sum_c_round_up \
				  fp_sum_c_round_nearest

fp_sum_c_round_zero: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -a -r 0 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_SUM_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_0,false,true)

fp_sum_c_round_down: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -a -r 1 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_SUM_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_NEG_INF,false,true)

fp_sum_c_round_up: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -a -r 2 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_SUM_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_POS_INF,false,true)

fp_sum_c_round_nearest: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -a -r 3 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_SUM_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_NEAREST,false,true)

fp_sum_c_all: $(FP_SUM_C_TESTS)

.PHONY: $(FP_SUM_TESTS) fp_sum_tp_all $(FP_SUM_C_TESTS) fp_sum_c_all

FP_SUB_TP_TESTS = fp_sub_23_6 \
                  fp_sub_24_6 \
                  fp_sub_25_7 \
                  fp_sub_26_7 \
                  fp_sub_30_8 \
                  fp_sub_32_8

fp_sub_23_6: all
	# 23 bits total, 6 exponent
	@$(call FP_SUB_TEST,23,6,$(SUB_TEST_DIR)/test_dif_float_23_6.txt,RoundingMode_0,true,false)

fp_sub_24_6: all
	# 24 bits total, 6 exponent
	@$(call FP_SUB_TEST,24,6,$(SUB_TEST_DIR)/test_dif_float_24_6.txt,RoundingMode_0,true,false)

fp_sub_25_7: all
	# 25 bits total, 7 exponent
	@$(call FP_SUB_TEST,25,7,$(SUB_TEST_DIR)/test_dif_float_25_7.txt,RoundingMode_0,true,false)

fp_sub_26_7: all
	# 26 bits total, 7 exponent
	@$(call FP_SUB_TEST,26,7,$(SUB_TEST_DIR)/test_dif_float_26_7.txt,RoundingMode_0,true,false)

fp_sub_30_8: all
	# 30 bits total, 8 exponent
	@$(call FP_SUB_TEST,30,8,$(SUB_TEST_DIR)/test_dif_float_30_8.txt,RoundingMode_0,true,false)

fp_sub_32_8: all
	# 32 bits total, 8 exponent
	@$(call FP_SUB_TEST,32,8,$(SUB_TEST_DIR)/test_dif_float_32_8.txt,RoundingMode_0,true,false)

fp_sub_tp_all: $(FP_SUB_TP_TESTS)

FP_SUB_C_TESTS = fp_sub_c_round_zero \
				  fp_sub_c_round_down \
				  fp_sub_c_round_up \
				  fp_sub_c_round_nearest

fp_sub_c_round_zero: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -s -r 0 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_SUB_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_0,false,true)

fp_sub_c_round_down: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -s -r 1 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_SUB_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_NEG_INF,false,true)

fp_sub_c_round_up: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -s -r 2 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_SUB_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_POS_INF,false,true)

fp_sub_c_round_nearest: all test_file_gen
	# 32 bits total, 8 exponent
	$(FP_GEN_PATH)/fpTestGen -s -r 3 $(C_DOUBLE_FLAG) -n $(NUM_C_TESTS) -o $(FP_GEN_PATH)/out.txt
	@$(call FP_SUB_TEST,$(NUM_C_TOTAL_BITS),$(NUM_C_EXP_BITS),$(FP_GEN_PATH)/out.txt,RoundingMode_NEAREST,false,true)

fp_sub_c_all: $(FP_SUB_C_TESTS)

.PHONY: $(FP_SUM_TESTS) fp_sub_tp_all $(FP_SUM_C_TESTS) fp_sub_c_all

all_tests: 	fp_sub_c_all fp_sum_c_all fp_mult_c_all \
			fp_sub_tp_all fp_sum_tp_all fp_mult_tp_all

all_c_tests: fp_sub_c_all fp_sum_c_all fp_mult_c_all

.PHONY: all_tests all_c_tests

# delete the library and all compiled files
clean: helper_clean
	$(call DEL_VLIB_CMD, $(COMMON_LIB))

distclean: clean
	make -C $(COMMON_DIR) clean

.PHONY: clean distclean
