import fp_type_pkg::*;

program fp_round_coverage_prog
        #(parameter TBITS,
          parameter EBITS,
          parameter SBITS)
         (input logic                       i_clk,
          input logic [SBITS-1:0]           i_sig,
          input logic [EBITS+1:0]           i_bExp,
          input logic                       i_sign,
          input logic                       i_r,
          input logic                       i_s,
          input fp_type_pkg::roundingmode   i_rm,
          input logic [SBITS-1:0]           o_sig,
          input logic [EBITS-1:0]           o_bExp,
          input fp_type_pkg::fpnumtype      o_type);

    covergroup cg_input @(posedge i_clk);
        option.per_instance = 1;
        option.at_least = 100;
        option.goal = 100;

        cp_rm: coverpoint i_rm
        {
            bins neg_inf = {roundingmode_neg_inf};
            bins pos_inf = {roundingmode_pos_inf};
            bins zero    = {roundingmode_0};
            bins nearest = {roundingmode_nearest};
        }
        cp_r: coverpoint i_r
        {
            bins zero = {0};
            bins one  = {1};
        }
        cp_s: coverpoint i_s
        {
            bins zero = {0};
            bins one  = {1};
        }
        cp_sign: coverpoint i_sign
        {
            bins pos = {0};
            bins neg = {1};
        }
        cp_sig: coverpoint i_sig
        {
            bins min = {0};
            // commented out because it's impossible to get max
            // with multiplication
            //bins max = {{SBITS{1'b1}}};
            bins others[100] = default;
        }
        cp_bexp: coverpoint i_bExp
        {
            bins min            = {0};
            bins emin           = {1};
            bins emax           = {{EBITS{1'b1}}-1};
            bins max            = {{EBITS{1'b1}}};
            bins overflow       = {[{EBITS{1'b1}}+1 : {(EBITS+1){1'b1}}]};
            bins underflow      = {[{{EBITS+1}{1'b1}}+1 : {(EBITS+2){1'b1}}]};
            bins others[10]     = default;
        }
        cp_cross: cross cp_rm, cp_r, cp_s, cp_sign, cp_sig, cp_bexp;
    endgroup

    covergroup cg_output @(posedge i_clk);
        option.per_instance = 1;
        option.at_least = 100;
        option.goal = 100;

        cp_sig: coverpoint o_sig
        {
            bins min = {0};
            bins max = {{SBITS{1'b1}}};
            bins others[10] = default;
        }
        cp_bexp: coverpoint o_bExp
        {
            bins min    = {0};
            bins emin   = {1};
            bins emax   = {{EBITS{1'b1}}-1};
            bins max    = {{EBITS{1'b1}}};
            bins others[10] = default;
        }
        cp_type: coverpoint o_type
        {
            bins zero       = {fpnumtype_zero};
            bins inf        = {fpnumtype_infinity};
            bins denormal   = {fpnumtype_denormal};
            bins normal     = {fpnumtype_normal};
            ignore_bins nan = {fpnumtype_nan};
        }
    endgroup

    cg_input  input_coverage  = new();
    cg_output output_coverage = new();

endprogram

program fp_add_mult_coverage_prog
        #(parameter TBITS,
          parameter EBITS)
         (input logic                       i_clk,
          input logic [TBITS-1:0]           i_a,
          input logic [TBITS-1:0]           i_b,
          input fp_type_pkg::roundingmode   i_rm,
          input logic [TBITS-1:0]           o_res);

    // note SBITS here is the amount of bits in the packed
    // significand, not the amount of bits in the actual one.
    localparam SBITS = TBITS - EBITS - 1;

    localparam DENORMAL_RANGE_START = {{EBITS{1'b0}}, {(SBITS-1){1'b0}}, 1'b1};
    localparam DENORMAL_RANGE_END   = {{EBITS{1'b0}}, {(SBITS){1'b1}}};

    localparam INF = {{EBITS{1'b1}}, {(SBITS){1'b0}}};

    localparam NAN_RANGE_START = {{EBITS{1'b1}}, {(SBITS-1){1'b0}}, 1'b1};
    localparam NAN_RANGE_END   = {{EBITS{1'b1}}, {(SBITS){1'b1}}};

    covergroup cg_input @(posedge i_clk);
        option.per_instance = 1;
        option.at_least = 100;
        option.goal = 100;

        cp_rm: coverpoint i_rm
        {
            bins neg_inf = {roundingmode_neg_inf};
            bins pos_inf = {roundingmode_pos_inf};
            bins zero    = {roundingmode_0};
            bins nearest = {roundingmode_nearest};
        }

        cp_sign_a: coverpoint i_a[TBITS-1]
        {
            bins pos = {0};
            bins neg = {1};
        }

        cp_sign_b: coverpoint i_b[TBITS-1]
        {
            bins pos = {0};
            bins neg = {1};
        }

        cp_rest_a: coverpoint i_a[TBITS-2 : 0]
        {
            bins zero           = {0};
            bins denormal[10]   = {[DENORMAL_RANGE_START : DENORMAL_RANGE_END]};
            bins inf            = {INF};
            bins NaN            = {[NAN_RANGE_START : NAN_RANGE_END]};
            bins normal[10]     = default;
        }

        cp_rest_b: coverpoint i_b[TBITS-2 : 0]
        {
            bins zero           = {0};
            bins denormal[10]   = {[DENORMAL_RANGE_START : DENORMAL_RANGE_END]};
            bins inf            = {INF};
            bins NaN            = {[NAN_RANGE_START : NAN_RANGE_END]};
            bins normal[10]     = default;
        }

        cp_a: cross cp_sign_a, cp_rest_a;
        cp_b: cross cp_sign_b, cp_rest_b;
        cp_inputs: cross cp_a, cp_b, cp_rm;
    endgroup

    covergroup cg_output @(posedge i_clk);
        option.per_instance = 1;
        option.at_least = 100;
        option.goal = 100;

        cp_rm: coverpoint i_rm
        {
            bins neg_inf = {roundingmode_neg_inf};
            bins pos_inf = {roundingmode_pos_inf};
            bins zero    = {roundingmode_0};
            bins nearest = {roundingmode_nearest};
        }

        cp_sign: coverpoint o_res[TBITS-1]
        {
            bins pos = {0};
            bins neg = {1};
        }

        cp_rest: coverpoint o_res[TBITS-2 : 0]
        {
            bins zero           = {0};
            bins denormal[10]   = {[DENORMAL_RANGE_START : DENORMAL_RANGE_END]};
            bins inf            = {INF};
            bins NaN            = {[NAN_RANGE_START : NAN_RANGE_END]};
            bins normal[10]     = default;
        }

        cp_output: cross cp_sign, cp_rest, cp_rm;
    endgroup

    cg_input  input_coverage  = new();
    cg_output output_coverage = new();

endprogram

module fp_mult_wrapper;
    bind fp_mult
         fp_add_mult_coverage_prog #(.TBITS(TBITS),
                                     .EBITS(EBITS))
         fp_mult_bind (.*);

    bind fp_round
         fp_round_coverage_prog #(.TBITS(TBITS),
                                  .EBITS(EBITS),
                                  .SBITS(SBITS))
         fp_round_bind (.*);
endmodule

module fp_add_wrapper;
    bind fp_add
         fp_add_mult_coverage_prog #(.TBITS(TBITS),
                                     .EBITS(EBITS))
         fp_add_bind (.*);

    bind fp_round
         fp_round_coverage_prog #(.TBITS(TBITS),
                                  .EBITS(EBITS),
                                  .SBITS(SBITS))
         fp_round_bind (.*);
endmodule
