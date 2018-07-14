`timescale 1ns/1ns

module cordic_rotation_tb;

    logic               clk;
    logic               reset;
    logic               en;
    logic [31:0]        x;
    logic [31:0]        y;
    logic [31:0]        alpha;
    logic [31:0]        resX;
    logic [31:0]        resY;
    logic               resValid;

    // --------------------------------------------------------------
    // Generate the clock
    // --------------------------------------------------------------
    localparam CLOCK_FREQUENCY_MHZ = 100;
    localparam CLOCK_PERIOD_NS = 1000 / CLOCK_FREQUENCY_MHZ;

    initial begin
        clk <= 1'b0;
        forever begin
            #(CLOCK_PERIOD_NS/2);
            clk <= ~clk;
        end
    end

    // --------------------------------------------------------------
    // DUT
    // --------------------------------------------------------------
    cordic_rotation #(.N        (9),
                      .M        (23),
                      .STEPS    (10))
                 dut (.i_clk    (clk),
                      .i_reset  (reset),
                      .i_en     (en),
                      .i_x      (x),
                      .i_y      (y),
                      .i_alpha  (alpha),
                      .o_x      (resX),
                      .o_y      (resY),
                      .o_valid  (resValid));

    // --------------------------------------------------------------
    // Test stimulus
    // --------------------------------------------------------------

    initial begin
        // reset the dut
        reset <= 1;
        repeat (10) @(posedge clk);
        reset <= 0;

        x <= 1 << 23;
        y <= 1 << 23;
        alpha <= 90 << 23;
        en <= 1;
        @(posedge clk);
        en <= 0;
        repeat (10) @(posedge clk);
        $display("valid %b, x %d, y %d", resValid, resX, resY);

        $stop;
    end

    // --------------------------------------------------------------
    // Asserts
    // --------------------------------------------------------------

endmodule
